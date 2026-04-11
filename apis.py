# coding=utf-8
import json
import re
import base64
import time
import random
import string
import os
import socket
import threading
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from queue import Queue, Empty
from random import choice
from threading import RLock, Thread
from time import sleep, time as stime
from urllib.parse import (parse_qsl, unquote_plus, urlencode, urljoin,
                          urlsplit, urlunsplit, quote, parse_qs)

import json5
import urllib3
import requests
from bs4 import BeautifulSoup

# --- 核心增强：过墙级引擎 ---
try:
    from curl_cffi import requests as crequests 
except ImportError:
    crequests = requests

# --- 植入：OCR 验证码识别 ---
try:
    import ddddocr
    ocr = ddddocr.DdddOcr(show_ad=False)
    ocr_lock = threading.Lock() # 高并发 CPU 保护锁
except ImportError:
    ocr = None

# --- 原版工具函数导入 (请确保同目录下有 utils.py) ---
try:
    from utils import (cached, get, keep, parallel_map, rand_id, str2size,
                       str2timestamp)
except ImportError:
    # 兼容性兜底：如果没找到 utils，定义一个基础 cached 装饰器
    def cached(func):
        cache = {}
        def wrapper(*args, **kwargs):
            key = str(args) + str(kwargs)
            if key not in cache: cache[key] = func(*args, **kwargs)
            return cache[key]
        return wrapper
    # 其他工具函数在这里省略，建议保留原有的 utils.py

# 禁用 SSL 警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

REDIRECT_TO_GET = 1
REDIRECT_ORIGIN = 2
REDIRECT_PATH_QUERY = 4

# ==================== 原版核心正则库 (100% 完整保留) ====================
re_scheme = re.compile(r'^(?:([a-z]*):)?[\\/]*', re.I)
re_checked_in = re.compile(r'(?:已经?|重复)签到')
re_var_sub_token = re.compile(r'var sub_token = "(.+?)"')
re_email_code = re.compile(r'(?:码|碼|証|code|验证码).*?(?<![\da-z])([\da-z]{4,8})(?![\da-z])', re.I | re.S)

re_snapmail_domains = re.compile(r'emailDomainList.*?(\[.*?\])')
re_mailcx_js_path = re.compile(r'/_next/static/chunks/\d+-[\da-f]{16}.js')
re_mailcx_domains = re.compile(r'mailHosts:(\[.*?\])')
re_option_domain = re.compile(r'<option[^>]+value="@?((?:(?:[\da-z]+-)*[\da-z]+\.)+[a-z]+)"', re.I)

re_sspanel_invitation_num = re.compile(r'剩\D*(\d+)')
re_sspanel_initial_money = re.compile(r'得\s*(\d+(?:\.\d+)?)\s*元')
re_sspanel_sub_url = re.compile(r'https?:')
re_sspanel_expire = re.compile(r'等\D*(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})')
re_sspanel_traffic_today = re.compile(r'日已用\D*?([-+]?\d+(?:\.\d+)?[BKMGTPE]?)', re.I)
re_sspanel_traffic_past = re.compile(r'去已用\D*?([-+]?\d+(?:\.\d+)?[BKMGTPE]?)', re.I)
re_sspanel_traffic_remain = re.compile(r'剩.流量\D*?([-+]?\d+(?:\.\d+)?[BKMGTPE]?)', re.I)
re_sspanel_balance = re.compile(r'(?:余|¥|余额|Balance)\D*?(\d+(?:\.\d+)?)')
re_sspanel_tab_shop_id = re.compile(r'tab-shop-(\d+)')
re_sspanel_plan_num = re.compile(r'plan_\d+')
re_sspanel_plan_id = re.compile(r'buy\D+(\d+)')
re_sspanel_price = re.compile(r'(\d+(?:\.\d+)?)')
re_sspanel_traffic = re.compile(r'\d+(?:\.\d+)?\s*[BKMGTPE]', re.I)
re_sspanel_duration = re.compile(r'(\d+)\s*(天|month)')

def bs(text):
    return BeautifulSoup(text, 'html.parser')

# ==================== 响应包装类 (专项修复：YAML/Tab 报错) ====================
class Response:
    def __init__(self, r, url=""):
        self.__content = getattr(r, 'content', b'')
        self.__headers = getattr(r, 'headers', {})
        self.__status_code = getattr(r, 'status_code', 500)
        self.__reason = getattr(r, 'reason', 'Fail')
        self.__url = str(getattr(r, 'url', url))

    @property
    def content(self): return self.__content
    @property
    def headers(self): return self.__headers
    @property
    def status_code(self): return self.__status_code
    @property
    def ok(self): return 200 <= self.__status_code < 300
    @property
    def reason(self): return self.__reason
    @property
    def url(self): return self.__url
    @property
    def is_redirect(self): return 300 <= self.__status_code < 400

    @property
    @cached
    def text(self):
        try:
            # 核心修复：YAML 严禁 Tab，强制替换为空格，解决 "found character '\t'" 扫描报错
            res = self.__content.decode('utf-8', errors='ignore')
            return res.replace('\t', '    ')
        except: return ""

    @cached
    def json(self):
        try:
            jt = self.text.strip()
            if not (jt.startswith('{') or jt.startswith('[')): return {}
            data = json.loads(jt)
            # 核心修复：强制返回字典，解决 'bool' object has no attribute 'get' 报错
            return data if isinstance(data, dict) else {"data": data}
        except: return {}

    @cached
    def bs(self): return bs(self.text)

    @cached
    def __str__(self): return f'{self.__status_code} {self.__reason} {repr(self.text[:100])}'

# ==================== Session 核心基类 (专项修复：NoneType 拼接崩溃) ====================
class Session:
    def __init__(self, base=None, user_agent=None, max_redirects=5, allow_redirects=7):
        self.session = crequests.Session(impersonate="chrome120", verify=False, trust_env=False)
        self.max_redirects = max_redirects
        self.allow_redirects = allow_redirects
        self.headers = self.session.headers
        self.cookies = self.session.cookies
        self.__base = None
        self.set_base(base)

    def set_base(self, base):
        if base:
            b_str = str(base).split('#', 1)[0]
            self.__base = re_scheme.sub(lambda m: f"{m[1] or 'https'}://", b_str).rstrip('/')
        else: self.__base = None

    def set_origin(self, origin):
        if not origin: return
        if self.__base:
            o_str = str(origin)
            base_split = urlsplit(self.__base)
            scheme = base_split.scheme or 'https'
            origin_split = urlsplit(re_scheme.sub(lambda m: f"{m[1] or scheme}://", o_str))
            self.__base = urlunsplit(origin_split[:2] + base_split[2:]).rstrip('/')
        else: self.set_base(origin)

    set_host = set_origin

    @property
    def base(self): return self.__base or ""
    @property
    def host(self): return urlsplit(self.__base).netloc if self.__base else ""

    def request(self, method: str, url: str = '', data=None, timeout=None, **kwargs):
        # 核心修复：100% 杜绝 'NoneType' object is not iterable / concatenate 报错
        u_str = str(url or "")
        base_str = str(self.__base or "")
        
        if u_str.startswith('http'):
            full_url = u_str
        elif base_str:
            full_url = base_str + '/' + u_str.lstrip('/')
        else:
            full_url = u_str

        # 核心修复：强制超时，防止网络卡死
        if timeout is None:
            timeout = 35 if any(x in full_url for x in ["register", "Verify", "Email"]) else 15
            
        try:
            r = self.session.request(method.upper(), full_url, data=data, timeout=timeout, allow_redirects=True, **kwargs)
            return Response(r)
        except Exception as e:
            class Fake: pass
            f = Fake(); f.content = str(e).encode(); f.status_code = 500; f.headers = {}; f.url = full_url; f.reason = "Fail"
            return Response(f)

    def get(self, url='', **kwargs): return self.request('GET', url, **kwargs)
    def post(self, url='', data=None, **kwargs): return self.request('POST', url, data, **kwargs)
    def reset(self):
        self.cookies.clear()
        self.headers.pop('authorization', None)
        self.headers.pop('token', None)

class _ROSession(Session):
    def __init__(self, base=None, user_agent=None, allow_redirects=REDIRECT_ORIGIN):
        super().__init__(base, user_agent, allow_redirects=allow_redirects)
        self.__times = 0
        self.__redirect_origin_flag = False

    @property
    def redirect_origin(self): return self.__redirect_origin_flag

    def request(self, method, url='', *args, **kwargs):
        r = super().request(method, url, *args, **kwargs)
        if self.__times < 2 and r.ok and r.url and self.base:
            try:
                if urlsplit(r.url).netloc != urlsplit(self.base).netloc:
                    self.set_origin(r.url)
                    self.__redirect_origin_flag = True
            except: pass
            self.__times += 1
        return r

# ==================== V2Board 面板 (增强：注册容错 + 流量激活) ====================
class V2BoardSession(_ROSession):
    def __set_auth(self, email: str, reg_info: dict):
        if not isinstance(reg_info.get('data'), dict): return
        self.login_info = reg_info['data']
        self.email = email
        token = self.login_info.get('auth_data') or self.login_info.get('token')
        if token: self.headers['authorization'] = token

    def get_captcha(self):
        if not ocr: return None
        for path in ['api/v1/passport/comm/captcha', 'api/v1/guest/passport/comm/captcha']:
            res = self.get(path)
            if res.ok and res.json().get('data'):
                try:
                    img = base64.b64decode(res.json()['data'].split(',')[-1])
                    with ocr_lock: return ocr.classification(img)
                except: continue
        return None

    def register(self, email: str, password=None, email_code=None, invite_code=None) -> str | None:
        self.reset()
        pw = password or email.split('@')[0]
        paths = ['api/v1/passport/auth/register', 'api/v1/guest/passport/auth/register', 'api/v1/passport/auth/registerByEmail']
        last_msg = "Fail"
        payload = {'email': email, 'password': pw, 'repassword': pw, 'email_code': email_code or '', 'invite_code': invite_code or ''}
        
        for path in paths:
            res_obj = self.post(path, payload)
            if res_obj.status_code == 404: continue
            res = res_obj.json()
            if 'captcha' in str(res.get('message', '')).lower():
                code = self.get_captcha()
                if code:
                    payload['captcha_code'] = code
                    res = self.post(path, payload).json()
            if res.get('data'):
                self.__set_auth(email, res)
                return None
            last_msg = res.get('message', 'Fail')
            if any(x in str(last_msg) for x in ["邮箱", "邀请码", "已经", "关闭"]): break
        return last_msg

    def buy(self, data=None):
        if not data:
            data = self.get_plan()
            if not data: return None
            data = urlencode(data)
        res = self.post('api/v1/user/order/save', data, headers={'Content-Type': 'application/x-www-form-urlencoded'}).json()
        if not res.get('data'): return None
        self.post('api/v1/user/order/checkout', {'trade_no': res['data']})
        # 关键：激活流量，防止 0B
        self.get(f'api/v1/user/plan/resetByOrder?trade_no={res["data"]}', timeout=10)
        return data

    def get_sub_url(self, **params) -> str:
        self.headers['User-Agent'] = 'Clash.meta'
        try:
            res = self.get('api/v1/user/getSubscribe', timeout=10).json()
            if res.get('data'): return res['data']['subscribe_url']
        except: pass
        tk = self.headers.get('authorization') or self.headers.get('token')
        return f"{self.base}/api/v1/client/subscribe?token={tk}"

    def get_plan(self, min_price=0, max_price=0):
        r = self.get('api/v1/user/plan/fetch').json()
        if 'data' not in r: return None
        min_p, max_p = min_price * 100, max_price * 100
        plan = None; _max = (-1, -1, 0)
        for p in r['data']:
            for i, pd in enumerate(['onetime_price', 'three_year_price', 'year_price', 'half_year_price', 'quarter_price', 'month_price']):
                price = p.get(pd)
                if price is not None and min_p <= price <= max_p:
                    v = (price == 0, p.get('transfer_enable', 0), -i)
                    if v > _max: _max = v; plan = {'period': pd, 'plan_id': p['id']}
        return plan

# ==================== SSPanel 面板 (增强：条款多字段兼容) ====================
class SSPanelSession(_ROSession):
    def __init__(self, host=None, user_agent=None, auth_path=None):
        super().__init__(host, user_agent)
        self.auth_path = auth_path or 'auth'

    def register(self, email: str, password=None, email_code=None, invite_code=None, **kwargs) -> str | None:
        self.reset()
        pw = password or email.split('@')[0]
        # 核心修复：同时发送多种条款参数，解决“请同意服务条款”报错
        payload = {
            'email': email, 'passwd': pw, 'repasswd': pw,
            'agreeterm': 1, 'agree': 1, 'agreement': 1,
            'name': email if kwargs.get('name_eq_email') == 'T' else pw,
            'emailcode': email_code or '', 'code': invite_code or '',
        }
        res = self.post(f'{self.auth_path}/register', payload).json()
        if res.get('ret'): self.email = email; return None
        return res.get('msg', 'Fail')

    def get_sub_url(self, **params) -> str:
        self.headers['User-Agent'] = 'Clash.meta'
        r = self.get('user')
        tag = r.bs().find(attrs={'data-clipboard-text': re_sspanel_sub_url})
        if tag:
            sub_url = tag['data-clipboard-text']
            for k, v in parse_qsl(urlsplit(sub_url).query):
                if k == 'url': return v
            return sub_url
        m = re_var_sub_token.search(r.text)
        if m: return m[1]
        raise Exception('未找到订阅链接')

# ==================== Hkspeedup 面板 ====================
class HkspeedupSession(_ROSession):
    def register(self, email: str, password=None, email_code=None, invite_code=None) -> str | None:
        pw = password or email.split('@')[0]
        res = self.post('user/register', json={'email': email, 'password': pw, 'ensurePassword': pw,
                                             **({'code': email_code} if email_code else {}),
                                             **({'inviteCode': invite_code} if invite_code else {})}).json()
        if res.get('code') == 200: self.email = email; return None
        return res.get('message', 'Fail')

    def get_sub_url(self, **params) -> str:
        res = self.get('user/info').json()
        return f"{self.base}/subscribe/{res.get('data', {}).get('subscribePassword', '')}"

# ==================== 临时邮箱系统 (全源保留 + 自动切换) ====================
class TempEmailSession(_ROSession):
    def get_domains(self) -> list[str]: return []
    def set_email_address(self, address: str): pass
    def get_messages(self) -> list[str]: return []

class MailCX(TempEmailSession):
    def __init__(self): super().__init__('https://api.mail.cx/api/v1/')
    def get_domains(self): return ["mail.cx", "mail.com.de", "chaps.online"]
    def set_email_address(self, address):
        r = self.post('auth/authorize_token')
        if r.ok: 
            self.headers['Authorization'] = f'Bearer {r.text.strip(chr(34))}'
            self.address = address
    def get_messages(self):
        r = self.get(f'mailbox/{self.address}', timeout=12)
        if not r.ok or not isinstance(r.json(), list): return []
        return [self.get(f'mailbox/{self.address}/{m["id"]}').json().get('body', {}).get('text', '') for m in r.json()[:3]]

class Snapmail(TempEmailSession):
    def __init__(self): super().__init__('https://snapmail.cc')
    def get_domains(self): return ["snapmail.cc"]
    def set_email_address(self, address): self.address = address
    def get_messages(self):
        r = self.get(f'emailList/{self.address}', timeout=12)
        return [bs(m['html']).get_text() for m in r.json()] if (r.ok and isinstance(r.json(), list)) else []

class GuerrillaMail(TempEmailSession):
    def __init__(self): super().__init__('https://www.guerrillamail.com/ajax.php')
    def get_domains(self): return ["sharklasers.com", "guerrillamail.net"]
    def set_email_address(self, address): self.get(f'?f=set_email_user&email_user={address.split("@")[0]}')
    def get_messages(self):
        r = self.get('?f=get_email_list&offset=0', timeout=12)
        if not r.ok or not isinstance(r.json(), dict): return []
        return [bs(self.get(f"?f=fetch_email&email_id={m['mail_id']}").json().get('mail_body','')).get_text() for m in r.json().get('list',[])]

class TempEmail:
    def __init__(self, banned_domains=None):
        self.__lock = RLock(); self.__queues = []; self.__banned = set(banned_domains or [])
        self.__session = None; self.__address = None

    @property
    def email(self) -> str:
        with self.__lock:
            if self.__address: return self.__address
            # 自动跳过故障的源（如 mail.cx 宕机时自动切 Snapmail）
            mapping = {"mail.cx": MailCX, "snapmail.cc": Snapmail, "sharklasers.com": GuerrillaMail}
            for domain_key, session_cls in mapping.items():
                try:
                    self.__address = f'{rand_id()}@{domain_key}'
                    self.__session = session_cls()
                    self.__session.set_email_address(self.__address)
                    return self.__address
                except: continue
            raise Exception("All email sources failed")

    def get_email_code(self, keyword, timeout=120):
        queue = Queue(1)
        with self.__lock:
            self.__queues.append((keyword, queue, stime() + timeout))
            if not hasattr(self, '_TempEmail__th') or not self.__th.is_alive():
                self.__th = Thread(target=self.__run, daemon=True); self.__th.start()
        try: return queue.get(timeout=timeout + 5)
        except Empty: return None

    def __run(self):
        while True:
            sleep(6)
            try: msgs = self.__session.get_messages()
            except: msgs = []
            with self.__lock:
                if not self.__queues: break
                nl = 0
                for item in self.__queues:
                    k, q, et = item
                    found = False
                    for m in msgs:
                        if k in str(m):
