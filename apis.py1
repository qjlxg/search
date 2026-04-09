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
from queue import Queue
from random import choice
from threading import RLock, Thread
from time import sleep, time as stime
from urllib.parse import (parse_qsl, unquote_plus, urlencode, urljoin,
                          urlsplit, urlunsplit, quote, parse_qs)

import json5
import urllib3
import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3 import Retry
from urllib3.util import parse_url

# --- 核心增强：过墙级引擎 ---
from curl_cffi import requests as crequests 

# --- 植入：OCR 验证码识别 ---
try:
    import ddddocr
    ocr = ddddocr.DdddOcr(show_ad=False)
    ocr_lock = threading.Lock() # 高并发 CPU 保护锁
except ImportError:
    ocr = None

# --- 原版工具函数导入 ---
from utils import (cached, get, keep, parallel_map, rand_id, str2size,
                   str2timestamp)

# 禁用 SSL 警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

REDIRECT_TO_GET = 1
REDIRECT_ORIGIN = 2
REDIRECT_PATH_QUERY = 4

# ==================== 原版核心正则库 (100% 完整保留 + 优化) ====================
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


# ==================== 响应包装类 (针对 YAML 扫描报错修复) ====================
class Response:
    def __init__(self, r, url=""):
        self.__content = getattr(r, 'content', b'')
        self.__headers = getattr(r, 'headers', {})
        self.__status_code = getattr(r, 'status_code', 500)
        self.__reason = getattr(r, 'reason', 'Fail')
        self.__url = getattr(r, 'url', url)

    @property
    def content(self):
        return self.__content

    @property
    def headers(self):
        return self.__headers

    @property
    def status_code(self):
        return self.__status_code

    @property
    def ok(self):
        return 200 <= self.__status_code < 300

    @property
    def reason(self):
        return self.__reason

    @property
    def url(self):
        return self.__url

    @property
    def is_redirect(self):
        return 300 <= self.__status_code < 400

    @property
    @cached
    def text(self):
        try:
            # 修复：将返回内容中的 Tab 替换为空格，解决 YAML 扫描崩溃
            res = self.__content.decode('utf-8', errors='ignore')
            return res.replace('\t', '    ')
        except:
            return ""

    @cached
    def json(self):
        try:
            jt = self.text.strip()
            if not (jt.startswith('{') or jt.startswith('[')):
                return {}
            return json.loads(jt)
        except:
            return {}

    @cached
    def bs(self):
        return bs(self.text)

    @cached
    def __str__(self):
        return f'{self.__status_code} {self.__reason} {repr(self.text[:100])}'


# ==================== Session 类 (修复 NoneType 拼接报错) ====================
class Session:
    def __init__(self, base=None, user_agent=None, max_redirects=5, allow_redirects=7):
        # 引擎换芯，模拟 Chrome 指纹，禁用 trust_env 提速
        self.session = crequests.Session(impersonate="chrome120", verify=False, trust_env=False)
        self.max_redirects = max_redirects
        self.allow_redirects = allow_redirects
        self.headers = self.session.headers
        self.cookies = self.session.cookies
        self.__base = None
        self.set_base(base)

    def set_base(self, base):
        if base:
            # 修复：强制转 str，解决 NoneType 拼接报错
            b_str = str(base)
            self.__base = re_scheme.sub(lambda m: f"{m[1] or 'https'}://", b_str.split('#', 1)[0]).rstrip('/')
        else:
            self.__base = None

    def set_origin(self, origin):
        if self.__base and origin:
            o_str = str(origin)
            base_split = urlsplit(self.__base)
            origin_split = urlsplit(re_scheme.sub(lambda m: f"{m[1] or base_split[0]}://", o_str))
            self.__base = urlunsplit(origin_split[:2] + base_split[2:]).rstrip('/')
        else:
            self.set_base(origin)

    set_host = set_origin

    @property
    def base(self):
        return self.__base

    @property
    def host(self):
        return urlsplit(self.__base).netloc if self.__base else ""

    @property
    def origin(self):
        if self.__base:
            split = urlsplit(self.__base)
            return f"{split.scheme}://{split.netloc}"
        return None

    def close(self):
        pass

    def reset(self):
        self.cookies.clear()
        self.headers.pop('authorization', None)
        self.headers.pop('token', None)

    def head(self, url='', **kwargs) -> Response:
        return self.request('HEAD', url, **kwargs)

    def get(self, url='', **kwargs) -> Response:
        return self.request('GET', url, **kwargs)

    def post(self, url='', data=None, **kwargs) -> Response:
        return self.request('POST', url, data, **kwargs)

    def put(self, url='', data=None, **kwargs) -> Response:
        return self.request('PUT', url, data, **kwargs)

    def request(self, method: str, url: str = '', data=None, timeout=None, allow_redirects=None, **kwargs):
        method = method.upper()
        # 修复：鲁棒的 URL 拼接，解决 NoneType + str 问题
        u_str = str(url) if url is not None else ""
        base_str = str(self.__base) if self.__base is not None else ""
        
        if u_str.startswith('http'):
            full_url = u_str
        elif base_str:
            full_url = base_str + '/' + u_str.lstrip('/')
        else:
            full_url = u_str

        # 针对 1W 站优化的超时
        if timeout is None:
            timeout = 30 if ("register" in full_url or "Email" in full_url) else 12
            
        try:
            r = self.session.request(
                method, full_url, data=data, 
                timeout=timeout, allow_redirects=True, **kwargs
            )
            return Response(r)
        except Exception as e:
            class Fake: pass
            f = Fake()
            f.content = str(e).encode(); f.status_code = 500; f.headers = {}; f.url = full_url; f.reason = "Fail"
            return Response(f)

    def get_ip_info(self):
        """return (ip, 位置, 运营商)"""
        try:
            ip_raw = self.get("https://ident.me", timeout=5).text.strip()
            if not ip_raw: return ("0.0.0.0", "Unknown", "Unknown")
            addr = self.get(f'https://ip125.com/api/{ip_raw}?lang=zh-CN', timeout=5).json()
            return (
                addr.get('query', '0.0.0.0'),
                addr.get('country', '') + (',' + addr['city'] if addr.get('city') and addr['city'] != addr['country'] else ''),
                addr.get('isp', '') + (',' + addr['org'] if addr.get('org') and addr['org'] != addr['isp'] else '')
            )
        except:
            return ("0.0.0.0", "Unknown", "Unknown")


class _ROSession(Session):
    def __init__(self, base=None, user_agent=None, allow_redirects=REDIRECT_ORIGIN):
        super().__init__(base, user_agent, allow_redirects=allow_redirects)
        self.__times = 0
        self.__redirect_origin_flag = False

    @property
    def redirect_origin(self):
        return self.__redirect_origin_flag

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


# ==================== V2BoardSession (强化探测与多路径) ====================
class V2BoardSession(_ROSession):
    def __set_auth(self, email: str, reg_info: dict):
        self.login_info = reg_info['data']
        self.email = email
        token = self.login_info.get('auth_data') or self.login_info.get('token')
        if token:
            self.headers['authorization'] = token

    def get_captcha(self):
        if not ocr: return None
        for path in ['api/v1/passport/comm/captcha', 'api/v1/guest/passport/comm/captcha']:
            res = self.get(path)
            if res.ok and res.json().get('data'):
                try:
                    img = base64.b64decode(res.json()['data'].split(',')[-1])
                    with ocr_lock:
                        return ocr.classification(img)
                except: continue
        return None

    def reset(self):
        super().reset()
        if hasattr(self, 'login_info'): del self.login_info
        if hasattr(self, 'email'): del self.email

    @staticmethod
    def raise_for_fail(res):
        if 'data' not in res: raise Exception(res)

    def register(self, email: str, password=None, email_code=None, invite_code=None) -> str | None:
        self.reset()
        pw = password or email.split('@')[0]
        paths = [
            'api/v1/passport/auth/register', 
            'api/v1/guest/passport/auth/register', 
            'api/v1/passport/auth/registerByEmail',
            'api/v1/passport/auth/register?type=email'
        ]
        last_msg = "Fail"
        payload = {
            'email': email, 'password': pw, 'repassword': pw,
            'email_code': email_code or '', 'invite_code': invite_code or '',
        }
        
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
            if any(x in last_msg for x in ["邮箱", "邀请码", "已经"]): break
        return last_msg

    def login(self, email: str = None, password=None):
        if hasattr(self, 'login_info') and (not email or email == getattr(self, 'email', None)):
            return
        self.reset()
        pw = password or email.split('@')[0]
        paths = ['api/v1/passport/auth/login', 'api/v1/guest/passport/auth/login']
        for path in paths:
            res = self.post(path, {'email': email, 'password': pw}).json()
            if res.get('data'):
                self.__set_auth(email, res)
                return
        raise Exception("Login Failed")

    def send_email_code(self, email):
        payload = {'email': email}
        code = self.get_captcha()
        if code: payload['captcha_code'] = code
        for path in [
            'api/v1/passport/comm/sendEmailVerify', 
            'api/v1/guest/passport/comm/sendEmailVerify',
            'api/v1/passport/auth/sendEmailVerify'
        ]:
            res = self.post(path, payload, timeout=20)
            if res.status_code != 404: return
        raise Exception("Send Code Failed")

    def buy(self, data=None):
        if not data:
            data = self.get_plan()
            if not data: return None
            data = urlencode(data)
        res = self.post('api/v1/user/order/save', data, headers={'Content-Type': 'application/x-www-form-urlencoded'}).json()
        self.raise_for_fail(res)
        self.post('api/v1/user/order/checkout', {'trade_no': res['data']}).json()
        self.get(f'api/v1/user/plan/resetByOrder?trade_no={res["data"]}', timeout=5)
        return data

    def get_sub_url(self, **params) -> str:
        try:
            res = self.get('api/v1/user/getSubscribe', timeout=8).json()
            if res.get('data'): return res['data']['subscribe_url']
        except: pass
        tk = self.headers.get('authorization') or self.headers.get('token')
        return f"{self.base}/api/v1/client/subscribe?token={tk}"

    def get_sub_info(self):
        res = self.get('api/v1/user/getSubscribe').json()
        self.raise_for_fail(res)
        d = res['data']
        return {'upload': d.get('u', 0), 'download': d.get('d', 0), 'total': d.get('transfer_enable', 0), 'expire': d.get('expired_at', 0) or 0}

    def get_plan(self, min_price=0, max_price=0):
        r = self.get('api/v1/user/plan/fetch').json()
        self.raise_for_fail(r)
        min_p, max_p = min_price * 100, max_price * 100
        plan = None
        _max = (-1, -1, 0)
        for p in r['data']:
            periods = ['onetime_price', 'three_year_price', 'two_year_price', 'year_price', 'half_year_price', 'quarter_price', 'month_price']
            for i, period in enumerate(periods):
                price = p.get(period)
                if price is not None and min_p <= price <= max_p:
                    v = (price == 0, p.get('transfer_enable', 0), -i)
                    if v > _max:
                        _max = v
                        plan = {'period': period, 'plan_id': p['id']}
        return plan


# ==================== SSPanelSession (修复条款与余额清洗) ====================
class SSPanelSession(_ROSession):
    def __init__(self, host=None, user_agent=None, auth_path=None):
        super().__init__(host, user_agent)
        self.auth_path = auth_path or 'auth'

    def reset(self):
        super().reset()
        if hasattr(self, 'email'): del self.email

    @staticmethod
    def raise_for_fail(res):
        if not res.get('ret'): raise Exception(res)

    def register(self, email: str, password=None, email_code=None, invite_code=None, name_eq_email=None, reg_fmt=None, im_type=False, aff=None) -> str | None:
        self.reset()
        email_code_k, invite_code_k = ('email_code', 'invite_code') if reg_fmt == 'B' else ('emailcode', 'code')
        pw = password or email.split('@')[0]
        res = self.post(f'{self.auth_path}/register', {
            'name': email if name_eq_email == 'T' else pw,
            'email': email, 'passwd': pw, 'repasswd': pw,
            'agreeterm': 1, # 修复：自动同意条款
            email_code_k: email_code or '',
            invite_code_k: invite_code or '',
            **({'imtype': 1, 'wechat': pw} if im_type else {}),
            **({'aff': aff} if aff is not None else {}),
        }).json()
        if res.get('ret'):
            self.email = email; return None
        return res.get('msg', 'Fail')

    def login(self, email: str = None, password=None):
        if not email: email = self.email
        if 'email' in self.cookies and email == unquote_plus(self.cookies.get('email','')): return
        self.reset()
        res = self.post(f'{self.auth_path}/login', {
            'email': email, 'passwd': password or email.split('@')[0]
        }).json()
        self.raise_for_fail(res)
        self.email = email

    def send_email_code(self, email):
        res = self.post(f'{self.auth_path}/send', {'email': email}, timeout=60).json()
        self.raise_for_fail(res)

    def buy(self, data=None):
        if not data:
            data = self.get_plan(max_price=self.get_balance())
            if not data: return None
            data = urlencode(data)
        res = self.post('user/buy', data, headers={'Content-Type': 'application/x-www-form-urlencoded'}).json()
        self.raise_for_fail(res)
        return data

    def checkin(self):
        res = self.post('user/checkin').json()
        if not res.get('ret') and not re_checked_in.search(res.get('msg', '')):
            raise Exception(res)

    def get_sub_url(self, **params) -> str:
        r = self.get('user')
        tag = r.bs().find(attrs={'data-clipboard-text': re_sspanel_sub_url})
        if tag:
            sub_url = tag['data-clipboard-text']
            for k, v in parse_qsl(urlsplit(sub_url).query):
                if k == 'url': sub_url = v; break
            return sub_url
        m = re_var_sub_token.search(r.text)
        if m: return m[1]
        raise Exception('未找到订阅链接')

    def get_sub_info(self):
        text = self.get('user').bs().text
        m_today = re_sspanel_traffic_today.search(text)
        m_past = re_sspanel_traffic_past.search(text)
        m_remain = re_sspanel_traffic_remain.search(text)
        if not (m_today and m_past and m_remain): return None
        used = str2size(m_today[1]) + str2size(m_past[1])
        m_expire = re_sspanel_expire.search(text)
        return {'upload': 0, 'download': used, 'total': used + str2size(m_remain[1]), 'expire': str2timestamp(m_expire[1]) if m_expire else 0}

    def get_plan(self, min_price=0, max_price=0):
        doc = self.get('user/shop').bs()
        plan = None; _max = (0, 0, 0)
        def up(id, price, traffic, duration):
            nonlocal plan, _max
            if min_price <= price <= max_price:
                v = (price == 0, traffic, duration)
                if v > _max: _max = v; plan = {'shop': id}

        if (tags := doc.find_all(id=re_sspanel_tab_shop_id)):
            for tag in tags:
                first = tag.find()
                id = int(re_sspanel_tab_shop_id.fullmatch(tag['id'])[1])
                price = float(get(re_sspanel_price.search(first.text), 0, default=0)) if first else 0
                traffic = str2size(get(re_sspanel_traffic.search(tag.text), 0, default='1T'))
                duration = int(get(re_sspanel_duration.search(tag.text), 1, default=999))
                up(id, price, traffic, duration)
        elif (tags := doc.find_all(class_='pricing')):
            for tag in tags:
                m_price_tag = tag.find(class_='pricing-price')
                price = float(re_sspanel_price.search(m_price_tag.text)[1]) if m_price_tag else 0
                traffic = str2size(get(re_sspanel_traffic.search(tag.text), 0, default='1T'))
                onclick_tag = tag.find(attrs={'onclick': True})
                if onclick_tag:
                    m_id = re_sspanel_plan_id.search(onclick_tag['onclick'])
                    if m_id: up(int(m_id[1]), price, traffic, 30)
        return plan

    def get_balance(self) -> float:
        raw_text = self.get('user/code').bs().text
        m = re_sspanel_balance.search(raw_text)
        if m:
            # 修复：清洗数字，移除分号、空格等，解决 '1775839848;' 转 float 报错
            clean_val = re.sub(r'[^\d.]', '', m.group(1))
            return float(clean_val)
        return 0.0


# ==================== HkspeedupSession (1:1 还原) ====================
class HkspeedupSession(_ROSession):
    def register(self, email: str, password=None, email_code=None, invite_code=None) -> str | None:
        pw = password or email.split('@')[0]
        res = self.post('user/register', json={'email': email, 'password': pw, 'ensurePassword': pw,
                                             **({'code': email_code} if email_code else {}),
                                             **({'inviteCode': invite_code} if invite_code else {})}).json()
        if res.get('code') == 200: self.email = email; return None
        return res.get('message', 'Fail')

    def login(self, email: str = None, password=None):
        res = self.post('user/login', json={'email': email, 'password': password or email.split('@')[0]}).json()
        if res.get('code') != 200: raise Exception(res)
        self.headers['token'] = res['data']['token']; self.email = email

    def send_email_code(self, email):
        self.post('user/sendAuthCode', json={'email': email}).json()

    def get_sub_url(self, **params) -> str:
        res = self.get('user/info').json()
        return f"{self.base}/subscribe/{res['data']['subscribePassword']}"


# ==================== 判别类型逻辑 ====================
def guess_panel(host):
    info = {}
    session = _ROSession(host)
    try:
        # V2Board 探测
        r = session.get('api/v1/guest/comm/config', timeout=8)
        if r.ok:
            res_json = r.json()
            info['type'] = 'v2board'; info['name'] = res_json.get('data', {}).get('app_name', 'V2Board')
            return info
        # SSPanel 探测
        r = session.get('auth/login', timeout=8)
        if r.ok and any(x in r.text for x in ['SSPanel', 'checkin', 'staff']):
            info['type'] = 'sspanel'; info['name'] = r.bs().title.text if r.bs().title else "SSPanel"
            return info
        # 处理 Cloudflare 403 后的 V2Board 特征
        if r.status_code == 403 and "v2board" in r.text.lower():
            info['type'] = 'v2board'; return info
    except: pass
    return info


# ==================== 临时邮箱系统 (强化接口兼容) ====================
class TempEmailSession(_ROSession):
    def get_domains(self) -> list[str]: ...
    def set_email_address(self, address: str): ...
    def get_messages(self) -> list[str]: ...

class MailCX(TempEmailSession):
    def __init__(self): super().__init__('https://api.mail.cx/api/v1/')
    def get_domains(self):
        try:
            r = self.get('https://mail.cx')
            js_paths = [js['src'] for js in r.bs().find_all('script') if js.has_attr('src') and re_mailcx_js_path.fullmatch(js['src'])]
            for jp in js_paths:
                m = re_mailcx_domains.search(self.get(urljoin('https://mail.cx', jp)).text)
                if m: return json5.loads(m[1])
        except: pass
        return ["mail.cx", "mail.com.de"]
    def set_email_address(self, address):
        r = self.post('auth/authorize_token')
        if r.ok: self.headers['Authorization'] = f'Bearer {r.json()}'; self.address = address
    def get_messages(self):
        r = self.get(f'mailbox/{self.address}')
        return [self.get(f'mailbox/{self.address}/{m["id"]}').json().get('body', {}).get('text', '') for m in r.json()] if r.ok else []

class Snapmail(TempEmailSession):
    def __init__(self): super().__init__('https://snapmail.cc')
    def get_domains(self):
        r = self.get('scripts/controllers/addEmailBox.js')
        m = re_snapmail_domains.search(r.text)
        return json5.loads(m[1]) if m else ["snapmail.cc"]
    def set_email_address(self, address): self.address = address
    def get_messages(self):
        r = self.get(f'emailList/{self.address}')
        return [bs(m['html']).get_text() for m in r.json()] if (r.ok and isinstance(r.json(), list)) else []

class GuerrillaMail(TempEmailSession):
    def __init__(self): super().__init__('https://www.guerrillamail.com/ajax.php')
    def get_domains(self): return ["sharklasers.com", "guerrillamail.net", "guerrillamailblock.com"]
    def set_email_address(self, address): self.get(f'?f=set_email_user&email_user={address.split("@")[0]}')
    def get_messages(self):
        r = self.get('?f=get_email_list&offset=0')
        if not r.ok: return []
        return [bs(self.get(f"?f=fetch_email&email_id={m['mail_id']}").json().get('mail_body','')).get_text() for m in r.json().get('list',[])]

class Moakt(TempEmailSession):
    def __init__(self): super().__init__('https://moakt.com')
    def get_domains(self): return re_option_domain.findall(self.get().text)
    def set_email_address(self, address):
        u, d = address.split('@'); self.post('inbox', {'domain': d, 'username': u})
    def get_messages(self):
        r = self.get('inbox')
        return [self.get(f"{a['href']}/content").bs().get_text() for a in r.bs().select('.tm-table td:first-child>a')]

class TempEmail:
    def __init__(self, banned_domains=None):
        self.__lock = RLock(); self.__queues = []; self.__banned = set(banned_domains or [])
        self.__session = None

    @property
    @cached
    def email(self) -> str:
        with self.__lock:
            # 修复：自动剔除失效邮箱源并重试
            for _ in range(5):
                try:
                    all_domains = [d for d in temp_email_domain_to_session_type() if d not in self.__banned]
                    domain = choice(all_domains)
                    addr = f'{rand_id()}@{domain}'
                    self.__session = temp_email_domain_to_session_type(domain)()
                    self.__session.set_email_address(addr)
                    return addr
                except:
                    if 'domain' in locals(): self.__banned.add(domain)
            raise Exception("No available email domains")

    def get_email_code(self, keyword, timeout=120):
        queue = Queue(1)
        with self.__lock:
            self.__queues.append((keyword, queue, stime() + timeout))
            if not hasattr(self, '_TempEmail__th'):
                self.__th = Thread(target=self.__run, daemon=True); self.__th.start()
        return queue.get()

    def __run(self):
        while True:
            sleep(4)
            try: msgs = self.__session.get_messages()
            except: msgs = []
            with self.__lock:
                nl = 0
                for item in self.__queues:
                    k, q, et = item
                    for m in msgs:
                        if k in m:
                            code = re_email_code.search(m)
                            if code: q.put(code[1]); break
                    else:
                        if stime() > et: q.put(None)
                        else: self.__queues[nl] = item; nl += 1
                del self.__queues[nl:]
                if nl == 0: del self.__th; break

@cached
def temp_email_domain_to_session_type(domain: str = None):
    sts = TempEmailSession.__subclasses__()
    def fn(st):
        try: ds = st().get_domains()
        except: ds = []
        return st, ds
    mapping = {d: s for s, ds in parallel_map(fn, sts) for d in ds}
    return mapping.get(domain) if domain else mapping


# ==================== 原版核心算法逻辑 (100% 全量还原) ====================
class IP_CIDR_SegmentTree:
    def __init__(self): self.__root = IP_CIDR_SegmentTree._Segment(); self.__version = -1
    def add(self, address: str) -> bool:
        from ipaddress import ip_network
        network = ip_network(address, False)
        prefix = int(network.network_address) >> (network.max_prefixlen - network.prefixlen)
        return self.__root.add(prefix, network.prefixlen)
    class _Segment:
        def __init__(self): self.cover = False; self.children = [None, None]
        def add(self, prefix: int, i: int) -> bool:
            if self.cover: return False
            if i == 0: self.cover = True; return True
            i -= 1; b = (prefix >> i) & 1
            if not self.children[b]: self.children[b] = IP_CIDR_SegmentTree._Segment()
            return self.children[b].add(prefix, i)

class DOMAIN_SUFFIX_Tree:
    def __init__(self): self.__root = DOMAIN_SUFFIX_Tree._Node()
    def add(self, domain: str, suffix=True) -> bool:
        node = self.__root
        for part in reversed(domain.split('.')):
            node = node.next[part]
            if node.flag == 2: return False
        node.flag = 2 if suffix else 1; return True
    class _Node:
        def __init__(self): self.flag = 0; self.next = defaultdict(DOMAIN_SUFFIX_Tree._Node)

class AC:
    def __init__(self): self.__root = AC._Node(); self.__size = 0
    def __len__(self): return self.__size
    def __next(self, node, c):
        edge = node.edges.get(c); return edge.v if edge else self.__root
    def build(self):
        q = deque()
        for e in self.__root.edges.values(): e.v.fail = self.__root; q.append(e.v)
        while q:
            n = q.popleft()
            for c, e in n.edges.items():
                if not e.failed: e.v.fail = self.__next(n.fail, c); q.append(e.v)
            for c, f_e in n.fail.edges.items():
                e = n.edges.get(c)
                if e and e.failed: e.v = f_e.v
                elif not e: n.edges[c] = AC._Edge(f_e.v)
    def add(self, word):
        node = self.__root
        for c in word:
            e = node.edges[c]
            if e.failed: e.failed = False; e.v = AC._Node()
            node = e.v
        node.end = True; node.edges.clear(); self.__size += 1
    def match(self, s):
        node = self.__root
        for c in s:
            if node.end: return True
            node = self.__next(node, c)
        return node.end
    def _eat(self, o): self.__root._eat(o.__root); self.__size += o.__size
    class _Node:
        def __init__(self): self.end = False; self.fail = None; self.edges = defaultdict(AC._Edge)
        def _eat(self, o):
            for c, oe in o.edges.items():
                if not oe.failed:
                    e = self.edges.get(c)
                    if e and not e.failed: e.v._eat(oe.v)
                    else: self.edges[c] = oe
    class _Edge:
        def __init__(self, f=None):
            if f: self.failed = True; self.v = f
            else: self.failed = False; self.v = AC._Node()

class AC_Online:
    def __init__(self): self.__acs = []
    def add(self, word):
        acs = self.__acs; i = len(acs)
        if i == 0 or len(acs[-1]) > 1:
            ac = AC(); ac.add(word); ac.build(); acs.append(ac)
        else:
            i -= 2; b = 2
            while i >= 0 and len(acs[i]) == b: i -= 1; b <<= 1
            i += 1; ac = acs[i]
            for j in range(i + 1, len(acs)): ac._eat(acs[j])
            del acs[i + 1:]; ac.add(word); ac.build()
    def match(self, s): return any(ac.match(s) for ac in self.__acs)

# ==================== 最终定义 ====================
panel_class_map = {'v2board': V2BoardSession, 'sspanel': SSPanelSession, 'hkspeedup': HkspeedupSession}
PanelSession = V2BoardSession | SSPanelSession | HkspeedupSession
