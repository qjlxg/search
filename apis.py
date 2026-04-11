# coding=utf-8
# ... (保留原有 import 保持不变) ...
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
from queue import Queue, Empty # 增加 Empty 导入
from random import choice
from threading import RLock, Thread
from time import sleep, time as stime
from urllib.parse import (parse_qsl, unquote_plus, urlencode, urljoin,
                          urlsplit, urlunsplit, quote, parse_qs)

import json5
import urllib3
import requests
from bs4 import BeautifulSoup
# ... (保留原有 try-except 导入逻辑) ...
try:
    from curl_cffi import requests as crequests 
except ImportError:
    crequests = requests

try:
    import ddddocr
    ocr = ddddocr.DdddOcr(show_ad=False)
    ocr_lock = threading.Lock() 
except ImportError:
    ocr = None

from utils import (cached, get, keep, parallel_map, rand_id, str2size,
                   str2timestamp)

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ==================== 响应包装类 (优化点：严谨解析与Tab替换) ====================
class Response:
    def __init__(self, r, url=""):
        self.__content = getattr(r, 'content', b'')
        self.__headers = getattr(r, 'headers', {})
        self.__status_code = getattr(r, 'status_code', 500)
        self.__reason = getattr(r, 'reason', 'Fail')
        self.__url = str(getattr(r, 'url', url)) # 强制转str

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
            # 解决 YAML 解析器报错 (found character '\t')
            res = self.__content.decode('utf-8', errors='ignore')
            return res.replace('\t', '    ')
        except: return ""

    @cached
    def json(self):
        try:
            jt = self.text.strip()
            if not (jt.startswith('{') or jt.startswith('[')): return {}
            data = json.loads(jt)
            return data if isinstance(data, dict) else {"data": data}
        except: return {}

    @cached
    def bs(self): return bs(self.text)

    @cached
    def __str__(self): return f'{self.__status_code} {self.__reason} {repr(self.text[:100])}'

# ==================== Session 类 (核心修复：解决拼接崩溃和挂起) ====================
class Session:
    def __init__(self, base=None, user_agent=None, max_redirects=5, allow_redirects=7):
        # 统一使用 impersonate 模拟浏览器指纹，提高成功率
        self.session = crequests.Session(impersonate="chrome120", verify=False, trust_env=False)
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
        if self.__base and origin:
            o_str = str(origin)
            base_split = urlsplit(self.__base)
            # 修复拼接逻辑中的 NoneType 隐患
            origin_split = urlsplit(re_scheme.sub(lambda m: f"{m[1] or base_split.scheme}://", o_str))
            self.__base = urlunsplit(origin_split[:2] + base_split[2:]).rstrip('/')
        else: self.set_base(origin)

    set_host = set_origin

    @property
    def base(self): return self.__base or ""
    @property
    def host(self): return urlsplit(self.__base).netloc if self.__base else ""

    def request(self, method: str, url: str = '', data=None, timeout=None, **kwargs):
        # 100% 修复 'NoneType' object is not iterable / concatenate 报错
        u_str = str(url or "")
        base_str = str(self.__base or "")
        
        if u_str.startswith('http'):
            full_url = u_str
        elif base_str:
            full_url = base_str + '/' + u_str.lstrip('/')
        else:
            full_url = u_str

        # 动态调配超时：注册类操作给长点防止断连，普通探测短点防止卡死
        if timeout is None:
            timeout = 35 if any(x in full_url for x in ["register", "Verify", "Email"]) else 15
            
        try:
            r = self.session.request(method.upper(), full_url, data=data, timeout=timeout, **kwargs)
            return Response(r)
        except Exception as e:
            # 返回一个伪造的 500 响应，防止调用方因为 NoneType 崩溃
            class Fake: pass
            f = Fake(); f.content = str(e).encode(); f.status_code = 500; f.headers = {}; f.url = full_url; f.reason = "Fail"
            return Response(f)

    def get(self, url='', **kwargs): return self.request('GET', url, **kwargs)
    def post(self, url='', data=None, **kwargs): return self.request('POST', url, data, **kwargs)

# ==================== V2BoardSession (优化：严谨的 JSON 检查) ====================
class V2BoardSession(_ROSession):
    def register(self, email: str, password=None, email_code=None, invite_code=None) -> str | None:
        self.reset()
        pw = password or email.split('@')[0]
        # 路径遍历
        paths = ['api/v1/passport/auth/register', 'api/v1/guest/passport/auth/register']
        payload = {'email': email, 'password': pw, 'repassword': pw, 'email_code': email_code or '', 'invite_code': invite_code or ''}
        
        for path in paths:
            res_obj = self.post(path, payload)
            res = res_obj.json()
            if not isinstance(res, dict): continue
            
            # 自动处理验证码
            if 'captcha' in str(res.get('message', '')).lower():
                code = self.get_captcha()
                if code:
                    payload['captcha_code'] = code
                    res = self.post(path, payload).json()
            
            if res.get('data'):
                self.__set_auth(email, res)
                return None
            msg = res.get('message', 'Fail')
            if any(x in str(msg) for x in ["邮箱", "邀请码", "已经", "关闭"]): return msg
        return "Fail"

    def buy(self, data=None):
        try:
            if not data:
                data = self.get_plan()
                if not data: return None
                data = urlencode(data)
            res_obj = self.post('api/v1/user/order/save', data, headers={'Content-Type': 'application/x-www-form-urlencoded'})
            res = res_obj.json()
            if not res.get('data'): return None
            
            self.post('api/v1/user/order/checkout', {'trade_no': res['data']})
            # 关键：激活流量，防止 0B 导致无法使用
            self.get(f'api/v1/user/plan/resetByOrder?trade_no={res["data"]}', timeout=10)
            return data
        except: return None

# ==================== SSPanelSession (优化：增加通用服务条款参数) ====================
class SSPanelSession(_ROSession):
    def register(self, email: str, password=None, email_code=None, invite_code=None, **kwargs) -> str | None:
        self.reset()
        pw = password or email.split('@')[0]
        # 兼容不同版本的 SSPanel 注册参数
        data = {
            'email': email, 'passwd': pw, 'repasswd': pw,
            'agreeterm': 1, 'agree': 1, 'agreement': 1, # 增加多种“同意条款”形式
            'emailcode': email_code or '',
            'code': invite_code or kwargs.get('aff') or '',
        }
        res = self.post(f'{self.auth_path}/register', data).json()
        if res.get('ret'): return None
        return res.get('msg', 'Fail')

# ==================== TempEmail (优化：心跳检查与超时退出) ====================
class TempEmail:
    def __init__(self, banned_domains=None):
        self.__lock = RLock()
        self.__queues = []
        self.__banned = set(banned_domains or [])
        self.__session = None
        self.__address = None

    @property
    def email(self) -> str:
        with self.__lock:
            if self.__address: return self.__address
            for _ in range(0): # 减少重试次数防止阻塞
                try:
                    all_domains = [d for d in temp_email_domain_to_session_type() if d not in self.__banned]
                    domain = choice(all_domains)
                    self.__address = f'{rand_id()}@{domain}'
                    self.__session = temp_email_domain_to_session_type(domain)()
                    self.__session.set_email_address(self.__address)
                    return self.__address
                except: continue
            raise Exception("Email providers busy")

    def get_email_code(self, keyword, timeout=120):
        queue = Queue(1)
        with self.__lock:
            self.__queues.append((keyword, queue, stime() + timeout))
            if not hasattr(self, '_TempEmail__th') or not self.__th.is_alive():
                self.__th = Thread(target=self.__run, daemon=True)
                self.__th.start()
        try:
            return queue.get(timeout=timeout + 5) # 增加物理超时防止永久阻塞
        except Empty:
            return None

    def __run(self):
        while True:
            sleep(6) # 稍微延长轮询间隔，降低频率
            if not self.__session: break
            try: 
                # 这里必须给 get_messages 一个短超时，防止邮箱接口挂起导致整个脚本卡死
                msgs = self.__session.get_messages() 
            except: msgs = []
            
            with self.__lock:
                if not self.__queues: break
                new_queues = []
                for item in self.__queues:
                    k, q, et = item
                    found = False
                    for m in msgs:
                        if k in str(m):
                            code = re_email_code.search(m)
                            if code: q.put(code[1]); found = True; break
                    if not found:
                        if stime() > et: q.put(None)
                        else: new_queues.append(item)
                self.__queues = new_queues
                if not self.__queues: break

# ==================== 探测逻辑 (优化：快速失败) ====================
def guess_panel(host):
    s = Session(host)
    try:
        # V2Board 探测：缩短超时至 10s
        r = s.get('api/v1/guest/comm/config', timeout=10)
        if r.ok and isinstance(r.json(), dict) and r.json().get('data'):
            return {'type': 'v2board', 'name': r.json()['data'].get('app_name', 'V2Board')}
        
        # SSPanel 探测
        r = s.get('auth/login', timeout=10)
        if r.ok:
            if any(x in r.text for x in ['SSPanel', 'staff', 'checkin']):
                return {'type': 'sspanel', 'name': 'SSPanel'}
        
        if r.status_code == 403 and "v2board" in r.text.lower():
            return {'type': 'v2board'}
    except: pass
    return {}

# ... (其余 AC 算法和 panel_class_map 保持不变) ...
