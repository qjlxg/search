import requests
import urllib3
from concurrent.futures import ThreadPoolExecutor

# 禁用不安全请求的警告
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

def check_url_logic(url):
    """底层探测逻辑"""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    }
    try:
        # 使用 allow_redirects=True 处理跳转（很多机场会从 http 跳到 https）
        response = requests.get(url, timeout=(5, 10), headers=headers, verify=False, allow_redirects=True)
        if response.status_code < 400:
            return True
    except:
        pass
    return False

def check_url(line):
    line = line.strip()
    if not line:
        return None

    # 1. 如果有协议头，直接测试
    if line.startswith('http://') or line.startswith('https://'):
        if check_url_logic(line):
            print(f"[SUCCESS] {line}")
            return line
    else:
        # 2. 如果没有协议头，先测 http 再测 https
        # 清理掉可能存在的斜杠
        domain = line.lstrip('/')
        
        # 测试 HTTP
        http_url = f"http://{domain}"
        if check_url_logic(http_url):
            print(f"[SUCCESS] {http_url}")
            return http_url
            
        # 测试 HTTPS
        https_url = f"https://{domain}"
        if check_url_logic(https_url):
            print(f"[SUCCESS] {https_url}")
            return https_url
    
    print(f"[FAILED] {line}")
    return None

def main():
    file_path = 'trial.cfg'
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except FileNotFoundError:
        print("Error: trial.cfg not found.")
        return

    header = ""
    urls = []
    if lines:
        # 兼容首行是 'link' 的情况
        if 'link' in lines[0].lower():
            header = lines[0].strip()
            urls = lines[1:]
        else:
            urls = lines

    # 去重并清理空白
    urls = list(dict.fromkeys([u.strip() for u in urls if u.strip()]))
    print(f"Total entries to check: {len(urls)}")

    # 并发测试
    with ThreadPoolExecutor(max_workers=85) as executor:
        results = list(executor.map(check_url, urls))

    # 过滤掉 None 结果
    valid_urls = [url for url in results if url is not None]

    # 保存回文件
    with open(file_path, 'w', encoding='utf-8') as f:
        if header:
            f.write(header + '\n')
        for url in valid_urls:
            f.write(url + '\n')
    
    print(f"Done! Saved {len(valid_urls)} valid links.")

if __name__ == "__main__":
    main()
