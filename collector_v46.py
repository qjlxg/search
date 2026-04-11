import os, json, re, base64, time, traceback, socket, ipaddress
import requests
from urllib.parse import urlparse, parse_qs, quote, urlencode
import concurrent.futures
import geoip2.database
from dns import resolver

print("--- GITHUB COLLECTOR v46.0 (Unified Database + Simplified) START ---")

# --- CONFIGURATION ---
CONFIG_CHUNK_SIZE = 44444
MAX_PREFILTER_WORKERS = 100
COLLECTOR_TOKEN = os.environ.get('COLLECTOR_TOKEN')
VALIDATED_LINKS_FILE = 'validated_subscriptions.json'

# Database configuration
DATABASE_DIR = './database'
DATABASE_BASE_NAME = 'Database'
MAX_DB_SIZE_MB = 44
MAX_DB_FILES = 7

# Active file
ACTIVE_FILE = 'latest_configs.txt'
MAX_ACTIVE_CONFIGS = 4444

# --- SHARED CACHING & GLOBALS ---
dns_cache = {}
geoip_reader = None

COUNTRY_FLAGS = {
    "AD": "🇦🇩", "AE": "🇦🇪", "AF": "🇦🇫", "AG": "🇦🇬", "AI": "🇦🇮", "AL": "🇦🇱", "AM": "🇦🇲", 
    "AO": "🇦🇴", "AQ": "🇦🇶", "AR": "🇦🇷", "AS": "🇦🇸", "AT": "🇦🇹", "AU": "🇦🇺", "AW": "🇦🇼", 
    "AX": "🇦🇽", "AZ": "🇦🇿", "BA": "🇧🇦", "BB": "🇧🇧", "BD": "🇧🇩", "BE": "🇧🇪", "BF": "🇧🇫", 
    "BG": "🇧🇬", "BH": "🇧🇭", "BI": "🇧🇮", "BJ": "🇧🇯", "BL": "🇧🇱", "BM": "🇧🇲", "BN": "🇧🇳", 
    "BO": "🇧🇴", "BR": "🇧🇷", "BS": "🇧🇸", "BT": "🇧🇹", "BW": "🇧🇼", "BY": "🇧🇾", "BZ": "🇧🇿", 
    "CA": "🇨🇦", "CC": "🇨🇨", "CD": "🇨🇩", "CF": "🇨🇫", "CG": "🇨🇬", "CH": "🇨🇭", "CI": "🇨🇮", 
    "CK": "🇨🇰", "CL": "🇨🇱", "CM": "🇨🇲", "CN": "🇨🇳", "CO": "🇨🇴", "CR": "🇨🇷", "CU": "🇨🇺", 
    "CV": "🇨🇻", "CW": "🇨🇼", "CX": "🇨🇽", "CY": "🇨🇾", "CZ": "🇨🇿", "DE": "🇩🇪", "DJ": "🇩🇯", 
    "DK": "🇩🇰", "DM": "🇩🇲", "DO": "🇩🇴", "DZ": "🇩🇿", "EC": "🇪🇨", "EE": "🇪🇪", "EG": "🇪🇬", 
    "EH": "🇪🇭", "ER": "🇪🇷", "ES": "🇪🇸", "ET": "🇪🇹", "FI": "🇫🇮", "FJ": "🇫🇯", "FK": "🇫🇰", 
    "FM": "🇫🇲", "FO": "🇫🇴", "FR": "🇫🇷", "GA": "🇬🇦", "GB": "🇬🇧", "GD": "🇬🇩", "GE": "🇬🇪", 
    "GF": "🇬🇫", "GG": "🇬🇬", "GH": "🇬🇭", "GI": "🇬🇮", "GL": "🇬🇱", "GM": "🇬🇲", "GN": "🇬🇳", 
    "GP": "🇬🇵", "GQ": "🇬🇶", "GR": "🇬🇷", "GT": "🇬🇹", "GU": "🇬🇺", "GW": "🇬🇼", "GY": "🇬🇾", 
    "HK": "🇭🇰", "HN": "🇭🇳", "HR": "🇭🇷", "HT": "🇭🇹", "HU": "🇭🇺", "ID": "🇮🇩", "IE": "🇮🇪", 
    "IL": "🇮🇱", "IM": "🇮🇲", "IN": "🇮🇳", "IO": "🇮🇴", "IQ": "🇮🇶", "IR": "🇮🇷", "IS": "🇮🇸", 
    "IT": "🇮🇹", "JE": "🇯🇪", "JM": "🇯🇲", "JO": "🇯🇴", "JP": "🇯🇵", "KE": "🇰🇪", "KG": "🇰🇬", 
    "KH": "🇰🇭", "KI": "🇰🇮", "KM": "🇰🇲", "KN": "🇰🇳", "KP": "🇰🇵", "KR": "🇰🇷", "KW": "🇰🇼", 
    "KY": "🇰🇾", "KZ": "🇰🇿", "LA": "🇱🇦", "LB": "🇱🇧", "LC": "🇱🇨", "LI": "🇱🇮", "LK": "🇱🇰", 
    "LR": "🇱🇷", "LS": "🇱🇸", "LT": "🇱🇹", "LU": "🇱🇺", "LV": "🇱🇻", "LY": "🇱🇾", "MA": "🇲🇦", 
    "MC": "🇲🇨", "MD": "🇲🇩", "ME": "🇲🇪", "MG": "🇲🇬", "MH": "🇲🇭", "MK": "🇲🇰", "ML": "🇲🇱", 
    "MM": "🇲🇲", "MN": "🇲🇳", "MO": "🇲🇴", "MP": "🇲🇵", "MQ": "🇲🇶", "MR": "🇲🇷", "MS": "🇲🇸", 
    "MT": "🇲🇹", "MU": "🇲🇺", "MV": "🇲🇻", "MW": "🇲🇼", "MX": "🇲🇽", "MY": "🇲🇾", "MZ": "🇲🇿", 
    "NA": "🇳🇦", "NC": "🇳🇨", "NE": "🇳🇪", "NF": "🇳🇫", "NG": "🇳🇬", "NI": "🇳🇮", "NL": "🇳🇱", 
    "NO": "🇳🇴", "NP": "🇳🇵", "NR": "🇳🇷", "NU": "🇳🇺", "NZ": "🇳🇿", "OM": "🇴🇲", "PA": "🇵🇦", 
    "PE": "🇵🇪", "PF": "🇵🇫", "PG": "🇵🇬", "PH": "🇵🇭", "PK": "🇵🇰", "PL": "🇵🇱", "PM": "🇵🇲", 
    "PR": "🇵🇷", "PS": "🇵🇸", "PT": "🇵🇹", "PW": "🇵🇼", "PY": "🇵🇾", "QA": "🇶🇦", "RE": "🇷🇪", 
    "RO": "🇷🇴", "RS": "🇷🇸", "RU": "🇷🇺", "RW": "🇷🇼", "SA": "🇸🇦", "SB": "🇸🇧", "SC": "🇸🇨", 
    "SD": "🇸🇩", "SE": "🇸🇪", "SG": "🇸🇬", "SH": "🇸🇭", "SI": "🇸🇮", "SK": "🇸🇰", "SL": "🇸🇱", 
    "SM": "🇸🇲", "SN": "🇸🇳", "SO": "🇸🇴", "SR": "🇸🇷", "SS": "🇸🇸", "ST": "🇸🇹", "SV": "🇸🇻", 
    "SX": "🇸🇽", "SY": "🇸🇾", "SZ": "🇸🇿", "TC": "🇹🇨", "TD": "🇹🇩", "TG": "🇹🇬", "TH": "🇹🇭", 
    "TJ": "🇹🇯", "TK": "🇹🇰", "TL": "🇹🇱", "TM": "🇹🇲", "TN": "🇹🇳", "TO": "🇹🇴", "TR": "🇹🇷", 
    "TT": "🇹🇹", "TV": "🇹🇻", "TW": "🇹🇼", "TZ": "🇹🇿", "UA": "🇺🇦", "UG": "🇺🇬", "US": "🇺🇸", 
    "UY": "🇺🇾", "UZ": "🇺🇿", "VA": "🇻🇦", "VC": "🇻🇨", "VE": "🇻🇪", "VG": "🇻🇬", "VI": "🇻🇮", 
    "VN": "🇻🇳", "VU": "🇻🇺", "WF": "🇼🇫", "WS": "🇼🇸", "YE": "🇾🇪", "YT": "🇾🇹", "ZA": "🇿🇦", 
    "ZM": "🇿🇲", "ZW": "🇿🇼", "XX": "🔓"
}

# =========================
# UTILITY: Filename Sanitization
# =========================

def sanitize_filename(name):
    """Sanitize a string to be safe for use as a filename."""
    if not name:
        return 'unknown'
    
    name = re.sub(r'[<>:"/\\|?*&=]', '_', name)
    name = re.sub(r'[\x00-\x1f\x7f]', '', name)
    name = re.sub(r'[_\s]+', '_', name)
    name = name.strip('._\t\n\r ')
    
    if len(name) > 100:
        name = name[:100].rstrip('._')
    
    if not name:
        name = 'unknown'
    
    return name.lower()

# =========================
# Database Management (Unified)
# =========================

def ensure_database_dir():
    """Ensure database directory exists."""
    if not os.path.exists(DATABASE_DIR):
        os.makedirs(DATABASE_DIR)
        print(f"📁 Created database directory: {DATABASE_DIR}")

def get_database_files():
    """Get all database files sorted by number."""
    ensure_database_dir()
    files = []
    for i in range(1, MAX_DB_FILES + 1):
        filepath = os.path.join(DATABASE_DIR, f"{DATABASE_BASE_NAME}_{i}.txt")
        if os.path.exists(filepath):
            files.append(filepath)
    return files

def get_current_database_file():
    """Get the current active database file (last one or create first)."""
    files = get_database_files()
    if not files:
        return os.path.join(DATABASE_DIR, f"{DATABASE_BASE_NAME}_1.txt")
    return files[-1]

def get_next_database_file(current_file):
    """Get next database file in rotation."""
    current_name = os.path.basename(current_file)
    match = re.search(r'_(\d+)\.txt$', current_name)
    if match:
        current_num = int(match.group(1))
        next_num = (current_num % MAX_DB_FILES) + 1
        return os.path.join(DATABASE_DIR, f"{DATABASE_BASE_NAME}_{next_num}.txt")
    return os.path.join(DATABASE_DIR, f"{DATABASE_BASE_NAME}_1.txt")

def load_database_file(filepath):
    """Load a single database file (base64 encoded)."""
    if not os.path.exists(filepath):
        return set()
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read().strip()
            if not content:
                return set()
            decoded = base64.b64decode(content).decode('utf-8')
            return set(decoded.splitlines())
    except Exception as e:
        print(f"Warning: Could not load {filepath}: {e}")
        return set()

def load_all_databases():
    """Load configs from ALL database files."""
    all_configs = set()
    files = get_database_files()
    
    if not files:
        print(f"  No database files found in {DATABASE_DIR}")
        return all_configs
    
    print(f"  Loading from {len(files)} database file(s):")
    for db_file in files:
        configs = load_database_file(db_file)
        all_configs.update(configs)
        size_mb = os.path.getsize(db_file) / (1024 * 1024)
        print(f"    • {os.path.basename(db_file)}: {len(configs)} configs ({size_mb:.2f} MB)")
    
    return all_configs

def save_database(new_configs_list):
    """Save new configs to database with rotation."""
    if not new_configs_list:
        return None
    
    ensure_database_dir()
    current_file = get_current_database_file()
    
    # Load existing from current file only
    existing = load_database_file(current_file)
    combined = existing.union(set(new_configs_list))
    
    # Prepare content
    content = "\n".join(sorted(combined))
    encoded = base64.b64encode(content.encode('utf-8')).decode('utf-8')
    size_mb = len(encoded.encode('utf-8')) / (1024 * 1024)
    
    # Check if rotation needed
    if size_mb > MAX_DB_SIZE_MB and existing:
        next_file = get_next_database_file(current_file)
        print(f"  ⚠️  {os.path.basename(current_file)} would be {size_mb:.2f}MB (limit: {MAX_DB_SIZE_MB}MB)")
        print(f"  🔄 Rotating to: {os.path.basename(next_file)}")
        
        # Save only new configs to next file
        new_content = "\n".join(sorted(new_configs_list))
        new_encoded = base64.b64encode(new_content.encode('utf-8')).decode('utf-8')
        
        with open(next_file, 'w', encoding='utf-8') as f:
            f.write(new_encoded)
        
        new_size_mb = len(new_encoded.encode('utf-8')) / (1024 * 1024)
        print(f"  ✅ Saved {len(new_configs_list)} configs to {os.path.basename(next_file)} ({new_size_mb:.2f}MB)")
        return next_file
    else:
        with open(current_file, 'w', encoding='utf-8') as f:
            f.write(encoded)
        print(f"  ✅ Updated {os.path.basename(current_file)} ({size_mb:.2f}MB, {len(combined)} total configs)")
        return current_file

# =========================
# Active File Management
# =========================

def save_active_file(configs_list):
    """Save active file (base64 encoded, capped)."""
    try:
        configs_to_save = configs_list[-MAX_ACTIVE_CONFIGS:] if len(configs_list) > MAX_ACTIVE_CONFIGS else configs_list
        content = "\n".join(configs_to_save)
        encoded = base64.b64encode(content.encode('utf-8')).decode('utf-8')
        with open(ACTIVE_FILE, 'w', encoding='utf-8') as f:
            f.write(encoded)
        return len(configs_to_save)
    except Exception as e:
        print(f"Error saving {ACTIVE_FILE}: {e}")
        return 0

def load_active_file():
    """Load active file."""
    if not os.path.exists(ACTIVE_FILE):
        return []
    try:
        with open(ACTIVE_FILE, 'r') as f:
            content = f.read()
            if content:
                return base64.b64decode(content).decode('utf-8').splitlines()
    except Exception as e:
        print(f"Error loading {ACTIVE_FILE}: {e}")
    return []

def get_config_fingerprint(config_str):
    """Get unique fingerprint for deduplication."""
    try:
        if config_str.startswith('vmess://'):
            vmess_data = parse_vmess_config(config_str)
            if not vmess_data:
                return None
            return f"vmess|{vmess_data.get('add', '')}|{vmess_data.get('port', '')}|{vmess_data.get('id', '')}"
        elif config_str.startswith(('vless://', 'trojan://')):
            parsed = urlparse(config_str)
            try:
                port = parsed.port or ''
            except:
                port = ''
            return f"{parsed.scheme}|{parsed.hostname}|{port}|{parsed.username}"
        elif config_str.startswith('ss://'):
            parts = config_str.split('@')
            if len(parts) == 2:
                return f"ss|{parts[1].split('#')[0]}|{parts[0].replace('ss://', '')}"
        else:
            parsed = urlparse(config_str)
            try:
                port = parsed.port or ''
            except:
                port = ''
            return f"{parsed.scheme}|{parsed.hostname}|{port}|{parsed.username}"
    except Exception:
        return None

def merge_configs_by_fingerprint(existing_list, new_list):
    """Merge existing + new, deduplicate, cap to newest."""
    combined = existing_list + new_list
    seen = set()
    dedup_rev = []
    for cfg in reversed(combined):
        fp = get_config_fingerprint(cfg)
        key = fp if fp else f"RAW::{cfg}"
        if key not in seen:
            dedup_rev.append(cfg)
            seen.add(key)
    dedup = list(reversed(dedup_rev))
    if len(dedup) > MAX_ACTIVE_CONFIGS:
        dedup = dedup[-MAX_ACTIVE_CONFIGS:]
    return dedup

# =========================
# DNS Resolution & Parsing
# =========================

def country_code_to_flag(iso_code):
    return COUNTRY_FLAGS.get(iso_code, "🌐")

def is_ip_address(hostname):
    """Check if hostname is an IP address."""
    if not hostname:
        return False
    try:
        ipaddress.ip_address(hostname)
        return True
    except ValueError:
        return False

def resolve_domain_to_ip(hostname):
    """Resolve domain to IP, return None if already IP or resolution fails."""
    if not hostname:
        return None
    
    # Already an IP - return as-is
    if is_ip_address(hostname):
        return hostname
    
    # Check cache
    if hostname in dns_cache:
        return dns_cache[hostname]
    
    # DNS resolution
    try:
        res = resolver.Resolver()
        res.nameservers = ["8.8.8.8", "1.1.1.1"]
        ip_addr = res.resolve(hostname, 'A')[0].to_text()
        dns_cache[hostname] = ip_addr
        return ip_addr
    except Exception:
        dns_cache[hostname] = None
        return None

def parse_vmess_config(config_str):
    """Parse VMess config from base64."""
    try:
        encoded = config_str.replace('vmess://', '').strip().rstrip('.,;!?')
        missing_padding = len(encoded) % 4
        if missing_padding:
            encoded += '=' * (4 - missing_padding)
        decoded_bytes = base64.b64decode(encoded, validate=True)
        for encoding in ['utf-8', 'latin-1', 'iso-8859-1', 'cp1252']:
            try:
                decoded = decoded_bytes.decode(encoding, errors='ignore')
                parsed = json.loads(decoded)
                if 'add' in parsed and 'port' in parsed and 'id' in parsed:
                    return parsed
            except Exception:
                continue
        return None
    except Exception:
        return None

def replace_domain_with_ip(config_str):
    """
    Replace domain with IP address if the address is a domain.
    Preserves original domain in SNI/host parameters.
    If already IP, returns unchanged.
    """
    try:
        if config_str.startswith('vmess://'):
            vmess_data = parse_vmess_config(config_str)
            if not vmess_data:
                return config_str
            
            address = vmess_data.get('add', '')
            
            # Already IP - no change needed
            if is_ip_address(address):
                return config_str
            
            # Resolve domain to IP
            ip_addr = resolve_domain_to_ip(address)
            if not ip_addr or ip_addr == address:
                return config_str
            
            # Preserve original domain in SNI if TLS
            if vmess_data.get('tls') == 'tls' and not vmess_data.get('sni'):
                vmess_data['sni'] = address
            
            # Preserve original domain in host if WS/HTTP
            net = vmess_data.get('net', '').lower()
            if net in ['ws', 'http', 'h2'] and not vmess_data.get('host'):
                vmess_data['host'] = address
            
            vmess_data['add'] = ip_addr
            new_json = json.dumps(vmess_data, separators=(',', ':'))
            return f"vmess://{base64.b64encode(new_json.encode('utf-8')).decode('utf-8')}"
        
        elif config_str.startswith(('vless://', 'trojan://')):
            parsed = urlparse(config_str)
            hostname = parsed.hostname
            
            # Already IP - no change needed
            if is_ip_address(hostname):
                return config_str
            
            # Resolve domain to IP
            ip_addr = resolve_domain_to_ip(hostname)
            if not ip_addr or ip_addr == hostname:
                return config_str
            
            params = parse_qs(parsed.query)
            security = params.get('security', [''])[0]
            network_type = params.get('type', [''])[0]
            
            # Preserve original domain in SNI for TLS/Reality
            if security in ['tls', 'reality'] and 'sni' not in params:
                params['sni'] = [hostname]
            
            # Preserve original domain in host for WS/HTTP
            if network_type in ['ws', 'http', 'h2'] and 'host' not in params:
                params['host'] = [hostname]
            
            new_query = urlencode(params, doseq=True)
            new_netloc = ip_addr
            try:
                if parsed.port:
                    new_netloc = f"{ip_addr}:{parsed.port}"
            except:
                pass
            if parsed.username:
                new_netloc = f"{parsed.username}@{new_netloc}"
            
            return parsed._replace(netloc=new_netloc, query=new_query).geturl()
        
        elif config_str.startswith('ss://'):
            parts = config_str.split('@')
            if len(parts) != 2:
                return config_str
            
            prefix, suffix = parts[0], parts[1]
            fragment = ''
            if '#' in suffix:
                suffix, fragment = suffix.split('#', 1)
                fragment = f'#{fragment}'
            
            if ':' in suffix:
                hostname, port = suffix.rsplit(':', 1)
            else:
                hostname, port = suffix, '443'
            
            # Already IP - no change needed
            if is_ip_address(hostname):
                return config_str
            
            ip_addr = resolve_domain_to_ip(hostname)
            if ip_addr and ip_addr != hostname:
                return f"{prefix}@{ip_addr}:{port}{fragment}"
            return config_str
        
        return config_str
    except Exception:
        return config_str

def get_country_from_hostname(hostname):
    """Get country code from hostname."""
    if not hostname:
        return "XX"
    
    # Resolve to IP first
    if not is_ip_address(hostname):
        ip_addr = resolve_domain_to_ip(hostname)
    else:
        ip_addr = hostname
    
    if not ip_addr or not geoip_reader:
        return "XX"
    
    try:
        return geoip_reader.country(ip_addr).country.iso_code or "XX"
    except Exception:
        return "XX"

def get_config_attributes(config_str):
    """Extract config attributes for categorization."""
    try:
        if config_str.startswith('vmess://'):
            vmess_data = parse_vmess_config(config_str)
            if not vmess_data:
                return None
            protocol = 'vmess'
            network = vmess_data.get('net', 'tcp').lower().strip()
            security = vmess_data.get('tls', 'none').lower().strip()
            country = get_country_from_hostname(vmess_data.get('add', '')).upper()
        else:
            parsed = urlparse(config_str)
            params = parse_qs(parsed.query)
            protocol = parsed.scheme.lower().strip()
            hostname = parsed.hostname
            network = params.get('type', ['tcp'])[0].lower().strip()
            security = params.get('security', ['none'])[0].lower().strip()
            if security != 'reality' and 'pbk' in params:
                security = 'reality'
            country = get_country_from_hostname(hostname).upper()
        
        valid_protocols = ['vmess', 'vless', 'trojan', 'ss', 'hy2', 'hysteria', 'tuic', 'juicity']
        if not protocol or protocol not in valid_protocols:
            return None
        
        valid_networks = ['tcp', 'kcp', 'ws', 'http', 'quic', 'grpc', 'h2', 'httpupgrade', 'splithttp']
        if not network or network not in valid_networks:
            network = 'tcp'
        
        valid_security = ['none', 'tls', 'reality', 'xtls']
        if not security or security not in valid_security:
            security = 'none'
        
        if not country or len(country) != 2 or not country.isalpha():
            country = 'XX'
        
        return {'protocol': protocol, 'network': network, 'security': security, 'country': country}
    except Exception:
        return None

def rename_config(config_str, country_code):
    """Rename config with country flag."""
    try:
        flag = country_code_to_flag(country_code)
        new_name = f"{flag} @MoboNetPC {flag}"
        return f"{config_str.split('#')[0]}#{quote(new_name)}"
    except Exception:
        return config_str

# =========================
# File System Helpers
# =========================

def setup_directories():
    """Setup required directories."""
    import shutil
    dirs = ['./splitted', './protocols', './networks', './countries', './security', './flow']
    for d in dirs:
        if os.path.exists(d):
            shutil.rmtree(d)
        os.makedirs(d)
    ensure_database_dir()
    print("INFO: Directories ready.")

def json_load_safe(path):
    """Safely load JSON file."""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception as e:
        print(f"ERROR loading {path}: {e}")
        return []

def find_configs_raw(text):
    """Find config strings in text."""
    if not text:
        return []
    pattern = r'(?:vless|vmess|trojan|ss|hy2|hysteria|tuic|juicity)://[^\s<>"\'`]+'
    return re.findall(pattern, text, re.IGNORECASE)

def check_host_port_with_socket(host_port):
    """Check if host:port is reachable."""
    try:
        host, port_str = host_port.rsplit(':', 1)
        port = int(port_str)
        with socket.create_connection((host, port), timeout=1.5):
            return host_port
    except:
        return None

def write_chunked_subscription_files(base_filepath, configs):
    """Write configs to files in chunks."""
    base_filepath = base_filepath.replace('..', '_')
    
    # Prevent writing to sensitive directories
    if '.github' in base_filepath or 'workflows' in base_filepath:
        print(f"WARNING: Skipping write to sensitive path: {base_filepath}")
        return
    
    dir_path = os.path.dirname(base_filepath)
    if dir_path:
        try:
            os.makedirs(dir_path, exist_ok=True)
        except Exception as e:
            print(f"ERROR: Could not create directory {dir_path}: {e}")
            return
    
    if not configs:
        try:
            with open(base_filepath, "w", encoding="utf-8") as f:
                f.write("")
        except Exception as e:
            print(f"ERROR: Could not write empty file {base_filepath}: {e}")
        return
    
    chunks = [configs[i:i + CONFIG_CHUNK_SIZE] for i in range(0, len(configs), CONFIG_CHUNK_SIZE)]
    
    for i, chunk in enumerate(chunks):
        if i == 0:
            filepath = base_filepath
        else:
            filepath = os.path.join(
                os.path.dirname(base_filepath),
                f"{os.path.basename(base_filepath)}{i + 1}"
            )
        
        try:
            content = base64.b64encode("\n".join(chunk).encode("utf-8")).decode("utf-8")
            with open(filepath, "w", encoding="utf-8") as f:
                f.write(content)
        except Exception as e:
            print(f"ERROR: Could not write file {filepath}: {e}")

# =========================
# Data Collection Functions
# =========================

def fetch_from_direct_aggregators():
    """Fetch from direct aggregator sources."""
    print("\n--- [TIER 1] Direct Aggregators ---")
    configs = set()
    aggregators = [
        'https://raw.githubusercontent.com/qjlxg/one/refs/heads/main/nodes_list.txt',
        'https://www.aicvideo.info/s/d6c6927922df7ce68652f8e8bcbfec4c#0',
    
    ]
    for url in aggregators:
        try:
            response = requests.get(url, timeout=15)
            if response.status_code == 200:
                content = response.text
                if re.match(r'^[A-Za-z0-9+/=]{100,}$', content.strip().replace('\n', '')):
                    try:
                        content = base64.b64decode(content).decode('utf-8', 'ignore')
                    except:
                        pass
                found = find_configs_raw(content)
                if found:
                    configs.update(found)
                    print(f"  ✓ {url.split('/')[-3]}: {len(found)} configs")
            time.sleep(0.5)
        except Exception as e:
            print(f"  ✗ {url}: {e}")
            continue
    print(f"Collected {len(configs)} from aggregators")
    return configs

def fetch_from_github_code_search():
    """Fetch from GitHub code search."""
    print("\n--- [TIER 2] GitHub Code Search ---")
    if not COLLECTOR_TOKEN:
        print("  ⚠ No token, skipping")
        return set()
    
    configs = set()
    headers = {'Authorization': f'token {COLLECTOR_TOKEN}', 'Accept': 'application/vnd.github.v3.raw'}
    queries = [
        '"vless" "کانفیگ" "رایگان"', '"vmess" "ایرانسل"', '"trojan" "همراه اول"',
        '"v2ray" "رایتل"', 'filename:subscribe "v2ray" "ایران"', '"reality" "کانفیگ"',
        '"vmess://" "subscription"', '"vless://" "subscription"', '"trojan://" "free"',
        '"vmess" "免费"', '"v2ray" "订阅"', '"节点" "分享"', '"翻墙" "配置"',
        '"vmess" "бесплатно"', '"v2ray" "подписка"', '"прокси" "бесплатно"',
        'filename:subscription.txt "vmess"', 'filename:sub.txt "vless"',
        'filename:all.txt "vmess://"', 'path:subscribe "vmess://"',
        '"hy2://"', '"tuic://"', '"reality" "grpc"', '"vless" "xtls"',
        '"clash" "proxies:" extension:yaml', '"vmess://" pushed:>2024-06-01',
        'size:>10000 "vmess://"', '"collector" "vmess"', '"aggregator" "v2ray"',
        '"xtls-rprx-vision"', '"flow=xtls-rprx-vision"', '"reality" "vision"',
    ]
    
    query_count = 0
    for query in queries:
        if query_count >= 30:
            break
        search_url = f"https://api.github.com/search/code?q={query}&sort=indexed&order=desc&per_page=100"
        try:
            time.sleep(6)
            res = requests.get(search_url, headers=headers, timeout=30)
            if res.status_code == 403:
                print(f"  Rate limit hit, stopping code search")
                break
            res.raise_for_status()
            items = res.json().get('items', [])
            if items:
                print(f"  Query {query_count + 1}: {len(items)} files")
            for item in items:
                time.sleep(0.5)
                try:
                    content_res = requests.get(item.get('url'), headers=headers, timeout=10)
                    if content_res.status_code == 200:
                        content = content_res.text
                        if re.match(r'^[A-Za-z0-9+/=]{100,}$', content.strip().replace('\n', '')):
                            try:
                                content = base64.b64decode(content).decode('utf-8', 'ignore')
                            except:
                                pass
                        configs.update(find_configs_raw(content))
                except:
                    continue
            query_count += 1
        except Exception as e:
            if 'rate limit' in str(e).lower():
                break
            continue
    print(f"Collected {len(configs)} from code search")
    return configs

def fetch_from_github_repos_smart():
    """Fetch from GitHub repos."""
    print("\n--- [TIER 2] Smart Repo Search ---")
    if not COLLECTOR_TOKEN:
        return set()
    
    configs = set()
    headers = {'Authorization': f'token {COLLECTOR_TOKEN}'}
    repo_queries = ['v2ray subscription', 'proxy subscription', 'v2ray collector']
    
    for query in repo_queries[:2]:
        try:
            time.sleep(6)
            search_url = f"https://api.github.com/search/repositories?q={query}&sort=updated&per_page=10"
            res = requests.get(search_url, headers=headers, timeout=30)
            if res.status_code != 200:
                continue
            repos = res.json().get('items', [])
            print(f"  '{query}': {len(repos)} repos")
            
            for repo in repos:
                try:
                    time.sleep(1)
                    default_branch = repo.get('default_branch', 'main')
                    tree_url = f"https://api.github.com/repos/{repo['full_name']}/git/trees/{default_branch}?recursive=1"
                    tree_res = requests.get(tree_url, headers=headers, timeout=10)
                    if tree_res.status_code != 200:
                        continue
                    tree = tree_res.json().get('tree', [])
                    promising_files = []
                    
                    for file_obj in tree:
                        path = file_obj.get('path', '')
                        if file_obj.get('type') == 'blob':
                            lower_path = path.lower()
                            if any(k in lower_path for k in ['sub', 'config', 'node', 'proxy', 'v2ray', 'all', 'merge']) and path.endswith(('.txt', '.yaml', '.yml')):
                                promising_files.append(path)
                    
                    for file_path in promising_files[:5]:
                        try:
                            time.sleep(0.5)
                            raw_url = f"https://raw.githubusercontent.com/{repo['full_name']}/{default_branch}/{file_path}"
                            content_res = requests.get(raw_url, timeout=10)
                            if content_res.status_code == 200:
                                content = content_res.text
                                if re.match(r'^[A-Za-z0-9+/=]{100,}$', content.strip().replace('\n', '')):
                                    try:
                                        content = base64.b64decode(content).decode('utf-8', 'ignore')
                                    except:
                                        pass
                                found = find_configs_raw(content)
                                if found:
                                    configs.update(found)
                                    print(f"    ✓ {repo['name']}/{file_path}: {len(found)}")
                        except:
                            continue
                except:
                    continue
        except:
            continue
    print(f"Collected {len(configs)} from smart repo search")
    return configs

def load_validated_links():
    """Load validated links from file."""
    try:
        with open(VALIDATED_LINKS_FILE, 'r') as f:
            return json.load(f)
    except:
        return {}

def save_validated_links(links_data):
    """Save validated links to file."""
    try:
        with open(VALIDATED_LINKS_FILE, 'w') as f:
            json.dump(links_data, f, indent=2)
    except:
        pass

def fetch_and_validate_readme_links():
    """Fetch from validated README links."""
    print("\n--- [TIER 3] README Links ---")
    if not COLLECTOR_TOKEN:
        return set()
    
    configs = set()
    validated_links = load_validated_links()
    print("  Testing cached links...")
    working_links = {}
    
    for link, metadata in validated_links.items():
        try:
            response = requests.get(link, timeout=10)
            if response.status_code == 200:
                found = find_configs_raw(response.text)
                if found:
                    configs.update(found)
                    working_links[link] = {'last_success': time.time(), 'total_configs': len(found)}
            time.sleep(0.3)
        except:
            continue
    
    save_validated_links(working_links)
    print(f"Collected {len(configs)} from validated links")
    return configs

# =========================
# Pre-filtering
# =========================

def pre_filter_live_hosts(all_configs):
    """Pre-filter configs by checking host connectivity."""
    print(f"\n--- Pre-filtering {len(all_configs)} configs ---")
    
    fingerprint_to_config = {}
    for config in all_configs:
        fp = get_config_fingerprint(config)
        if fp and fp not in fingerprint_to_config:
            fingerprint_to_config[fp] = config
    print(f"After deduplication: {len(fingerprint_to_config)} unique")
    
    host_port_to_fingerprint = {}
    parse_errors = 0
    
    for fp, config in fingerprint_to_config.items():
        try:
            if config.startswith('vmess://'):
                vmess_data = parse_vmess_config(config)
                if not vmess_data:
                    continue
                host, port = vmess_data.get('add'), vmess_data.get('port')
            else:
                parsed = urlparse(config)
                host = parsed.hostname
                try:
                    port = parsed.port
                except:
                    parse_errors += 1
                    continue
            
            if not host or not port:
                continue
            
            try:
                port = int(port)
            except:
                parse_errors += 1
                continue
            
            if port < 1 or port > 65535:
                parse_errors += 1
                continue
            
            ip_addr = resolve_domain_to_ip(host)
            if not ip_addr:
                continue
            
            host_port_key = f"{ip_addr}:{port}"
            if host_port_key not in host_port_to_fingerprint:
                host_port_to_fingerprint[host_port_key] = fp
        except:
            parse_errors += 1
            continue
    
    if parse_errors > 0:
        print(f"Skipped {parse_errors} malformed")
    print(f"Testing {len(host_port_to_fingerprint)} unique host:port pairs...")
    
    live_host_ports = set()
    hosts_to_test = list(host_port_to_fingerprint.keys())
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_PREFILTER_WORKERS) as executor:
        future_to_host = {executor.submit(check_host_port_with_socket, hp): hp for hp in hosts_to_test}
        for i, future in enumerate(concurrent.futures.as_completed(future_to_host)):
            if (i + 1) % 1000 == 0:
                print(f"  Tested {i+1}/{len(hosts_to_test)}...")
            result = future.result()
            if result:
                live_host_ports.add(result)
    
    live_fingerprints = {host_port_to_fingerprint[hp] for hp in live_host_ports if hp in host_port_to_fingerprint}
    live_configs = [fingerprint_to_config[fp] for fp in live_fingerprints if fp in fingerprint_to_config]
    print(f"Pre-filter complete: {len(live_configs)} live configs")
    return live_configs

# =========================
# Processing
# =========================

def process_configs(configs):
    """Process configs: convert domain to IP, extract attributes, rename."""
    print(f"\n--- Processing {len(configs)} configs ---")
    
    processed = []
    stats = {'converted': 0, 'failed_attrs': 0}
    
    for config in configs:
        # Convert domain to IP (if needed)
        ip_config = replace_domain_with_ip(config)
        if ip_config != config:
            stats['converted'] += 1
        
        # Get attributes
        attrs = get_config_attributes(ip_config)
        if not attrs:
            stats['failed_attrs'] += 1
            continue
        
        # Rename with country flag
        final_config = rename_config(ip_config, attrs['country'])
        processed.append({'config': final_config, 'attrs': attrs})
    
    print(f"Converted {stats['converted']} domains to IP, failed to parse {stats['failed_attrs']}")
    return processed

# =========================
# Main Execution
# =========================

def main():
    global geoip_reader
    
    print("DEBUG: main() function started")
    print(f"DEBUG: Current directory: {os.getcwd()}")
    print(f"DEBUG: COLLECTOR_TOKEN exists: {bool(COLLECTOR_TOKEN)}")
    
    try:
        setup_directories()
        print("DEBUG: Directories setup complete")
    except Exception as e:
        print(f"ERROR in setup_directories: {e}")
        traceback.print_exc()
        return
    
    # Download GeoIP
    db_path = "./geoip.mmdb"
    if not os.path.exists(db_path):
        print("Downloading GeoIP...")
        for url in [
            "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb",
            "https://raw.githubusercontent.com/Loyalsoldier/geoip/release/Country.mmdb"
        ]:
            try:
                r = requests.get(url, allow_redirects=True, timeout=30)
                if r.status_code == 200:
                    with open(db_path, 'wb') as f:
                        f.write(r.content)
                    print(f"✓ GeoIP downloaded from {url}")
                    break
            except Exception as e:
                print(f"Failed to download from {url}: {e}")
                continue
    
    try:
        geoip_reader = geoip2.database.Reader(db_path)
        print("DEBUG: GeoIP reader initialized")
    except Exception as e:
        print(f"Warning: GeoIP load failed: {e}")
    
    # Collect from all sources
    all_raw_configs = set()
    
    print("\n--- Collecting from subscription links.json ---")
    subs_links = json_load_safe('subscription links.json')
    print(f"DEBUG: Loaded {len(subs_links)} subscription links")
    
    for i, link in enumerate(subs_links):
        try:
            print(f"  Fetching link {i+1}/{len(subs_links)}: {link}")
            content = requests.get(link, timeout=15).text
            if re.match(r'^[A-Za-z0-9+/=]{100,}$', content.strip().replace('\n', '')):
                try:
                    content = base64.b64decode(content).decode('utf-8', 'ignore')
                except:
                    pass
            found = find_configs_raw(content)
            all_raw_configs.update(found)
            print(f"    Found {len(found)} configs")
        except Exception as e:
            print(f"  ERROR fetching {link}: {e}")
            continue
    print(f"✓ Local: {len(all_raw_configs)} configs")
    
    # Fetch from other sources
    try:
        all_raw_configs.update(fetch_from_direct_aggregators())
    except Exception as e:
        print(f"ERROR in aggregators: {e}")
    
    try:
        all_raw_configs.update(fetch_from_github_code_search())
    except Exception as e:
        print(f"ERROR in code search: {e}")
    
    try:
        all_raw_configs.update(fetch_from_github_repos_smart())
    except Exception as e:
        print(f"ERROR in smart repos: {e}")
    
    try:
        all_raw_configs.update(fetch_and_validate_readme_links())
    except Exception as e:
        print(f"ERROR in README links: {e}")
    
    print(f"\n{'='*70}")
    print(f"  COLLECTION COMPLETE: {len(all_raw_configs)} raw configs")
    print(f"{'='*70}\n")
    
    if not all_raw_configs:
        print("⚠️ No configs collected. Exiting.")
        return
    
    # Pre-filter
    live_configs = pre_filter_live_hosts(list(all_raw_configs))
    
    if not live_configs:
        print("⚠️ No live configs after filtering.")
        return
    
    # Process configs
    processed = process_configs(live_configs)
    configs_in_order = [item['config'] for item in processed]
    
    # === DATABASE PROCESSING ===
    print(f"\n{'='*70}")
    print(f"  DATABASE PROCESSING")
    print(f"{'='*70}")
    
    db_all = load_all_databases()
    print(f"Total historical configs across all databases: {len(db_all)}")
    
    new_configs = [c for c in configs_in_order if c not in db_all]
    print(f"Found {len(new_configs)} NEW configs")
    
    if new_configs:
        save_database(new_configs)
        
        existing_active = load_active_file()
        merged_active = merge_configs_by_fingerprint(existing_active, new_configs)
        saved_count = save_active_file(merged_active)
        print(f"  ✅ Saved {saved_count} to {ACTIVE_FILE}")
    else:
        print("  ℹ️  No new configs this run")
    
    # === CATEGORIZATION ===
    print(f"\n{'='*70}")
    print(f"  CATEGORIZATION")
    print(f"{'='*70}")
    
    by_protocol, by_network, by_security, by_country = {}, {}, {}, {}
    
    for item in processed:
        config, attrs = item['config'], item['attrs']
        by_protocol.setdefault(attrs['protocol'], []).append(config)
        by_network.setdefault(attrs['network'], []).append(config)
        by_security.setdefault(attrs['security'], []).append(config)
        by_country.setdefault(attrs['country'].lower(), []).append(config)
    
    print("  Writing categorized files...")
    
    for proto, cfgs in by_protocol.items():
        write_chunked_subscription_files(f'./protocols/{sanitize_filename(proto)}', cfgs)
    
    for net, cfgs in by_network.items():
        write_chunked_subscription_files(f'./networks/{sanitize_filename(net)}', cfgs)
    
    for sec, cfgs in by_security.items():
        write_chunked_subscription_files(f'./security/{sanitize_filename(sec)}', cfgs)
    
    for country, cfgs in by_country.items():
        write_chunked_subscription_files(f'./countries/{sanitize_filename(country)}', cfgs)
    
    write_chunked_subscription_files('./splitted/mixed', configs_in_order)
    
    # Final summary
    print(f"\n{'='*70}")
    print(f"  FINAL SUMMARY")
    print(f"{'='*70}")
    print(f"  Raw collected        : {len(all_raw_configs)}")
    print(f"  Live filtered        : {len(live_configs)}")
    print(f"  Processed            : {len(processed)}")
    print(f"  New configs          : {len(new_configs)}")
    print(f"  Database files       : {len(get_database_files())}")
    print(f"  Active configs       : {len(load_active_file())}")
    print(f"  Protocol groups      : {len(by_protocol)}")
    print(f"  Network groups       : {len(by_network)}")
    print(f"  Security groups      : {len(by_security)}")
    print(f"  Country groups       : {len(by_country)}")
    print(f"{'='*70}")
    print("\n✓ COLLECTION COMPLETE!")


if __name__ == "__main__":
    print("DEBUG: Script starting")
    try:
        main()
        print("DEBUG: main() completed successfully")
    except Exception as e:
        print(f"\n--- FATAL ERROR ---")
        print(f"Error type: {type(e).__name__}")
        print(f"Error message: {e}")
        traceback.print_exc()
        exit(1)
    print("DEBUG: Script ending normally")
