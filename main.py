import os
import asyncio
import json
import re
import base64
import logging
import random
import string
import math
import socket
import time
from pathlib import Path
from typing import List, Dict, Set, Optional, Any, Tuple, Union
from urllib.parse import urlparse, parse_qs, unquote
import ipaddress
from collections import Counter, defaultdict
from datetime import datetime, timezone, timedelta

# Third-party libraries
import httpx
import aiofiles
import jdatetime

try:
    import geoip2.database
    import geoip2.errors
except ImportError:
    print("Error: 'geoip2' library not found. Please run: pip install geoip2")
    exit(1)

try:
    from rich.console import Console
    from rich.progress import Progress, BarColumn, TextColumn, TimeRemainingColumn, SpinnerColumn, MofNCompleteColumn
    from rich.table import Table
    from rich.panel import Panel
    from rich.logging import RichHandler
    from rich.layout import Layout
    from rich.live import Live
    from rich.align import Align
    from rich.text import Text
except ImportError:
    print("Error: 'rich' library not found. Please run: pip install rich")
    exit(1)

from bs4 import BeautifulSoup
from pydantic import BaseModel, Field, model_validator, ValidationError

# ==============================================================================
# EXCEPTIONS
# ==============================================================================

class V2RayCollectorException(Exception): pass
class ParsingError(V2RayCollectorException): pass
class NetworkError(V2RayCollectorException): pass

# ==============================================================================
# CONFIGURATION & CONSTANTS
# ==============================================================================

class AppConfig:
    """Application Configuration and Path Management"""
    BASE_DIR = Path(__file__).parent
    DATA_DIR = BASE_DIR / "data"
    OUTPUT_DIR = BASE_DIR / "sub"

    # Directory Structure
    DIRS = {
        "security": OUTPUT_DIR / "security",
        "protocols": OUTPUT_DIR / "protocols",
        "networks": OUTPUT_DIR / "networks",
        "subscribe": OUTPUT_DIR / "subscribe",
        "countries": OUTPUT_DIR / "countries",
        "clash": OUTPUT_DIR / "clash",
        "singbox": OUTPUT_DIR / "singbox",
        "html": OUTPUT_DIR / "html",
    }

    # Files
    TELEGRAM_CHANNELS_FILE = DATA_DIR / "telegram_channels.json"
    SUBSCRIPTION_LINKS_FILE = DATA_DIR / "subscription_links.json"
    LAST_UPDATE_FILE = DATA_DIR / "last_update.log"
    SEEN_CONFIGS_FILE = DATA_DIR / "seen_configs.json"
    TELEGRAM_REPORT_FILE = DATA_DIR / "telegram_report.log"
    GEOIP_DB_FILE = DATA_DIR / "GeoLite2-Country.mmdb"
    GEOIP_ASN_DB_FILE = DATA_DIR / "GeoLite2-ASN.mmdb"

    # Remote Resources
    REMOTE_SUBS_URL = "https://raw.githubusercontent.com/fitexgit/fitex/refs/heads/main/data/subscription_links.json"
    GEOIP_DB_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
    GEOIP_ASN_DB_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-ASN.mmdb"

    # Networking Settings
    HTTP_TIMEOUT = 30.0
    HTTP_MAX_REDIRECTS = 10
    HTTP_HEADERS = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:120.0) Gecko/20100101 Firefox/120.0",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
    }
    MAX_CONCURRENT_REQUESTS = 50
    DNS_CACHE_TTL = 300  # seconds

    # Telegram Scraping Settings
    TELEGRAM_BASE_URL = "https://t.me/s/{}"
    TELEGRAM_MESSAGE_LIMIT = 75
    TELEGRAM_IGNORE_LAST_UPDATE = True
    MAX_CONFIGS_PER_CHANNEL = 500

    # Collector Settings
    ENABLE_SUBSCRIPTION_FETCHING = True
    ENABLE_IP_DEDUPLICATION = True
    ENABLE_SEEN_CONFIG_FILTER = False
    SEEN_CONFIG_TIMEOUT_HOURS = 24
    
    # Connectivity Test Settings
    ENABLE_CONNECTIVITY_TEST = False 
    CONNECTIVITY_TEST_TIMEOUT = 2.5
    MAX_CONNECTIVITY_TESTS = 2500
    TEST_RETRIES = 1

    # Output Signatures
    ADD_SIGNATURES = True
    ADV_SIGNATURE = "✨ Fast & Secure Proxy | @FitexGit"
    DNT_SIGNATURE = "🔰 Anti-Censorship | Filter Breaker"
    DEV_SIGNATURE = "⚡ Powered by FitexGit | GitHub"
    CUSTOM_SIGNATURE = "🌐 Source: github.com/fitexgit"

CONFIG = AppConfig()
console = Console()

# ==============================================================================
# UTILS & HELPERS
# ==============================================================================

def setup_logger():
    logging.basicConfig(
        level=logging.INFO,
        format="%(message)s",
        datefmt="[%X]",
        handlers=[RichHandler(console=console, rich_tracebacks=True, show_path=False)]
    )
    # Suppress noisy loggers
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)
    logging.getLogger("geoip2").setLevel(logging.WARNING)
    return logging.getLogger("FitexCollector")

logger = setup_logger()

COUNTRY_CODE_TO_FLAG = {
    'AD': '🇦🇩', 'AE': '🇦🇪', 'AF': '🇦🇫', 'AG': '🇦🇬', 'AI': '🇦🇮', 'AL': '🇦🇱', 'AM': '🇦🇲', 'AO': '🇦🇴', 'AQ': '🇦🇶', 'AR': '🇦🇷', 'AS': '🇦🇸', 'AT': '🇦🇹', 'AU': '🇦🇺', 'AW': '🇦🇼', 'AX': '🇦🇽', 'AZ': '🇦🇿', 'BA': '🇧🇦', 'BB': '🇧🇧',
    'BD': '🇧🇩', 'BE': '🇧🇪', 'BF': '🇧🇫', 'BG': '🇧🇬', 'BH': '🇧🇭', 'BI': '🇧🇮', 'BJ': '🇧🇯', 'BL': '🇧🇱', 'BM': '🇧🇲', 'BN': '🇧🇳', 'BO': '🇧🇴', 'BR': '🇧🇷', 'BS': '🇧🇸', 'BT': '🇧🇹', 'BW': '🇧🇼', 'BY': '🇧🇾', 'BZ': '🇧🇿', 'CA': '🇨🇦',
    'CC': '🇨🇨', 'CD': '🇨🇩', 'CF': '🇨🇫', 'CG': '🇨🇬', 'CH': '🇨🇭', 'CI': '🇨🇮', 'CK': '🇨🇰', 'CL': '🇨🇱', 'CM': '🇨🇲', 'CN': '🇨🇳', 'CO': '🇨🇴', 'CR': '🇨🇷', 'CU': '🇨🇺', 'CV': '🇨🇻', 'CW': '🇨🇼', 'CX': '🇨🇽', 'CY': '🇨🇾', 'CZ': '🇨🇿',
    'DE': '🇩🇪', 'DJ': '🇩🇯', 'DK': '🇩🇰', 'DM': '🇩🇲', 'DO': '🇩🇴', 'DZ': '🇩🇿', 'EC': '🇪🇨', 'EE': '🇪🇪', 'EG': '🇪🇬', 'ER': '🇪🇷', 'ES': '🇪🇸', 'ET': '🇪🇹', 'FI': '🇫🇮', 'FJ': '🇫🇯', 'FK': '🇫🇰', 'FM': '🇫🇲', 'FO': '🇫🇴', 'FR': '🇫🇷',
    'GA': '🇬🇦', 'GB': '🇬🇧', 'GD': '🇬🇩', 'GE': '🇬🇪', 'GF': '🇬🇫', 'GG': '🇬🇬', 'GH': '🇬🇭', 'GI': '🇬🇮', 'GL': '🇬🇱', 'GM': '🇬🇲', 'GN': '🇬🇳', 'GP': '🇬🇵', 'GQ': '🇬🇶', 'GR': '🇬🇷', 'GS': '🇬🇸', 'GT': '🇬🇹', 'GU': '🇬🇺', 'GW': '🇬🇼',
    'GY': '🇬🇾', 'HK': '🇭🇰', 'HN': '🇭🇳', 'HR': '🇭🇷', 'HT': '🇭🇹', 'HU': '🇭🇺', 'ID': '🇮🇩', 'IE': '🇮🇪', 'IL': '🇮🇱', 'IM': '🇮🇲', 'IN': '🇮🇳', 'IO': '🇮🇴', 'IQ': '🇮🇶', 'IR': '🇮🇷', 'IS': '🇮🇸', 'IT': '🇮🇹', 'JE': '🇯🇪', 'JM': '🇯🇲',
    'JO': '🇯🇴', 'JP': '🇯🇵', 'KE': '🇰🇪', 'KG': '🇰🇬', 'KH': '🇰🇭', 'KI': '🇰🇮', 'KM': '🇰🇲', 'KN': '🇰🇳', 'KP': '🇰🇵', 'KR': '🇰🇷', 'KW': '🇰🇼', 'KY': '🇰🇾', 'KZ': '🇰🇿', 'LA': '🇱🇦', 'LB': '🇱🇧', 'LC': '🇱🇨', 'LI': '🇱🇮', 'LK': '🇱🇰',
    'LR': '🇱🇷', 'LS': '🇱🇸', 'LT': '🇱🇹', 'LU': '🇱🇺', 'LV': '🇱🇻', 'LY': '🇱🇾', 'MA': '🇲🇦', 'MC': '🇲🇨', 'MD': '🇲🇩', 'ME': '🇲🇪', 'MF': '🇲🇫', 'MG': '🇲🇬', 'MH': '🇲🇭', 'MK': '🇲🇰', 'ML': '🇲🇱', 'MM': '🇲🇲', 'MN': '🇲🇳', 'MO': '🇲🇴',
    'MP': '🇲🇵', 'MQ': '🇲🇶', 'MR': '🇲🇷', 'MS': '🇲🇸', 'MT': '🇲🇹', 'MU': '🇲🇺', 'MV': '🇲🇻', 'MW': '🇲🇼', 'MX': '🇲🇽', 'MY': '🇲🇾', 'MZ': '🇲🇿', 'NA': '🇳🇦', 'NC': '🇳🇨', 'NE': '🇳🇪', 'NF': '🇳🇫', 'NG': '🇳🇬', 'NI': '🇳🇮', 'NL': '🇳🇱',
    'NO': '🇳🇴', 'NP': '🇳🇵', 'NR': '🇳🇷', 'NU': '🇳🇺', 'NZ': '🇳🇿', 'OM': '🇴🇲', 'PA': '🇵🇦', 'PE': '🇵🇪', 'PF': '🇵🇫', 'PG': '🇵🇬', 'PH': '🇵🇭', 'PK': '🇵🇰', 'PL': '🇵🇱', 'PM': '🇵🇲', 'PN': '🇵🇳', 'PR': '🇵🇷', 'PS': '🇵🇸', 'PT': '🇵🇹',
    'PW': '🇵🇼', 'PY': '🇵🇾', 'QA': '🇶🇦', 'RE': '🇷🇪', 'RO': '🇷🇴', 'RS': '🇷🇸', 'RU': '🇷🇺', 'RW': '🇷🇼', 'SA': '🇸🇦', 'SB': '🇸🇧', 'SC': '🇸🇨', 'SD': '🇸🇩', 'SE': '🇸🇪', 'SG': '🇸🇬', 'SH': '🇸🇭', 'SI': '🇸🇮', 'SJ': '🇸🇯', 'SK': '🇸🇰',
    'SL': '🇸🇱', 'SM': '🇸🇲', 'SN': '🇸🇳', 'SO': '🇸🇴', 'SR': '🇸🇷', 'SS': '🇸🇸', 'ST': '🇸🇹', 'SV': '🇸🇻', 'SX': '🇸🇽', 'SY': '🇸🇾', 'SZ': '🇸🇿', 'TC': '🇹🇨', 'TD': '🇹🇩', 'TF': '🇹🇫', 'TG': '🇹🇬', 'TH': '🇹🇭', 'TJ': '🇹🇯', 'TK': '🇹🇰',
    'TL': '🇹🇱', 'TM': '🇹🇲', 'TN': '🇹🇳', 'TO': '🇹🇴', 'TR': '🇹🇷', 'TT': '🇹🇹', 'TV': '🇹🇻', 'TW': '🇹🇼', 'TZ': '🇹🇿', 'UA': '🇺🇦', 'UG': '🇺🇬', 'US': '🇺🇸', 'UY': '🇺🇾', 'UZ': '🇺🇿', 'VA': '🇻🇦', 'VC': '🇻🇨', 'VE': '🇻🇪', 'VG': '🇻🇬',
    'VI': '🇻🇮', 'VN': '🇻🇳', 'VU': '🇻🇺', 'WF': '🇼🇫', 'WS': '🇼🇸', 'YE': '🇾🇪', 'YT': '🇾🇹', 'ZA': '🇿🇦', 'ZM': '🇿🇲', 'ZW': '🇿🇼', 'XX': '🏳️'
}

def b64_decode(s: str) -> str:
    s = s.strip()
    s += '=' * (-len(s) % 4)
    try:
        return base64.urlsafe_b64decode(s).decode('utf-8')
    except Exception:
        return ""

def b64_encode(s: str) -> str:
    return base64.urlsafe_b64encode(s.encode('utf-8')).rstrip(b'=').decode('utf-8')

def is_valid_base64(s: str) -> bool:
    try:
        s_padded = s + '=' * (-len(s) % 4)
        base64.b64decode(s_padded, validate=True)
        return True
    except Exception:
        return False

def get_iran_timezone():
    return timezone(timedelta(hours=3, minutes=30))

def generate_random_uuid_string() -> str:
    return '-'.join([''.join(random.choices(string.ascii_lowercase + string.digits, k=k)) for k in [8, 4, 4, 4, 12]])

def is_ip_address(address: str) -> bool:
    try:
        ipaddress.ip_address(address)
        return True
    except ValueError:
        return False

def clean_remarks(name: str) -> str:
    """Removes emojis and special chars to keep remarks clean"""
    # Keep only alphanumeric, common punctuation, and spaces
    cleaned = re.sub(r'[^\w\s\-\.\:\@\(\)\[\]]', '', name)
    cleaned = re.sub(r'\s+', ' ', cleaned).strip()
    return cleaned if cleaned else "Config"

# ==============================================================================
# DATA MODELS
# ==============================================================================

class BaseConfig(BaseModel):
    model_config = {'str_strip_whitespace': True}
    protocol: str
    host: str
    port: int
    uuid: str
    remarks: str = "N/A"
    network: str = 'tcp'
    security: str = 'none'
    path: Optional[str] = None
    sni: Optional[str] = None
    fingerprint: Optional[str] = None
    country: Optional[str] = Field("XX", exclude=True)
    source_type: str = Field("unknown", exclude=True)
    ping: Optional[int] = Field(None, exclude=True)
    asn_org: Optional[str] = Field(None, exclude=True)
    ip_address: Optional[str] = Field(None, exclude=True)

    def get_deduplication_key(self) -> str:
        return f"{self.protocol}:{self.host}:{self.port}:{self.uuid}"

    def to_uri(self) -> str:
        raise NotImplementedError

class VmessConfig(BaseConfig):
    protocol: str = 'vmess'
    source_type: str = 'vmess'
    ps: str
    add: str
    v: Any = "2"
    aid: int = 0
    scy: str = 'auto'
    net: str
    type: str = 'none'
    tls: str = ''

    @model_validator(mode='before')
    def map_fields(cls, values):
        values['remarks'] = values.get('ps', 'N/A')
        values['host'] = values.get('add', '')
        values['uuid'] = values.get('id', '')
        values['network'] = values.get('net', 'tcp')
        values['security'] = values.get('tls') or 'none'
        values['v'] = str(values.get('v', '2'))
        return values

    def to_uri(self) -> str:
        vmess_data = {"v": self.v, "ps": self.remarks, "add": self.host, "port": self.port, "id": self.uuid, "aid": self.aid, "scy": self.scy, "net": self.network, "type": self.type, "host": self.sni, "path": self.path, "tls": self.security if self.security != 'none' else '', "sni": self.sni}
        vmess_data_clean = {k: v for k, v in vmess_data.items() if v is not None and v != ""}
        json_str = json.dumps(vmess_data_clean, separators=(',', ':'))
        encoded = base64.b64encode(json_str.encode('utf-8')).decode('utf-8').rstrip("=")
        return f"vmess://{encoded}"

class VlessConfig(BaseConfig):
    protocol: str = 'vless'
    flow: Optional[str] = None
    pbk: Optional[str] = None
    sid: Optional[str] = None

    def to_uri(self) -> str:
        params = {'type': self.network, 'security': self.security, 'path': self.path, 'sni': self.sni, 'fp': self.fingerprint, 'flow': self.flow, 'pbk': self.pbk, 'sid': self.sid}
        query_string = '&'.join([f"{k}={v}" for k, v in params.items() if v is not None and v != ""])
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"vless://{self.uuid}@{self.host}:{self.port}?{query_string}{remarks_encoded}"

class ShadowsocksConfig(BaseConfig):
    protocol: str = 'shadowsocks'
    source_type: str = 'shadowsocks'
    method: str

    @model_validator(mode='before')
    def map_fields(cls, values):
        values['uuid'] = values.get('password', '')
        return values

    def to_uri(self) -> str:
        user_info = f"{self.method}:{self.uuid}"
        encoded_user_info = base64.b64encode(user_info.encode('utf-8')).decode('utf-8').rstrip('=')
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"ss://{encoded_user_info}@{self.host}:{self.port}{remarks_encoded}"

class Hysteria2Config(BaseConfig):
    protocol: str = 'hysteria2'
    insecure: Optional[int] = None
    obfs: Optional[str] = None
    obfs_password: Optional[str] = Field(None, alias='obfs-password')

    def to_uri(self) -> str:
        params = {'sni': self.sni, 'insecure': self.insecure, 'obfs': self.obfs, 'obfs-password': self.obfs_password}
        query_string = '&'.join([f"{k}={v}" for k, v in params.items() if v is not None])
        remarks_encoded = f"#{unquote(self.remarks)}"
        return f"hysteria2://{self.uuid}@{self.host}:{self.port}?{query_string}{remarks_encoded}"

# ==============================================================================
# NETWORK & PARSING
# ==============================================================================

class AsyncHttpClient:
    _client: Optional[httpx.AsyncClient] = None

    @classmethod
    async def get_client(cls) -> httpx.AsyncClient:
        if cls._client is None or cls._client.is_closed:
            limits = httpx.Limits(max_connections=CONFIG.MAX_CONCURRENT_REQUESTS, max_keepalive_connections=20)
            cls._client = httpx.AsyncClient(
                headers=CONFIG.HTTP_HEADERS,
                timeout=CONFIG.HTTP_TIMEOUT,
                max_redirects=CONFIG.HTTP_MAX_REDIRECTS,
                http2=True,
                follow_redirects=True,
                limits=limits,
                verify=False # Often necessary for some iran-hosted links
            )
        return cls._client

    @classmethod
    async def close(cls):
        if cls._client and not cls._client.is_closed:
            await cls._client.aclose()
            cls._client = None

    @classmethod
    async def get(cls, url: str) -> Tuple[int, str]:
        client = await cls.get_client()
        try:
            response = await client.get(url)
            response.raise_for_status()
            return response.status_code, response.text
        except httpx.RequestError as e:
            return 0, ""
        except httpx.HTTPStatusError as e:
            return e.response.status_code, ""
        except Exception:
            return 0, ""

class V2RayParser:
    @staticmethod
    def parse(uri: str, source_type: str = "unknown") -> Optional[BaseConfig]:
        uri = uri.strip()
        if not uri: return None
        
        # Basic cleanup
        if "..." in uri or len(uri) < 10: return None

        try:
            if uri.startswith("vmess://"): return V2RayParser._parse_vmess(uri)
            elif uri.startswith("vless://"): return V2RayParser._parse_vless(uri)
            elif uri.startswith("ss://"): return V2RayParser._parse_shadowsocks(uri)
            elif uri.startswith("hy2://") or uri.startswith("hysteria2://"): return V2RayParser._parse_hysteria2(uri)
        except (ValidationError, ParsingError, Exception):
            pass
        return None

    @staticmethod
    def _parse_vmess(uri: str) -> Optional[VmessConfig]:
        b64_data = uri[len("vmess://"):]
        if not is_valid_base64(b64_data): return None
        try:
            data = json.loads(b64_decode(b64_data))
            return VmessConfig(**data)
        except Exception: return None

    @staticmethod
    def _parse_vless(uri: str) -> Optional[VlessConfig]:
        parsed_url = urlparse(uri)
        if not parsed_url.hostname or not parsed_url.port: return None
        params = parse_qs(parsed_url.query)
        return VlessConfig(
            uuid=parsed_url.username, 
            host=parsed_url.hostname, 
            port=parsed_url.port, 
            remarks=unquote(parsed_url.fragment) if parsed_url.fragment else f"{parsed_url.hostname}:{parsed_url.port}",
            network=params.get('type', ['tcp'])[0], 
            security=params.get('security', ['none'])[0], 
            path=unquote(params.get('path', [None])[0]) if params.get('path') else None, 
            sni=params.get('sni', [None])[0], 
            fingerprint=params.get('fp', [None])[0], 
            flow=params.get('flow', [None])[0], 
            pbk=params.get('pbk', [None])[0], 
            sid=params.get('sid', [None])[0]
        )

    @staticmethod
    def _parse_shadowsocks(uri: str) -> Optional[ShadowsocksConfig]:
        main_part, remarks_part = (uri[len("ss://"):].split('#', 1) + [''])[:2]
        if '@' not in main_part: return None
        user_info_part, host_port_part = main_part.split('@', 1)
        decoded_user_info = b64_decode(user_info_part)
        if ':' not in decoded_user_info or ':' not in host_port_part: return None
        method, password = decoded_user_info.split(':', 1)
        host, port_str = host_port_part.rsplit(':', 1)
        
        # Check for malformed ports
        try:
            cleaned_host = host.strip("[]")
            # Remove any trailing non-digits from port string if possible, or just fail
            port = int(port_str)
            return ShadowsocksConfig(host=cleaned_host, port=port, remarks=unquote(remarks_part), method=method, password=password)
        except ValueError:
            return None
            
    @staticmethod
    def _parse_hysteria2(uri: str) -> Optional[Hysteria2Config]:
        uri = uri.replace("hy2://", "hysteria2://")
        parsed_url = urlparse(uri)
        if not parsed_url.hostname or not parsed_url.port: return None
        params = parse_qs(parsed_url.query)
        return Hysteria2Config(
            uuid=parsed_url.username or '',
            host=parsed_url.hostname,
            port=parsed_url.port,
            remarks=unquote(parsed_url.fragment),
            sni=params.get('sni', [None])[0],
            insecure=int(params.get('insecure', [0])[0]),
            obfs=params.get('obfs', [None])[0],
            obfs_password=params.get('obfs-password', [None])[0],
        )

class RawConfigCollector:
    PATTERNS = {
        "ss": r"(ss://[^\s<>#]+)", 
        "vmess": r"(vmess://[^\s<>#]+)", 
        "vless": r"(vless://(?:(?!=reality)[^\s<>#])+(?=[\s<>#]))", 
        "reality": r"(vless://[^\s<>#]+?security=reality[^\s<>#]*)",
        "hysteria2": r"((?:hy2|hysteria2)://[^\s<>#]+)",
    }

    @classmethod
    def find_all(cls, text_content: str) -> Dict[str, List[str]]:
        all_matches = {}
        for name, pattern in cls.PATTERNS.items():
            full_pattern = r"(?<![\w-])" + pattern
            matches = re.findall(full_pattern, text_content, re.IGNORECASE)
            cleaned_matches = [re.sub(r"#[^#]*$", "", m) for m in matches if "…" not in m]
            if cleaned_matches:
                all_matches[name] = cleaned_matches
        return all_matches

# ==============================================================================
# FETCHING LOGIC
# ==============================================================================

class TelegramScraper:
    def __init__(self, channels: List[str], since_datetime: datetime):
        self.channels, self.since_datetime = channels, since_datetime
        self.configs_by_channel: Dict[str, List[str]] = {}
        self.successful_channels: List[Tuple[str, int]] = []
        self.failed_channels: List[str] = []

    async def scrape_all(self):
        with Progress(
            SpinnerColumn(),
            TextColumn("[bold blue]Telegram Scraping..."),
            BarColumn(),
            MofNCompleteColumn(),
            TimeRemainingColumn(),
            console=console
        ) as progress:
            task = progress.add_task("Channels", total=len(self.channels))
            
            batch_size = 15
            for i in range(0, len(self.channels), batch_size):
                batch = self.channels[i:i + batch_size]
                tasks = [self._scrape_channel_with_retry(ch) for ch in batch]
                results = await asyncio.gather(*tasks)

                for j, res in enumerate(results):
                    channel = batch[j]
                    if res:
                        count = sum(len(v) for v in res.values())
                        if count > 0:
                            self.successful_channels.append((channel, count))
                            self.configs_by_channel[channel] = [c for sub in res.values() for c in sub]
                    else:
                        self.failed_channels.append(channel)
                    progress.update(task, advance=1)
                
                await asyncio.sleep(1)

        self._write_report()

    def _write_report(self):
        now = datetime.now(get_iran_timezone())
        report = f"REPORT DATE: {now.strftime('%Y-%m-%d %H:%M:%S')}\n"
        report += f"Total: {len(self.channels)} | Success: {len(self.successful_channels)} | Failed: {len(self.failed_channels)}\n\n"
        for ch, cnt in self.successful_channels: report += f"{ch}: {cnt}\n"
        with open(CONFIG.TELEGRAM_REPORT_FILE, "w", encoding="utf-8") as f: f.write(report)

    async def _scrape_channel_with_retry(self, channel: str) -> Optional[Dict[str, List[str]]]:
        for _ in range(2):
            url = CONFIG.TELEGRAM_BASE_URL.format(channel)
            status, html = await AsyncHttpClient.get(url)
            if status == 200 and html:
                try:
                    soup = BeautifulSoup(html, "html.parser")
                    messages = soup.find_all("div", class_="tgme_widget_message", limit=CONFIG.TELEGRAM_MESSAGE_LIMIT)
                    if not messages: return {}
                    
                    configs = defaultdict(list)
                    count = 0
                    for msg in messages:
                        text_div = msg.find("div", class_="tgme_widget_message_text")
                        if text_div:
                            found = RawConfigCollector.find_all(text_div.get_text('\n', strip=True))
                            for k, v in found.items():
                                configs[k].extend(v)
                                count += len(v)
                        if count >= CONFIG.MAX_CONFIGS_PER_CHANNEL: break
                    return configs
                except Exception: pass
            await asyncio.sleep(2)
        return None

class SubscriptionFetcher:
    def __init__(self, sub_links: List[str]):
        self.sub_links = sub_links
        self.total_configs_by_type: Dict[str, List[str]] = defaultdict(list)

    async def fetch_all(self):
        with Progress(
            SpinnerColumn(),
            TextColumn("[bold cyan]Fetching Subs..."),
            BarColumn(),
            MofNCompleteColumn(),
            console=console
        ) as progress:
            task = progress.add_task("Fetching", total=len(self.sub_links))
            tasks = [self._fetch_link(link) for link in self.sub_links]
            
            for coro in asyncio.as_completed(tasks):
                content = await coro
                if content:
                    found = RawConfigCollector.find_all(content)
                    for k, v in found.items():
                        self.total_configs_by_type[k].extend(v)
                progress.update(task, advance=1)

    async def _fetch_link(self, link: str) -> str:
        try:
            _, content = await AsyncHttpClient.get(link)
            if not content: return ""
            # Try decoding base64 if it looks like one
            if "://" not in content[:50] and len(content) > 20:
                try: return b64_decode(content)
                except: pass
            return content
        except: return ""

# ==============================================================================
# PROCESSING, GEOIP & TESTING
# ==============================================================================

class DNSResolver:
    _cache: Dict[str, str] = {}
    _lock = asyncio.Lock()

    @classmethod
    async def resolve(cls, host: str) -> Optional[str]:
        if is_ip_address(host): return host
        async with cls._lock:
            if host in cls._cache: return cls._cache[host]
        
        try:
            info = await asyncio.get_event_loop().getaddrinfo(host, None, family=socket.AF_INET)
            ip = info[0][4][0]
            async with cls._lock: cls._cache[host] = ip
            return ip
        except: return None

class Geolocation:
    _country_reader: Optional[geoip2.database.Reader] = None
    _asn_reader: Optional[geoip2.database.Reader] = None

    @classmethod
    def initialize(cls):
        if CONFIG.GEOIP_DB_FILE.exists():
            try: cls._country_reader = geoip2.database.Reader(str(CONFIG.GEOIP_DB_FILE))
            except: pass
        if CONFIG.GEOIP_ASN_DB_FILE.exists():
            try: cls._asn_reader = geoip2.database.Reader(str(CONFIG.GEOIP_ASN_DB_FILE))
            except: pass

    @classmethod
    def get_info(cls, ip: str) -> Tuple[str, Optional[str]]:
        country, asn = "XX", None
        if not cls._country_reader or not ip: return country, asn
        try:
            res = cls._country_reader.country(ip)
            country = res.country.iso_code or "XX"
        except: pass
        
        if cls._asn_reader:
            try:
                res = cls._asn_reader.asn(ip)
                asn = res.autonomous_system_organization
            except: pass
        return country, asn

    @classmethod
    def close(cls):
        if cls._country_reader: cls._country_reader.close()
        if cls._asn_reader: cls._asn_reader.close()

class ConfigProcessor:
    def __init__(self, raw_configs: Dict[str, List[str]]):
        self.raw_configs = raw_configs
        self.parsed_configs: List[BaseConfig] = []
        self.unique_configs: Dict[str, BaseConfig] = {}

    async def process(self):
        console.log("[cyan]Parsing configurations...[/cyan]")
        for proto, links in self.raw_configs.items():
            for link in links:
                obj = V2RayParser.parse(link, proto)
                if obj: self.parsed_configs.append(obj)
        
        # Deduplicate by UUID/Host/Port
        for c in self.parsed_configs:
            self.unique_configs[c.get_deduplication_key()] = c
        
        console.log(f"[green]Unique configs after parsing: {len(self.unique_configs)}[/green]")
        
        # Optimize: Sample FIRST only if testing is enabled to avoid bottleneck
        if CONFIG.ENABLE_CONNECTIVITY_TEST and len(self.unique_configs) > CONFIG.MAX_CONNECTIVITY_TESTS:
            console.log(f"[yellow]Sampling {CONFIG.MAX_CONNECTIVITY_TESTS} configs from {len(self.unique_configs)}...[/yellow]")
            sampled_keys = random.sample(list(self.unique_configs.keys()), CONFIG.MAX_CONNECTIVITY_TESTS)
            self.unique_configs = {k: self.unique_configs[k] for k in sampled_keys}

        await self._enrich_data()
        if CONFIG.ENABLE_CONNECTIVITY_TEST:
            await self._test_connectivity()
        
        self._format_remarks()

    async def _enrich_data(self):
        hosts = {c.host for c in self.unique_configs.values()}
        console.log(f"[cyan]Resolving DNS for {len(hosts)} hosts...[/cyan]")
        
        # Batch resolve
        tasks = [DNSResolver.resolve(h) for h in hosts]
        results = await asyncio.gather(*tasks)
        dns_map = dict(zip(hosts, results))

        for c in self.unique_configs.values():
            c.ip_address = dns_map.get(c.host)
            if c.ip_address:
                c.country, c.asn_org = Geolocation.get_info(c.ip_address)

    async def _test_tcp(self, config: BaseConfig) -> int:
        target = config.ip_address or config.host
        if not target: return 9999
        try:
            start = time.monotonic()
            reader, writer = await asyncio.wait_for(
                asyncio.open_connection(target, config.port), timeout=CONFIG.CONNECTIVITY_TEST_TIMEOUT
            )
            ping = int((time.monotonic() - start) * 1000)
            writer.close()
            await writer.wait_closed()
            return ping
        except: return 9999

    async def _test_connectivity(self):
        configs = list(self.unique_configs.values())
        
        with Progress(
            SpinnerColumn(),
            TextColumn("[bold yellow]Testing Connectivity..."),
            BarColumn(),
            MofNCompleteColumn(),
            console=console
        ) as progress:
            task = progress.add_task("Ping", total=len(configs))
            
            # Increased semaphore for faster processing
            sem = asyncio.Semaphore(100)
            async def _worker(c):
                async with sem:
                    ping = await self._test_tcp(c)
                    if ping < 2000: c.ping = ping
                    progress.update(task, advance=1)
            
            await asyncio.gather(*[_worker(c) for c in configs])
        
        # Remove failed configs
        self.unique_configs = {k: v for k, v in self.unique_configs.items() if v.ping}
        console.log(f"[bold green]Active configs: {len(self.unique_configs)}[/bold green]")

    def _format_remarks(self):
        for c in self.unique_configs.values():
            proto_full_map = {
                'vmess': 'VMESS', 'vless': 'VLESS', 'trojan': 'TROJAN', 
                'shadowsocks': 'SHADOWSOCKS', 'hysteria2': 'HYSTERIA2'
            }
            proto = proto_full_map.get(c.protocol, c.protocol.upper())

            # Determine security label
            if c.source_type == 'reality':
                sec = 'RLT'
            elif c.security == 'tls':
                sec = 'TLS'
            elif c.security == 'xtls':
                sec = 'XTLS'
            elif c.security == 'none' or not c.security:
                sec = 'NTLS'
            else:
                sec = c.security.upper()

            net = (c.network or 'tcp').upper()
            flag = COUNTRY_CODE_TO_FLAG.get(c.country, "🏳️")
            ip_str = c.ip_address if c.ip_address else "N/A"
            asn_str = f" - {c.asn_org}" if c.asn_org else ""
            
            # Restore Old Format: "DE 🇩🇪 ┇ VLESS-TCP-TLS - Hetzner ┇ 1.2.3.4"
            c.remarks = f"{c.country} {flag} ┇ {proto}-{net}-{sec}{asn_str} ┇ {ip_str}"

    def get_results(self) -> List[BaseConfig]:
        configs = list(self.unique_configs.values())
        random.shuffle(configs)
        
        if CONFIG.ENABLE_CONNECTIVITY_TEST:
            return sorted(configs, key=lambda x: x.ping if x.ping is not None else 999999)
        
        return configs

# ==============================================================================
# OUTPUT GENERATORS (CLASH, SINGBOX, HTML)
# ==============================================================================

class ConfigConverter:
    """Handles conversion to Clash Meta and Sing-box formats"""
    
    @staticmethod
    def to_clash_yaml(configs: List[BaseConfig]) -> str:
        # Simple template-based generation to avoid heavy yaml dependencies
        proxies = []
        for c in configs:
            if isinstance(c, VmessConfig):
                proxies.append(f"""  - name: "{c.remarks}"
    type: vmess
    server: {c.host}
    port: {c.port}
    uuid: {c.uuid}
    alterId: {c.aid}
    cipher: auto
    tls: {str(c.security == 'tls').lower()}
    skip-cert-verify: true
    network: {c.network}
    servername: {c.sni or ''}
    ws-opts:
      path: {c.path or '/'}
""")
            elif isinstance(c, VlessConfig):
                proxies.append(f"""  - name: "{c.remarks}"
    type: vless
    server: {c.host}
    port: {c.port}
    uuid: {c.uuid}
    tls: {str(c.security == 'tls').lower()}
    network: {c.network}
    servername: {c.sni or ''}
    client-fingerprint: {c.fingerprint or 'chrome'}
    skip-cert-verify: true
    ws-opts:
      path: {c.path or '/'}
""")
        
        yaml_content = "proxies:\n" + "".join(proxies)
        return yaml_content

    @staticmethod
    def to_singbox_json(configs: List[BaseConfig]) -> str:
        outboards = []
        for c in configs:
            base = {
                "tag": c.remarks,
                "server": c.host,
                "server_port": c.port,
                "tls": {"enabled": c.security in ['tls', 'reality'], "insecure": True, "server_name": c.sni or c.host},
                "transport": {}
            }
            
            if c.network == 'ws':
                base["transport"] = {"type": "ws", "path": c.path or "/"}
            
            if isinstance(c, VmessConfig):
                base["type"] = "vmess"
                base["uuid"] = c.uuid
                base["security"] = "auto"
                base["alter_id"] = c.aid
                outboards.append(base)
            elif isinstance(c, VlessConfig):
                base["type"] = "vless"
                base["uuid"] = c.uuid
                if c.flow: base["flow"] = c.flow
                outboards.append(base)
                
        return json.dumps({"outbounds": outboards}, indent=2)

class HTMLGenerator:
    @staticmethod
    def generate_dashboard(stats: Dict[str, int], top_countries: List[Tuple[str, int]]) -> str:
        jalali_now = jdatetime.datetime.now().strftime("%Y/%m/%d %H:%M")
        rows = "".join([f"<tr><td>{COUNTRY_CODE_TO_FLAG.get(c, '')} {c}</td><td>{n}</td></tr>" for c, n in top_countries])
        
        return f"""
        <!DOCTYPE html>
        <html lang="fa" dir="rtl">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Fitex Collector Dashboard</title>
            <style>
                body {{ font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; background-color: #1a1a1a; color: #fff; margin: 0; padding: 20px; }}
                .container {{ max-width: 800px; margin: 0 auto; }}
                .card {{ background: #2d2d2d; border-radius: 10px; padding: 20px; margin-bottom: 20px; box-shadow: 0 4px 6px rgba(0,0,0,0.3); }}
                h1 {{ color: #00ff88; text-align: center; }}
                .stat-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr)); gap: 15px; text-align: center; }}
                .stat-item {{ background: #333; padding: 15px; border-radius: 8px; }}
                .stat-value {{ font-size: 24px; font-weight: bold; color: #4facfe; }}
                table {{ width: 100%; border-collapse: collapse; margin-top: 10px; }}
                th, td {{ padding: 10px; text-align: right; border-bottom: 1px solid #444; }}
                th {{ color: #aaa; }}
            </style>
        </head>
        <body>
            <div class="container">
                <div class="card">
                    <h1>⚡ Fitex Collector Status</h1>
                    <p style="text-align:center; color:#888;">آخرین بروزرسانی: {jalali_now}</p>
                </div>
                
                <div class="card">
                    <div class="stat-grid">
                        <div class="stat-item">
                            <div class="stat-value">{stats.get('total', 0)}</div>
                            <div>کل کانفیگ‌ها</div>
                        </div>
                        <div class="stat-item">
                            <div class="stat-value">{stats.get('vmess', 0)}</div>
                            <div>VMess</div>
                        </div>
                        <div class="stat-item">
                            <div class="stat-value">{stats.get('vless', 0)}</div>
                            <div>VLESS</div>
                        </div>
                    </div>
                </div>

                <div class="card">
                    <h3>🌍 کشورهای برتر</h3>
                    <table>
                        <thead><tr><th>کشور</th><th>تعداد</th></tr></thead>
                        <tbody>{rows}</tbody>
                    </table>
                </div>
                
                <div class="card" style="text-align:center; font-size: 12px; color: #666;">
                    Powered by <a href="https://github.com/fitexgit" style="color:#00ff88;text-decoration:none;">FitexGit</a>
                </div>
            </div>
        </body>
        </html>
        """

class FileManager:
    def __init__(self):
        pass

    async def save_text(self, path: Path, content: str):
        path.parent.mkdir(parents=True, exist_ok=True)
        async with aiofiles.open(path, 'w', encoding='utf-8') as f:
            await f.write(content)

    def generate_subscription_content(self, configs: List[BaseConfig]) -> str:
        # Create Persian Date Header
        jalali_now = jdatetime.datetime.now().strftime("%Y/%m/%d %H:%M")
        
        # Header Configs using VLESS
        header_configs = [
            f"vless://{generate_random_uuid_string()}@127.0.0.1:1080?security=tls&type=tcp&encryption=none#{unquote(f'📅 Update: {jalali_now}')}",
            f"vless://{generate_random_uuid_string()}@127.0.0.1:1080?security=tls&type=tcp&encryption=none#{unquote(CONFIG.ADV_SIGNATURE)}",
            f"vless://{generate_random_uuid_string()}@127.0.0.1:1080?security=tls&type=tcp&encryption=none#{unquote(CONFIG.DNT_SIGNATURE)}",
            f"vless://{generate_random_uuid_string()}@127.0.0.1:1080?security=tls&type=tcp&encryption=none#{unquote(CONFIG.DEV_SIGNATURE)}",
            f"vless://{generate_random_uuid_string()}@127.0.0.1:1080?security=tls&type=tcp&encryption=none#{unquote(CONFIG.CUSTOM_SIGNATURE)}"
        ]
        
        body_configs = [c.to_uri() for c in configs]
        full_list = header_configs + body_configs
        return b64_encode("\n".join(full_list))

# ==============================================================================
# MAIN APP FLOW
# ==============================================================================

class V2RayCollectorApp:
    def __init__(self):
        self.file_manager = FileManager()
        self.start_time = datetime.now()

    async def run(self):
        # Console Header
        jalali_date = jdatetime.datetime.now().strftime("%Y/%m/%d")
        console.print(Panel.fit(
            f"[bold green]Fitex V2Ray Collector[/bold green]\n[cyan]Date: {jalali_date}[/cyan]\n[yellow]Version: 8.0.0 Pro[/yellow]", 
            border_style="green"
        ))

        # 1. Prepare Environment
        CONFIG.DATA_DIR.mkdir(exist_ok=True, parents=True)
        await self._download_assets()
        Geolocation.initialize()

        # 2. Fetch Sources
        sub_links = await self._get_subscription_links()
        tg_channels = await self._get_telegram_channels()
        
        # 3. Scrape & Fetch
        tg_scraper = TelegramScraper(tg_channels, datetime.now(timezone.utc) - timedelta(days=1))
        sub_fetcher = SubscriptionFetcher(sub_links)
        
        await tg_scraper.scrape_all()
        if CONFIG.ENABLE_SUBSCRIPTION_FETCHING:
            await sub_fetcher.fetch_all()

        # 4. Merge & Deduplicate
        all_raw = defaultdict(list)
        # Merge Telegram
        for ch_configs in tg_scraper.configs_by_channel.values():
            for c in ch_configs:
                for k, v in RawConfigCollector.find_all(c).items():
                    all_raw[k].extend(v)
        # Merge Subs
        for k, v in sub_fetcher.total_configs_by_type.items():
            all_raw[k].extend(v)

        if not any(all_raw.values()):
            console.log("[red]No configs found! Exiting...[/red]")
            return

        # 5. Process & Test
        processor = ConfigProcessor(all_raw)
        await processor.process()
        final_configs = processor.get_results()

        # 6. Save Results
        await self._save_outputs(final_configs)
        
        # 7. Summary
        self._print_summary(final_configs)
        await AsyncHttpClient.close()
        Geolocation.close()

    async def _download_assets(self):
        """Downloads GeoIP databases if missing"""
        for url, path in [(CONFIG.GEOIP_DB_URL, CONFIG.GEOIP_DB_FILE), (CONFIG.GEOIP_ASN_DB_URL, CONFIG.GEOIP_ASN_DB_FILE)]:
            if not path.exists():
                console.log(f"Downloading {path.name}...")
                try:
                    client = await AsyncHttpClient.get_client()
                    resp = await client.get(url, follow_redirects=True)
                    async with aiofiles.open(path, "wb") as f: await f.write(resp.content)
                except Exception as e: console.log(f"[red]Failed to download {path.name}: {e}[/red]")

    async def _get_subscription_links(self) -> List[str]:
        """Fetches subscription links from remote JSON"""
        console.log(f"Fetching subscription links from remote...")
        status, content = await AsyncHttpClient.get(CONFIG.REMOTE_SUBS_URL)
        if status == 200 and content:
            try:
                # Save local backup
                async with aiofiles.open(CONFIG.SUBSCRIPTION_LINKS_FILE, "w", encoding="utf-8") as f:
                    await f.write(content)
                return json.loads(content)
            except: pass
        
        # Fallback to local file
        if CONFIG.SUBSCRIPTION_LINKS_FILE.exists():
            try:
                async with aiofiles.open(CONFIG.SUBSCRIPTION_LINKS_FILE, "r") as f:
                    return json.loads(await f.read())
            except: pass
        return []

    async def _get_telegram_channels(self) -> List[str]:
        if CONFIG.TELEGRAM_CHANNELS_FILE.exists():
            async with aiofiles.open(CONFIG.TELEGRAM_CHANNELS_FILE, "r") as f:
                return json.loads(await f.read())
        return []

    async def _save_outputs(self, configs: List[BaseConfig]):
        console.log("[cyan]Saving outputs...[/cyan]")
        
        # 1. Base64 Subscription
        b64_content = self.file_manager.generate_subscription_content(configs)
        await self.file_manager.save_text(CONFIG.DIRS["subscribe"] / "base64.txt", b64_content)
        
        # 2. Raw Links
        raw_text = "\n".join([c.to_uri() for c in configs])
        await self.file_manager.save_text(CONFIG.OUTPUT_DIR / "all_configs.txt", raw_text)
        
        # 3. Clash Meta
        clash_yaml = ConfigConverter.to_clash_yaml(configs)
        await self.file_manager.save_text(CONFIG.DIRS["clash"] / "meta.yaml", clash_yaml)
        
        # 4. Sing-box
        singbox_json = ConfigConverter.to_singbox_json(configs)
        await self.file_manager.save_text(CONFIG.DIRS["singbox"] / "config.json", singbox_json)
        
        # 5. Categorized
        categories = defaultdict(list)
        for c in configs:
            categories[c.protocol].append(c)
            categories[c.country].append(c)
        
        for cat, items in categories.items():
            if not cat or cat == "XX": continue
            path = CONFIG.DIRS["protocols"] if cat in ['vmess', 'vless', 'trojan', 'shadowsocks'] else CONFIG.DIRS["countries"]
            await self.file_manager.save_text(path / f"{cat}.txt", "\n".join([x.to_uri() for x in items]))

        # 6. HTML Dashboard
        stats = {
            "total": len(configs),
            "vmess": len([c for c in configs if c.protocol == 'vmess']),
            "vless": len([c for c in configs if c.protocol == 'vless'])
        }
        countries = Counter([c.country for c in configs if c.country != 'XX']).most_common(10)
        html = HTMLGenerator.generate_dashboard(stats, countries)
        await self.file_manager.save_text(CONFIG.DIRS["html"] / "dashboard.html", html)

    def _print_summary(self, configs: List[BaseConfig]):
        table = Table(title="📊 Final Statistics", show_header=True, header_style="bold magenta")
        table.add_column("Category", style="cyan")
        table.add_column("Count", style="green")
        
        total = len(configs)
        table.add_row("Total Unique Configs", str(total))
        
        protos = Counter([c.protocol for c in configs])
        for p, c in protos.most_common():
            table.add_row(f"Protocol: {p.upper()}", str(c))
            
        top_countries = Counter([c.country for c in configs if c.country != 'XX']).most_common(5)
        for country, count in top_countries:
            flag = COUNTRY_CODE_TO_FLAG.get(country, '')
            table.add_row(f"Country: {flag} {country}", str(count))
            
        console.print(table)
        
        console.print(Panel(f"✅ Data saved to: {CONFIG.OUTPUT_DIR}", style="bold green"))

if __name__ == "__main__":
    try:
        asyncio.run(V2RayCollectorApp().run())
    except KeyboardInterrupt:
        pass
    except Exception as e:
        console.print_exception()
