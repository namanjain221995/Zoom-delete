"""
CSV-driven Zoom cloud cleanup:  Zoom admin CSV -> Zoom cloud -> S3 -> delete.

For every meeting ID in the exported CSV (Host, Topic, ID):
  1. Find ALL recording occurrences of that ID (same ID can have 2-3 recordings).
  2. For each file: if it is ALREADY in S3 with the correct size -> delete from
     Zoom (when enabled). If NOT in S3 -> upload, size-verify, THEN delete.
Nothing is ever deleted from Zoom unless the exact file passed the S3 size check.

Writes a per-meeting report to csv_cleanup_report.csv and a full audit trail.

UPDATED to match the zoom-recording-processor Lambda exactly:

  Departments (10):
    Interview-Success, Training, Advanced-Training, HR, Customer-Success,
    Marketing, COO, CEO, Executive-Assistant, Techsphere

  S3 layouts (identical to the Lambda):
    Interview-Success/{Host}/{Year}/{MonthName}/{Candidate}/{Company}/{Date}/{Round}/{MeetingID}/
    Training/{Trainer}/{Year}/{MonthName}/{Candidate}/{Date}/{Time}/{MeetingID}/
    HR/{HRPerson}/{Year}/{MonthName}/{Candidate}/{Date}/{Time}/{MeetingID}/
    Advanced-Training/{Host}/{Year}/{MonthName}/{CandidatesGroup}/{Date}/{Time}/{MeetingID}/
    {OtherDept}/{Host}/{Year}/{MonthName}/{Candidate}/{Date}/{Time}/{MeetingID}/

  {MonthName} = January..December (no more Month-N).
  Year/Month/Date come from the raw UTC start_time (same as Lambda);
  only the Time-...-IST folder is IST-converted (same as Lambda).
  Filenames = {recording_id}.{ext} (no more __hash suffix), so this script
  and the Lambda recognise each other's uploads (idempotent both ways).

  Extras ported from the Lambda:
    - Salesforce Round lookup for Interview-Success (Interview__c.Zoom_Meeting_Id__c
      -> Round_Info__c), cached token, auto-disable if auth fails.
    - Fuzzy folder canonicalisation for Trainer / HR person / generic Host
      against existing S3 folders (typo + case tolerant).
    - Advanced-Training: shared-account host resolution (real trainer =
      internal participant), ALL external participants grouped into one
      folder, full list written to participants.json.
"""

import os
import csv
import json
import time
import math
import base64
import calendar
import threading
from urllib.parse import quote, urlsplit, urlunsplit, parse_qsl, urlencode
from datetime import datetime, timezone, timedelta, date
from difflib import SequenceMatcher, get_close_matches
from concurrent.futures import ThreadPoolExecutor, as_completed

import boto3
import requests
from botocore.exceptions import ClientError
from boto3.s3.transfer import TransferConfig

try:
    from dotenv import load_dotenv
    load_dotenv()
except Exception:
    pass

TOKEN_URL = "https://zoom.us/oauth/token"
API_BASE = "https://api.zoom.us/v2"

REQUEST_TIMEOUT_SECONDS = int(os.getenv("REQUEST_TIMEOUT_SECONDS", "120"))
DOWNLOAD_TIMEOUT_SECONDS = int(os.getenv("DOWNLOAD_TIMEOUT_SECONDS", "900"))
MAX_HTTP_RETRIES = int(os.getenv("MAX_HTTP_RETRIES", "5"))

HOST_WORKERS = int(os.getenv("HOST_WORKERS", "4"))
TRANSFER_WORKERS = int(os.getenv("TRANSFER_WORKERS", "12"))
MAX_PENDING_TRANSFERS = int(os.getenv("MAX_PENDING_TRANSFERS", "200"))

ZOOM_SECRET_NAME = os.getenv("ZOOM_SECRET_NAME", "zoom/general-oauth")
S3_BUCKET_NAME = os.environ["S3_BUCKET_NAME"]
COMPANY_EMAIL_DOMAIN = os.getenv("COMPANY_EMAIL_DOMAIN", "techsarasolutions.com").strip().lower()

TARGET_DEPARTMENT_INPUT = os.getenv("TARGET_DEPARTMENT", "ALL").strip()
ONLY_HOST_EMAIL = os.getenv("ONLY_HOST_EMAIL", "").strip().lower()
ONLY_MEETING_ID = os.getenv("ONLY_MEETING_ID", "").strip()
MIN_SCAN_DATE = os.getenv("MIN_SCAN_DATE", "2000-01-01").strip()
SKIP_PARTICIPANTS_LOOKUP = os.getenv("SKIP_PARTICIPANTS_LOOKUP", "0").strip().lower() in {"1", "true", "yes", "y"}

DRY_RUN = os.getenv("DRY_RUN", "1").strip().lower() in {"1", "true", "yes", "y"}
DELETE_FROM_ZOOM = os.getenv("DELETE_FROM_ZOOM", "0").strip().lower() in {"1", "true", "yes", "y"}
DELETE_ACTION = os.getenv("DELETE_ACTION", "trash").strip().lower()  # trash | delete
PREFER_UUID_RECORDS = os.getenv("PREFER_UUID_RECORDS", "1").strip().lower() not in {"0", "false", "no", "n"}

TRANSCRIPT_RECHECK_ATTEMPTS = int(os.getenv("TRANSCRIPT_RECHECK_ATTEMPTS", "3"))
TRANSCRIPT_RECHECK_INITIAL_SLEEP_SECONDS = int(os.getenv("TRANSCRIPT_RECHECK_INITIAL_SLEEP_SECONDS", "20"))
TRANSCRIPT_RECHECK_MAX_SLEEP_SECONDS = int(os.getenv("TRANSCRIPT_RECHECK_MAX_SLEEP_SECONDS", "120"))

REQUIRE_S3_SIZE_MATCH = os.getenv("REQUIRE_S3_SIZE_MATCH", "1").strip().lower() not in {"0", "false", "no", "n"}
AUDIT_LOG_PATH = os.getenv("AUDIT_LOG_PATH", "csv_cleanup_audit.jsonl").strip()

DETAIL_DEBUG = os.getenv("DETAIL_DEBUG", "0").strip().lower() in {"1", "true", "yes", "y"}
ALLOW_UNSAFE_MEETING_ID_FALLBACK = os.getenv("ALLOW_UNSAFE_MEETING_ID_FALLBACK", "0").strip().lower() in {
    "1", "true", "yes", "y"
}

# ── NEW: Salesforce round lookup (Interview-Success) ──────────────────────────
SF_LOOKUP_ENABLED = os.getenv("SF_LOOKUP_ENABLED", "1").strip().lower() in {"1", "true", "yes", "y"}
SF_SECRET_NAME = os.getenv("SF_SECRET_NAME", "sf/jwt/credentials")
SF_OBJECT_API_NAME = os.getenv("SF_OBJECT_API_NAME", "Interview__c")
SF_MEETING_ID_FIELD = os.getenv("SF_MEETING_ID_FIELD_API_NAME", "Zoom_Meeting_Id__c")
SF_ROUND_FIELD = os.getenv("SF_ROUND_FIELD_API_NAME", "Round_Info__c")

# ── NEW: fuzzy folder-name matching (Trainer / HR person / generic Host) ─────
FOLDER_FUZZY_THRESHOLD = float(os.getenv("FOLDER_FUZZY_THRESHOLD",
                                         os.getenv("TRAINER_FUZZY_THRESHOLD", "0.88")))
FOLDER_CACHE_TTL_SEC = int(os.getenv("FOLDER_CACHE_TTL_SEC",
                                     os.getenv("TRAINER_CACHE_TTL_SEC", "600")))

# ── NEW: Advanced-Training (shared host account + grouped candidates) ────────
ADV_TRAINING_GENERIC_HOSTS = {
    e.strip().lower()
    for e in os.getenv(
        "ADV_TRAINING_GENERIC_HOSTS",
        "advance.training@techsarasolutions.com",
    ).split(",")
    if e.strip()
}
ADV_TRAINING_MAX_FOLDER_LEN = int(os.getenv("ADV_TRAINING_MAX_FOLDER_LEN", "200"))

# ── NEW (script only, NOT in Lambda): hosts WITHOUT a recognised department ──
#   INCLUDE_OTHER_DEPARTMENT=1 -> Zoom users whose "dept" field is EMPTY or
#   NOT in the known list are processed anyway, stored under "Other/" with the
#   generic layout:  Other/{Host}/{Year}/{Month}/{Candidate}/{Date}/{Time}/{MeetingID}/
#   Set 0 to skip such hosts (old behaviour).
INCLUDE_OTHER_DEPARTMENT = os.getenv("INCLUDE_OTHER_DEPARTMENT", "1").strip().lower() in {"1", "true", "yes", "y"}
OTHER_DEPARTMENT_FOLDER = "Other"

# ── NEW: CSV-driven cleanup config ────────────────────────────────────────────
#   CSV_PATH        - the Zoom admin "Recording Management" export (Host,Topic,ID)
#   REPORT_PATH     - per-meeting result report written by this script
#   MEETING_WORKERS - parallel meeting IDs processed (Zoom API bound; keep low)
CSV_PATH = os.getenv("CSV_PATH", "zoomus_recordings.csv").strip()
REPORT_PATH = os.getenv("REPORT_PATH", "csv_cleanup_report.csv").strip()
MEETING_WORKERS = int(os.getenv("MEETING_WORKERS", os.getenv("HOST_WORKERS", "3")))

AWS_REGION = (
    os.getenv("AWS_REGION")
    or os.getenv("AWS_DEFAULT_REGION")
    or os.getenv("AWS_REGION_NAME")
    or None
)

session = boto3.session.Session(region_name=AWS_REGION)
secrets = session.client("secretsmanager")
s3 = session.client("s3")
S3_TRANSFER_CONFIG = TransferConfig(use_threads=False)

# ── UPDATED: full department list (added Advanced-Training and HR) ────────────
DEPARTMENT_PRIORITY = [
    "Interview-Success",
    "Training",
    "Advanced-Training",
    "HR",
    "Customer-Success",
    "Marketing",
    "COO",
    "CEO",
    "Executive-Assistant",
    "Techsphere",
    "QMS",
    "Business-Development",
    "Other",   # NEW (script only): hosts with empty/unknown Zoom department
]

# ── UPDATED (cleanup): back up EVERY file type by default so Zoom cloud can be
#    fully emptied (MP4, M4A, TRANSCRIPT, CHAT, CC, TIMELINE, SUMMARY, ...).
#    Each type lands under its own {TYPE}/ folder inside the meeting prefix.
#    Restrict with e.g. UPLOAD_FILE_TYPES=MP4,M4A,TRANSCRIPT,CHAT if wanted.
_raw_types = os.getenv("UPLOAD_FILE_TYPES", "ALL").strip().upper()
UPLOAD_ALL_FILE_TYPES = _raw_types in {"ALL", "*", ""}
ALLOWED_FILE_TYPES = set() if UPLOAD_ALL_FILE_TYPES else {
    t.strip() for t in _raw_types.split(",") if t.strip()
}
TEXTUAL_FILE_TYPES = {"TRANSCRIPT", "CHAT", "CC"}


def file_type_allowed(file_type: str) -> bool:
    return UPLOAD_ALL_FILE_TYPES or file_type in ALLOWED_FILE_TYPES

# Month folder uses real names (January, February, ...) instead of Month-N
MONTH_NAMES = [
    "January", "February", "March", "April", "May", "June",
    "July", "August", "September", "October", "November", "December",
]

stats_lock = threading.Lock()
audit_lock = threading.Lock()


def build_allowed_departments():
    aliases = {}

    def add_alias(raw_value: str, canonical_value: str):
        aliases[raw_value.strip().lower()] = canonical_value

    for canonical in DEPARTMENT_PRIORITY:
        lower = canonical.lower()
        add_alias(canonical, canonical)
        add_alias(lower, canonical)
        add_alias(lower.replace("-", " "), canonical)
        add_alias(lower.replace("-", "_"), canonical)

    add_alias("interview success", "Interview-Success")
    add_alias("interview-success", "Interview-Success")
    add_alias("interview_success", "Interview-Success")

    add_alias("customer success", "Customer-Success")
    add_alias("customer-success", "Customer-Success")
    add_alias("customer_success", "Customer-Success")

    add_alias("executive assistant", "Executive-Assistant")
    add_alias("executive-assistant", "Executive-Assistant")
    add_alias("executive_assistant", "Executive-Assistant")

    add_alias("coo", "COO")
    add_alias("ceo", "CEO")
    add_alias("marketing", "Marketing")
    add_alias("training", "Training")

    add_alias("techsphere", "Techsphere")
    add_alias("tech sphere", "Techsphere")
    add_alias("tech-sphere", "Techsphere")
    add_alias("tech_sphere", "Techsphere")

    # NEW — HR department (same aliases as the Lambda)
    add_alias("hr", "HR")
    add_alias("h.r.", "HR")
    add_alias("h r", "HR")
    add_alias("human resources", "HR")
    add_alias("human-resources", "HR")
    add_alias("human_resources", "HR")
    add_alias("humanresources", "HR")

    # NEW — Advanced-Training department (same aliases as the Lambda)
    add_alias("advanced-training", "Advanced-Training")
    add_alias("advanced training", "Advanced-Training")
    add_alias("advanced_training", "Advanced-Training")
    add_alias("advancedtraining", "Advanced-Training")
    add_alias("advance-training", "Advanced-Training")
    add_alias("advance training", "Advanced-Training")
    add_alias("advance_training", "Advanced-Training")

    # NEW — QMS department (same aliases as the Lambda)
    add_alias("qms", "QMS")
    add_alias("q.m.s", "QMS")
    add_alias("q.m.s.", "QMS")
    add_alias("q m s", "QMS")
    add_alias("quality management", "QMS")
    add_alias("quality management system", "QMS")
    add_alias("quality-management-system", "QMS")
    add_alias("quality_management_system", "QMS")

    # NEW — Business-Development department (same aliases as the Lambda)
    add_alias("business-development", "Business-Development")
    add_alias("business development", "Business-Development")
    add_alias("business_development", "Business-Development")
    add_alias("businessdevelopment", "Business-Development")
    add_alias("bd", "Business-Development")
    add_alias("b.d.", "Business-Development")
    add_alias("biz dev", "Business-Development")
    add_alias("bizdev", "Business-Development")

    return aliases


ALLOWED_DEPARTMENTS = build_allowed_departments()


def normalize_department(raw_dept: str):
    dept = (raw_dept or "").strip().lower()
    return ALLOWED_DEPARTMENTS.get(dept)


def resolve_target_departments():
    raw = TARGET_DEPARTMENT_INPUT.strip()
    if not raw or raw.upper() in {"ALL", "*"}:
        return list(DEPARTMENT_PRIORITY)

    resolved = normalize_department(raw)
    if not resolved:
        raise RuntimeError(
            f"Unsupported TARGET_DEPARTMENT={TARGET_DEPARTMENT_INPUT!r}. "
            f"Use ALL or one of: {', '.join(DEPARTMENT_PRIORITY)}"
        )
    return [resolved]


TARGET_DEPARTMENTS = resolve_target_departments()


def request_with_retry(
    method,
    url,
    *,
    headers=None,
    headers_factory=None,
    params=None,
    data=None,
    stream=False,
    timeout=None,
    on_401=None,
):
    timeout = timeout or (DOWNLOAD_TIMEOUT_SECONDS if stream else REQUEST_TIMEOUT_SECONDS)
    last_exc = None

    for attempt in range(1, MAX_HTTP_RETRIES + 1):
        resp = None
        try:
            request_headers = headers_factory() if headers_factory else headers
            resp = requests.request(
                method=method,
                url=url,
                headers=request_headers,
                params=params,
                data=data,
                stream=stream,
                timeout=timeout,
            )

            if resp.status_code == 401 and on_401 is not None:
                try:
                    resp.close()
                except Exception:
                    pass
                if attempt >= MAX_HTTP_RETRIES:
                    raise requests.HTTPError(f"401 Unauthorized after retries for {method} {url}")
                on_401()
                time.sleep(min(attempt, 3))
                continue

            if resp.status_code in {429, 500, 502, 503, 504}:
                retry_after = resp.headers.get("Retry-After")
                sleep_s = int(retry_after) if retry_after and retry_after.isdigit() else min(2 ** attempt, 30)
                preview = ""
                try:
                    preview = resp.text[:200]
                except Exception:
                    pass
                print(
                    f"[HTTP RETRY] {method} {url}; status={resp.status_code}; "
                    f"attempt={attempt}/{MAX_HTTP_RETRIES}; sleep={sleep_s}s; preview={preview!r}"
                )
                try:
                    resp.close()
                except Exception:
                    pass
                time.sleep(sleep_s)
                continue

            if 400 <= resp.status_code < 500 and resp.status_code not in {401, 429}:
                preview = ""
                try:
                    preview = resp.text[:500]
                except Exception:
                    pass
                raise requests.HTTPError(
                    f"{resp.status_code} Client Error for {method} {url}; body={preview!r}",
                    response=resp,
                )

            resp.raise_for_status()
            return resp

        except requests.RequestException as exc:
            last_exc = exc

            client_error_no_retry = (
                resp is not None and 400 <= resp.status_code < 500 and resp.status_code not in {401, 429}
            )

            if resp is not None:
                try:
                    resp.close()
                except Exception:
                    pass

            if client_error_no_retry or attempt >= MAX_HTTP_RETRIES:
                raise

            sleep_s = min(2 ** attempt, 30)
            print(
                f"[HTTP ERROR] {method} {url}; attempt={attempt}/{MAX_HTTP_RETRIES}; "
                f"sleep={sleep_s}s; error={exc}"
            )
            time.sleep(sleep_s)

    if last_exc:
        raise last_exc
    raise RuntimeError(f"Unexpected HTTP failure calling {method} {url}")


def get_zoom_secret():
    resp = secrets.get_secret_value(SecretId=ZOOM_SECRET_NAME)
    secret_obj = json.loads(resp["SecretString"])

    required = ["account_id", "client_id", "client_secret"]
    missing = [k for k in required if not secret_obj.get(k)]
    if missing:
        raise RuntimeError(f"Missing keys in Secrets Manager secret {ZOOM_SECRET_NAME}: {missing}")

    return secret_obj


def basic_auth_header(client_id, client_secret):
    raw = f"{client_id}:{client_secret}".encode("utf-8")
    return "Basic " + base64.b64encode(raw).decode("utf-8")


class ZoomTokenManager:
    def __init__(self, secret_obj):
        self.secret_obj = secret_obj
        self._token = None
        self._expires_at = 0.0
        self._lock = threading.Lock()

    def _refresh_locked(self):
        headers = {
            "Authorization": basic_auth_header(
                self.secret_obj["client_id"],
                self.secret_obj["client_secret"],
            ),
            "Content-Type": "application/x-www-form-urlencoded",
        }
        data = {
            "grant_type": "account_credentials",
            "account_id": self.secret_obj["account_id"],
        }

        resp = request_with_retry("POST", TOKEN_URL, headers=headers, data=data, stream=False)
        try:
            tok = resp.json()
        finally:
            resp.close()

        access_token = tok.get("access_token")
        expires_in = int(tok.get("expires_in", 3600))
        if not access_token:
            raise RuntimeError("Zoom token response missing access_token")

        self._token = access_token
        self._expires_at = time.time() + max(expires_in - 60, 60)

    def get_token(self, force_refresh=False):
        with self._lock:
            if force_refresh or not self._token or time.time() >= self._expires_at:
                self._refresh_locked()
            return self._token


def zoom_headers_factory(token_manager):
    return {"Authorization": f"Bearer {token_manager.get_token()}"}


def zoom_refresh_callback(token_manager):
    def _cb():
        token_manager.get_token(force_refresh=True)
    return _cb


def zoom_get(token_manager, path, params=None):
    url = f"{API_BASE}{path}"
    resp = request_with_retry(
        "GET",
        url,
        headers_factory=lambda: zoom_headers_factory(token_manager),
        params=params,
        stream=False,
        on_401=zoom_refresh_callback(token_manager),
    )
    try:
        return resp.json()
    finally:
        resp.close()


def zoom_delete(token_manager, path, params=None):
    url = f"{API_BASE}{path}"
    resp = request_with_retry(
        "DELETE",
        url,
        headers_factory=lambda: zoom_headers_factory(token_manager),
        params=params,
        stream=False,
        on_401=zoom_refresh_callback(token_manager),
    )
    try:
        return resp.status_code
    finally:
        resp.close()


def zoom_get_paginated(token_manager, path, list_key, base_params=None):
    next_page_token = ""
    while True:
        params = dict(base_params or {})
        params.setdefault("page_size", 300)
        if next_page_token:
            params["next_page_token"] = next_page_token

        data = zoom_get(token_manager, path, params=params)
        items = data.get(list_key, []) or []
        for item in items:
            yield item

        next_page_token = data.get("next_page_token") or ""
        if not next_page_token:
            break


# ══════════════════════════════════════════════════════════════════════════════
#  NEW: Salesforce JWT auth + Round lookup  (same behaviour as the Lambda,
#  but with a shared cached token and a circuit-breaker so a bulk run does
#  not hammer the token endpoint if credentials are missing/broken)
# ══════════════════════════════════════════════════════════════════════════════

def _b64url_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode()


def _build_sf_jwt_assertion(sf_secret: dict) -> str:
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import padding as asym_padding

    client_id = sf_secret["SF_CLIENT_ID"]
    username = sf_secret["SF_USERNAME"]
    login_url = sf_secret.get("SF_LOGIN_URL", "https://login.salesforce.com")
    pem_b64 = sf_secret["PRIVATE_KEY_B64"]

    pem_bytes = base64.b64decode(pem_b64)
    private_key = serialization.load_pem_private_key(pem_bytes, password=None)

    header = {"alg": "RS256"}
    payload = {
        "iss": client_id,
        "sub": username,
        "aud": login_url,
        "exp": math.floor(time.time()) + 300,
    }

    header_enc = _b64url_encode(json.dumps(header, separators=(",", ":")).encode())
    payload_enc = _b64url_encode(json.dumps(payload, separators=(",", ":")).encode())
    signing_input = f"{header_enc}.{payload_enc}".encode()

    signature = private_key.sign(signing_input, asym_padding.PKCS1v15(), hashes.SHA256())
    sig_enc = _b64url_encode(signature)

    return f"{header_enc}.{payload_enc}.{sig_enc}"


class SalesforceTokenManager:
    """Thread-safe cached SF access token. Disables itself after a hard auth failure."""

    def __init__(self):
        self._lock = threading.Lock()
        self._token = None
        self._instance_url = None
        self._disabled = not SF_LOOKUP_ENABLED

    def _authenticate_locked(self):
        resp = secrets.get_secret_value(SecretId=SF_SECRET_NAME)
        sf_secret = json.loads(resp["SecretString"])

        login_url = sf_secret.get("SF_LOGIN_URL", "https://login.salesforce.com")
        assertion = _build_sf_jwt_assertion(sf_secret)

        r = requests.post(
            f"{login_url}/services/oauth2/token",
            data={
                "grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer",
                "assertion": assertion,
            },
            timeout=30,
        )
        print(f"SF token status: {r.status_code}")
        r.raise_for_status()

        tok = r.json()
        access_token = tok.get("access_token")
        instance_url = tok.get("instance_url")
        if not access_token or not instance_url:
            raise RuntimeError(f"SF token response missing fields: {tok}")

        self._token = access_token
        self._instance_url = instance_url

    def get(self, force_refresh=False):
        if self._disabled:
            return None, None
        with self._lock:
            if self._disabled:
                return None, None
            if force_refresh or not self._token:
                try:
                    self._authenticate_locked()
                except Exception as exc:
                    print(f"[SF AUTH FAILED] Salesforce round lookup disabled for this run: {exc}")
                    self._disabled = True
                    return None, None
            return self._token, self._instance_url


sf_token_manager = SalesforceTokenManager()


def lookup_round_from_sf(meeting_id):
    """Interview__c.Zoom_Meeting_Id__c == meeting_id -> Round_Info__c (or None)."""
    if not SF_LOOKUP_ENABLED:
        return None

    token, instance_url = sf_token_manager.get()
    if not token:
        return None

    soql = (
        f"SELECT {SF_ROUND_FIELD} "
        f"FROM {SF_OBJECT_API_NAME} "
        f"WHERE {SF_MEETING_ID_FIELD} = '{meeting_id}' "
        f"LIMIT 1"
    )

    try:
        resp = requests.get(
            f"{instance_url}/services/data/v59.0/query",
            headers={"Authorization": f"Bearer {token}"},
            params={"q": soql},
            timeout=30,
        )

        if resp.status_code == 401:
            token, instance_url = sf_token_manager.get(force_refresh=True)
            if not token:
                return None
            resp = requests.get(
                f"{instance_url}/services/data/v59.0/query",
                headers={"Authorization": f"Bearer {token}"},
                params={"q": soql},
                timeout=30,
            )

        resp.raise_for_status()
        records = resp.json().get("records", [])
        if not records:
            print(f"No Salesforce record found for meeting_id={meeting_id}")
            return None

        raw_round = records[0].get(SF_ROUND_FIELD)
        if not raw_round:
            print(f"Salesforce record found but {SF_ROUND_FIELD} empty for meeting_id={meeting_id}")
            return None

        round_name = sanitize_name(str(raw_round))
        print(f"Salesforce round lookup success: meeting_id={meeting_id} -> {round_name}")
        return round_name

    except Exception as exc:
        print(f"Salesforce round lookup failed (meeting_id={meeting_id}): {exc}")
        return None


def sanitize_name(name: str) -> str:
    if not name:
        return "Unknown"
    cleaned = "".join(c if c.isalnum() or c in (" ", "-", "_") else "_" for c in str(name)).strip()
    return cleaned.replace(" ", "_") or "Unknown"


def normalize_meeting_id_value(value) -> str:
    return "".join(ch for ch in str(value or "") if ch.isdigit())


def build_recording_filename(recording_id, ext):
    """UPDATED: plain {sanitized_id}.{ext} — identical to the Lambda, so both
    systems recognise each other's uploads (no more __sha1 suffix)."""
    safe = sanitize_name(str(recording_id)) or "recording"
    return f"{safe}.{ext}" if ext else safe


def encode_zoom_uuid(meeting_uuid):
    raw = str(meeting_uuid)
    encoded_once = quote(raw, safe="")
    if raw.startswith("/") or "//" in raw:
        return quote(encoded_once, safe="")
    return encoded_once


def parse_date_yyyy_mm_dd(value: str) -> date:
    return datetime.strptime(value, "%Y-%m-%d").date()


def safe_user_start_date(user):
    created = (user.get("created_at") or "").strip()
    if len(created) >= 10:
        return max(created[:10], MIN_SCAN_DATE)
    return MIN_SCAN_DATE


def today_utc_date_str():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def iter_month_windows(start_date_str: str, end_date_str: str):
    start_d = parse_date_yyyy_mm_dd(start_date_str)
    end_d = parse_date_yyyy_mm_dd(end_date_str)
    if end_d < start_d:
        raise RuntimeError(f"End date {end_date_str} cannot be before start date {start_date_str}")

    cursor = start_d
    while cursor <= end_d:
        last_dom = calendar.monthrange(cursor.year, cursor.month)[1]
        month_end = date(cursor.year, cursor.month, last_dom)
        window_end = min(month_end, end_d)
        yield cursor.strftime("%Y-%m-%d"), window_end.strftime("%Y-%m-%d")
        cursor = window_end + timedelta(days=1)


def parse_zoom_start_time(start_time: str):
    if not start_time:
        return None

    candidates = [
        start_time,
        start_time.replace("Z", "+00:00") if start_time.endswith("Z") else start_time,
    ]

    for value in candidates:
        try:
            dt = datetime.fromisoformat(value)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.astimezone(timezone.utc)
        except Exception:
            pass

    for fmt in ("%Y-%m-%dT%H:%M:%SZ", "%Y-%m-%dT%H:%M:%S%z"):
        try:
            dt = datetime.strptime(start_time, fmt)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.astimezone(timezone.utc)
        except Exception:
            pass

    return None


def month_folder_name(start_time: str) -> str:
    """January..December from the raw UTC start_time string (same as Lambda)."""
    if not start_time or len(start_time) < 7:
        return "UnknownMonth"
    try:
        n = int(start_time[5:7])
        if 1 <= n <= 12:
            return MONTH_NAMES[n - 1]
    except Exception:
        pass
    return "UnknownMonth"


def build_time_folder_ist(start_time: str) -> str:
    dt_utc = parse_zoom_start_time(start_time)
    if not dt_utc:
        return "Time-Unknown-IST"
    ist = timezone(timedelta(hours=5, minutes=30))
    dt_ist = dt_utc.astimezone(ist)
    hour_12 = dt_ist.strftime("%I").lstrip("0") or "12"
    return f"Time-{hour_12}-{dt_ist.strftime('%M')}-{dt_ist.strftime('%p')}-IST"


def build_path_parts(start_time: str):
    """UPDATED to match the Lambda exactly:
    Year/Month/Date from the raw UTC string; only Time folder is IST."""
    year = start_time[:4] if len(start_time or "") >= 4 else "UnknownYear"
    month = month_folder_name(start_time or "")
    date_only = start_time[:10] if len(start_time or "") >= 10 else "UnknownDate"
    time_folder = build_time_folder_ist(start_time or "")
    return year, month, date_only, time_folder


def build_host_name(user):
    return sanitize_name(
        ((user.get("first_name") or "") + " " + (user.get("last_name") or "")).strip()
        or user.get("display_name")
        or user.get("email")
        or user.get("id")
        or "Unknown_Host"
    )


def list_all_users(token_manager):
    return list(
        zoom_get_paginated(
            token_manager=token_manager,
            path="/users",
            list_key="users",
            base_params={"status": "active", "page_size": 300},
        )
    )


def list_user_recordings(token_manager, user_id, from_date, to_date):
    path = f"/users/{quote(str(user_id), safe='')}/recordings"
    return list(
        zoom_get_paginated(
            token_manager=token_manager,
            path=path,
            list_key="meetings",
            base_params={"from": from_date, "to": to_date, "trash": "false", "page_size": 300},
        )
    )


def list_all_participants(token_manager, meeting_uuid):
    encoded_uuid = encode_zoom_uuid(meeting_uuid)
    path = f"/past_meetings/{encoded_uuid}/participants"
    try:
        return list(
            zoom_get_paginated(
                token_manager=token_manager,
                path=path,
                list_key="participants",
                base_params={"page_size": 300},
            )
        )
    except Exception as e:
        print(f"Could not fetch participants for meeting_uuid={meeting_uuid}: {e}")
        return []


def extract_recording_files(obj):
    if not isinstance(obj, dict):
        return []
    files = obj.get("recording_files") or []
    return [f for f in files if isinstance(f, dict)]


def recording_files_count(obj):
    return len(extract_recording_files(obj))


def recording_count_value(obj):
    try:
        return int((obj or {}).get("recording_count") or 0)
    except Exception:
        return 0


def total_size_value(obj):
    try:
        return int((obj or {}).get("total_size") or 0)
    except Exception:
        return 0


def same_occurrence(detail, requested_uuid, requested_start_time):
    detail_uuid = str((detail or {}).get("uuid") or "").strip()
    req_uuid = str(requested_uuid or "").strip()
    if detail_uuid and req_uuid and detail_uuid == req_uuid:
        return True

    detail_dt = parse_zoom_start_time((detail or {}).get("start_time") or "")
    req_dt = parse_zoom_start_time(requested_start_time or "")
    if detail_dt and req_dt:
        return abs((detail_dt - req_dt).total_seconds()) <= 120

    return False


def log_detail_candidate(source_label, detail, meeting_id, meeting_uuid, requested_start_time):
    if not DETAIL_DEBUG:
        return

    print(
        json.dumps(
            {
                "detail_source": source_label,
                "requested_meeting_id": meeting_id,
                "requested_meeting_uuid": meeting_uuid,
                "requested_start_time": requested_start_time,
                "returned_meeting_id": detail.get("id"),
                "returned_meeting_uuid": detail.get("uuid"),
                "returned_start_time": detail.get("start_time"),
                "recording_count": detail.get("recording_count"),
                "total_size": detail.get("total_size"),
                "recording_files_len": recording_files_count(detail),
                "same_occurrence": same_occurrence(detail, meeting_uuid, requested_start_time),
            },
            indent=2,
            default=str,
        )
    )


def detail_sort_key(entry):
    return (
        1 if entry["safe"] else 0,
        1 if entry["source"] == "uuid" else 0,
        entry["files_len"],
        entry["recording_count"],
        entry["total_size"],
    )


def get_recording_detail(token_manager, meeting_uuid, meeting_id, requested_start_time=""):
    errors = []
    candidates = []

    def fetch_uuid():
        encoded_uuid = encode_zoom_uuid(meeting_uuid)
        return zoom_get(token_manager, f"/meetings/{encoded_uuid}/recordings")

    def fetch_id():
        return zoom_get(token_manager, f"/meetings/{meeting_id}/recordings")

    fetch_order = [("uuid", fetch_uuid), ("id", fetch_id)] if PREFER_UUID_RECORDS else [("id", fetch_id), ("uuid", fetch_uuid)]

    for source_label, fetcher in fetch_order:
        if source_label == "uuid" and not meeting_uuid:
            continue
        if source_label == "id" and not meeting_id:
            continue

        try:
            detail = fetcher()
            safe = source_label == "uuid" or same_occurrence(detail, meeting_uuid, requested_start_time)
            if source_label == "id" and not safe and ALLOW_UNSAFE_MEETING_ID_FALLBACK:
                safe = True

            entry = {
                "source": source_label,
                "detail": detail,
                "safe": safe,
                "files_len": recording_files_count(detail),
                "recording_count": recording_count_value(detail),
                "total_size": total_size_value(detail),
            }
            candidates.append(entry)
            log_detail_candidate(source_label, detail, meeting_id, meeting_uuid, requested_start_time)

        except Exception as e:
            errors.append(f"{source_label} fetch failed: {e}")
            print(
                f"[DETAIL ERROR] source={source_label}; "
                f"meeting_id={meeting_id}; meeting_uuid={meeting_uuid}; error={e}"
            )

    usable = [c for c in candidates if c["files_len"] > 0 and c["safe"]]
    if usable:
        chosen = max(usable, key=detail_sort_key)
        mode = "safe"
        if chosen["source"] == "id" and not same_occurrence(chosen["detail"], meeting_uuid, requested_start_time):
            mode = "unsafe"
        print(
            f"[DETAIL PICK] source={chosen['source']}; mode={mode}; "
            f"meeting_id={meeting_id}; meeting_uuid={meeting_uuid}; files={chosen['files_len']}"
        )
        return chosen["detail"]

    if candidates:
        chosen = max(candidates, key=detail_sort_key)
        print(
            f"[DETAIL PICK] source={chosen['source']}; mode=empty_or_unusable; "
            f"meeting_id={meeting_id}; meeting_uuid={meeting_uuid}; files={chosen['files_len']}"
        )
        return chosen["detail"]

    raise RuntimeError(" ; ".join(errors) if errors else "Could not fetch recording detail")


def extract_extension(recording_file):
    file_extension = (recording_file.get("file_extension") or "").strip().lower()
    if file_extension:
        return file_extension

    download_url = recording_file.get("download_url") or ""
    base = download_url.split("?", 1)[0]
    if "." in base:
        ext = base.rsplit(".", 1)[-1].strip().lower()
        if ext:
            return ext

    file_type = (recording_file.get("file_type") or "").strip().lower()
    default_ext = {
        "mp4": "mp4",
        "m4a": "m4a",
        "transcript": "vtt",
        "chat": "txt",
        "cc": "vtt",
    }
    return default_ext.get(file_type, "")


def merge_non_empty_dicts(old_obj, new_obj):
    merged = dict(old_obj or {})
    for k, v in (new_obj or {}).items():
        if v is None:
            continue
        if isinstance(v, str) and v == "":
            continue
        if isinstance(v, (list, dict)) and len(v) == 0:
            continue
        merged[k] = v
    return merged


def recording_file_key(rf):
    rid = str(rf.get("id") or rf.get("recording_id") or "").strip()
    ftype = (rf.get("file_type") or "").upper().strip()
    if rid:
        return ("id", rid, ftype)

    base_url = str(rf.get("download_url") or rf.get("play_url") or "").split("?", 1)[0].strip()
    if base_url:
        return ("url", base_url, ftype)

    return ("raw", json.dumps(rf, sort_keys=True, default=str), ftype)


def merge_recording_file_lists(*lists_):
    merged = {}
    order = []

    for lst in lists_:
        for rf in lst or []:
            if not isinstance(rf, dict):
                continue
            key = recording_file_key(rf)
            if key not in merged:
                merged[key] = dict(rf)
                order.append(key)
            else:
                merged[key] = merge_non_empty_dicts(merged[key], rf)

    return [merged[k] for k in order]


def extract_download_tokens(obj):
    obj = obj or {}
    return {
        "download_access_token": obj.get("download_access_token") or "",
        "recording_access_token": obj.get("recording_access_token") or "",
    }


def merge_download_tokens(*objs):
    merged = {
        "download_access_token": "",
        "recording_access_token": "",
    }
    for obj in objs:
        tokens = extract_download_tokens(obj)
        for k, v in tokens.items():
            if not merged[k] and v:
                merged[k] = v
    return merged


# ══════════════════════════════════════════════════════════════════════════════
#  NEW: generic fuzzy folder-name matcher (Trainer / HR person / generic Host)
#  Thread-safe port of the Lambda's canonicaliser.
# ══════════════════════════════════════════════════════════════════════════════

_FOLDER_CACHE = {}
_FOLDER_CACHE_LOCK = threading.Lock()


def list_known_folders(dept_prefix: str) -> list:
    if not dept_prefix.endswith("/"):
        dept_prefix = dept_prefix + "/"

    now = time.time()
    with _FOLDER_CACHE_LOCK:
        entry = _FOLDER_CACHE.get(dept_prefix)
        if entry and (now - entry["timestamp"]) < FOLDER_CACHE_TTL_SEC:
            return entry["folders"]

    try:
        folders = set()
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(
            Bucket=S3_BUCKET_NAME,
            Prefix=dept_prefix,
            Delimiter="/",
        ):
            for cp in page.get("CommonPrefixes", []):
                prefix = cp.get("Prefix", "")
                name = prefix[len(dept_prefix):].rstrip("/")
                if name:
                    folders.add(name)

        sorted_folders = sorted(folders)
        with _FOLDER_CACHE_LOCK:
            _FOLDER_CACHE[dept_prefix] = {
                "folders": sorted_folders,
                "timestamp": now,
            }
        print(f"Folder cache refreshed for {dept_prefix}: {len(sorted_folders)} entries")
        return sorted_folders
    except Exception as exc:
        print(f"Failed to list folders under {dept_prefix}: {exc} - using previous cache")
        with _FOLDER_CACHE_LOCK:
            entry = _FOLDER_CACHE.get(dept_prefix)
            return entry["folders"] if entry else []


def find_canonical_folder(name_raw: str, dept_prefix: str, threshold: float = None):
    if threshold is None:
        threshold = FOLDER_FUZZY_THRESHOLD

    if not name_raw:
        return name_raw, "empty_input"

    known = list_known_folders(dept_prefix)
    if not known:
        return name_raw, "no_known_entries"

    normalized = name_raw.lower().strip()

    for canonical in known:
        if canonical.lower() == normalized:
            if canonical == name_raw:
                return canonical, "exact"
            return canonical, "case_corrected"

    lowered_to_canonical = {k.lower(): k for k in known}
    matches = get_close_matches(
        normalized,
        list(lowered_to_canonical.keys()),
        n=1,
        cutoff=threshold,
    )
    if matches:
        canonical = lowered_to_canonical[matches[0]]
        score = SequenceMatcher(None, normalized, matches[0]).ratio()
        return canonical, f"fuzzy_matched(score={score:.3f})"

    return name_raw, "new_entry"


# ══════════════════════════════════════════════════════════════════════════════
#  Topic parsers + candidate pickers
# ══════════════════════════════════════════════════════════════════════════════

def parse_interview_success_topic(topic: str):
    raw_topic = (topic or "").strip()
    if not raw_topic:
        return None

    parts = [p.strip() for p in raw_topic.split("<>")]
    parts = [p for p in parts if p]
    if len(parts) < 3:
        return None

    candidate_name = sanitize_name(parts[0])
    company_name = sanitize_name(parts[1])
    round_name = sanitize_name(parts[-1])

    if not candidate_name or not company_name or not round_name:
        return None

    return {
        "candidate_name": candidate_name,
        "company_name": company_name,
        "round_name": round_name,
    }


def parse_training_topic(topic: str):
    """NEW (same as Lambda): <Candidate> <> <Trainer> <> Training"""
    raw_topic = (topic or "").strip()
    if not raw_topic:
        return None

    parts = [p.strip() for p in raw_topic.split("<>") if p.strip()]

    if len(parts) < 3:
        return None

    if parts[-1].strip().lower() != "training":
        return None

    candidate_name = sanitize_name(parts[0])
    trainer_name = sanitize_name(parts[1])

    if candidate_name == "Unknown" or trainer_name == "Unknown":
        return None

    return {
        "candidate_name": candidate_name,
        "trainer_name": trainer_name,
    }


def extract_candidate_from_topic_fallback(topic: str):
    raw = (topic or "").strip()
    if not raw:
        return None

    cleaned = raw
    for prefix in (
        "Interview Support",
        "Interview-Support",
        "Interview",
        "Techsara Interview",
        "Candidate Interview",
        "Advanced Training",
        "Advanced-Training",
        "Training",
        "Marketing",
        "Customer Success",
        "Customer-Success",
        "Executive Assistant",
        "Executive-Assistant",
        "Human Resources",
        "HR",
        "CEO",
        "COO",
        "Techsphere",
        "Tech Sphere",
        "Tech-Sphere",
        "QMS",
        "Business Development",
        "Business-Development",
    ):
        if cleaned.lower().startswith(prefix.lower()):
            cleaned = cleaned[len(prefix):].strip(" :-_")
            break

    cleaned = cleaned.replace("'s Zoom Meeting", "").replace("Zoom Meeting", "").strip(" :-_")
    if not cleaned:
        return None

    return sanitize_name(cleaned)


def pick_candidate(participants, host_email, topic):
    host_email = (host_email or "").strip().lower()

    for p in participants:
        email = (p.get("user_email") or p.get("email") or "").strip().lower()
        internal_user = p.get("internal_user")
        if email and email != host_email and not email.endswith("@" + COMPANY_EMAIL_DOMAIN):
            return sanitize_name(p.get("name") or email.split("@")[0])
        if internal_user is False:
            name = (p.get("name") or "").strip()
            if name:
                return sanitize_name(name)

    topic_candidate = extract_candidate_from_topic_fallback(topic)
    if topic_candidate:
        return topic_candidate

    for p in participants:
        email = (p.get("user_email") or p.get("email") or "").strip().lower()
        name = (p.get("name") or "").strip()
        if email != host_email and name:
            return sanitize_name(name)

    return "Unknown_Candidate"


# ── NEW: Advanced-Training helpers (same as Lambda) ────────────────────────────

def resolve_adv_training_host(participants, host_email, host_name):
    """Shared account hosted -> real trainer = internal participant.
    Real person hosted -> keep them."""
    he = (host_email or "").strip().lower()

    if he and he not in ADV_TRAINING_GENERIC_HOSTS:
        return host_name

    for p in participants:
        email = (p.get("user_email") or p.get("email") or "").strip().lower()
        if (
            email
            and email.endswith("@" + COMPANY_EMAIL_DOMAIN)
            and email not in ADV_TRAINING_GENERIC_HOSTS
        ):
            return sanitize_name((p.get("name") or email.split("@")[0]).strip())

    return host_name


def pick_all_candidates(participants, host_email):
    """ALL external participants, deduped, name-sorted (stable folder)."""
    host_email = (host_email or "").strip().lower()
    seen, out = set(), []

    for p in participants:
        email = (p.get("user_email") or p.get("email") or "").strip().lower()
        name = (p.get("name") or "").strip()

        if email == host_email:
            continue
        if email and email.endswith("@" + COMPANY_EMAIL_DOMAIN):
            continue

        clean = sanitize_name(name or (email.split("@")[0] if email else ""))
        if clean == "Unknown":
            continue

        key = email or clean.lower()
        if key in seen:
            continue
        seen.add(key)
        out.append({"name": clean, "email": email})

    out.sort(key=lambda c: c["name"].lower())
    return out


def build_group_candidate_folder(candidates, max_len=None):
    """Amit_Verma-Priya_Patel-Rahul_Sharma-and_17_more (capped, S3 key safe)."""
    if max_len is None:
        max_len = ADV_TRAINING_MAX_FOLDER_LEN

    names = [c["name"] for c in candidates]
    if not names:
        return "Unknown_Candidates"

    folder, used = names[0][:max_len], 1
    for n in names[1:]:
        nxt = f"{folder}-{n}"
        if len(nxt) > max_len:
            break
        folder, used = nxt, used + 1

    remaining = len(names) - used
    if remaining > 0:
        folder = f"{folder}-and_{remaining}_more"
    return folder


# ══════════════════════════════════════════════════════════════════════════════
#  UPDATED: storage-path resolution (per-department, same as Lambda)
# ══════════════════════════════════════════════════════════════════════════════

def resolve_storage_info(department_folder, topic, participants, host_email, meeting_id, host_name):

    # ── Interview-Success (SF round first, then topic, then fallback) ──────
    if department_folder == "Interview-Success":
        sf_round = lookup_round_from_sf(meeting_id)
        parsed = parse_interview_success_topic(topic)

        if sf_round:
            candidate = parsed["candidate_name"] if parsed else pick_candidate(participants, host_email, topic)
            company = parsed["company_name"] if parsed else "Unknown_Company"
            round_name = sf_round
            print(f"Round resolved from Salesforce: {round_name}")
        elif parsed:
            candidate = parsed["candidate_name"]
            company = parsed["company_name"]
            round_name = parsed["round_name"]
            print(f"Round resolved from topic parsing: {round_name}")
        else:
            candidate = pick_candidate(participants, host_email, topic)
            company = "Unknown_Company"
            round_name = "Unknown_Round"
            print("Round could not be resolved; using Unknown_Round")

        return {
            "candidate_name": candidate,
            "company_name": company,
            "round_name": round_name,
            "trainer_name": None,
            "hr_person_name": None,
            "canonical_host_name": None,
        }

    # ── Training (topic parser + fuzzy trainer match) ──────────────────────
    if department_folder == "Training":
        parsed = parse_training_topic(topic)

        if parsed:
            candidate = parsed["candidate_name"]
            trainer_raw = parsed["trainer_name"]
        else:
            candidate = pick_candidate(participants, host_email, topic)
            trainer_raw = sanitize_name((host_email or "").split("@")[0]) or "Unknown_Trainer"
            print(f"Training topic parse failed - fallback: candidate={candidate}, trainer={trainer_raw}")

        trainer_canonical, match_reason = find_canonical_folder(trainer_raw, "Training/")
        if trainer_canonical != trainer_raw:
            print(f"Trainer name normalized: '{trainer_raw}' -> '{trainer_canonical}' ({match_reason})")

        return {
            "candidate_name": candidate,
            "company_name": None,
            "round_name": None,
            "trainer_name": trainer_canonical,
            "hr_person_name": None,
            "canonical_host_name": None,
        }

    # ── HR (host is the HR person, candidate from participants) ────────────
    if department_folder == "HR":
        candidate = pick_candidate(participants, host_email, topic)
        hr_person_raw = host_name or "Unknown_HR_Person"

        hr_person_canonical, match_reason = find_canonical_folder(hr_person_raw, "HR/")
        if hr_person_canonical != hr_person_raw:
            print(f"HR person name normalized: '{hr_person_raw}' -> '{hr_person_canonical}' ({match_reason})")

        return {
            "candidate_name": candidate,
            "company_name": None,
            "round_name": None,
            "trainer_name": None,
            "hr_person_name": hr_person_canonical,
            "canonical_host_name": None,
        }

    # ── Advanced-Training (shared host account + group of candidates) ─────
    if department_folder == "Advanced-Training":
        internal_host = resolve_adv_training_host(participants, host_email, host_name)
        candidates = pick_all_candidates(participants, host_email)
        group_folder = build_group_candidate_folder(candidates)

        host_canonical, match_reason = find_canonical_folder(internal_host, "Advanced-Training/")
        if host_canonical != internal_host:
            print(f"Adv-Training host normalized: '{internal_host}' -> '{host_canonical}' ({match_reason})")

        print(f"Adv-Training candidates ({len(candidates)}): {group_folder}")

        return {
            "candidate_name": group_folder,
            "company_name": None,
            "round_name": None,
            "trainer_name": None,
            "hr_person_name": None,
            "canonical_host_name": host_canonical,
            "all_candidates": candidates,
        }

    # ── All other departments (generic — fuzzy host matching) ─────────────
    candidate = pick_candidate(participants, host_email, topic)

    canonical_host, match_reason = find_canonical_folder(host_name, f"{department_folder}/")
    if canonical_host != host_name:
        print(f"Host name normalized: '{host_name}' -> '{canonical_host}' ({match_reason})")

    return {
        "candidate_name": candidate,
        "company_name": None,
        "round_name": None,
        "trainer_name": None,
        "hr_person_name": None,
        "canonical_host_name": canonical_host,
    }


def build_base_prefix(
    department_folder,
    host_name,
    year,
    month,
    candidate_name,
    date_only,
    time_folder,
    company_name=None,
    round_name=None,
    meeting_id=None,
    trainer_name=None,
    hr_person_name=None,
    canonical_host_name=None,
):
    """
    UPDATED — identical to the Lambda:

    Interview-Success:
        Interview-Success/{Host}/{Year}/{MonthName}/{Candidate}/{Company}/{Date}/{Round}/{MeetingID}/
    Training:
        Training/{Trainer}/{Year}/{MonthName}/{Candidate}/{Date}/{Time}/{MeetingID}/
    HR:
        HR/{HRPerson}/{Year}/{MonthName}/{Candidate}/{Date}/{Time}/{MeetingID}/
    Advanced-Training + all other departments:
        {Department}/{Host}/{Year}/{MonthName}/{Candidate(s)}/{Date}/{Time}/{MeetingID}/
    """
    meeting_id_folder = str(meeting_id).strip() if meeting_id else "Unknown_Meeting_ID"

    if department_folder == "Interview-Success":
        company_name = company_name or "Unknown_Company"
        round_name = round_name or "Unknown_Round"

        return (
            f"{department_folder}/"
            f"{host_name}/"
            f"{year}/"
            f"{month}/"
            f"{candidate_name}/"
            f"{company_name}/"
            f"{date_only}/"
            f"{round_name}/"
            f"{meeting_id_folder}/"
        )

    if department_folder == "Training":
        trainer = trainer_name or host_name or "Unknown_Trainer"

        return (
            f"{department_folder}/"
            f"{trainer}/"
            f"{year}/"
            f"{month}/"
            f"{candidate_name}/"
            f"{date_only}/"
            f"{time_folder}/"
            f"{meeting_id_folder}/"
        )

    if department_folder == "HR":
        hr_person = hr_person_name or host_name or "Unknown_HR_Person"

        return (
            f"{department_folder}/"
            f"{hr_person}/"
            f"{year}/"
            f"{month}/"
            f"{candidate_name}/"
            f"{date_only}/"
            f"{time_folder}/"
            f"{meeting_id_folder}/"
        )

    # Generic layout (includes Advanced-Training)
    host = canonical_host_name or host_name or "Unknown_Host"

    return (
        f"{department_folder}/"
        f"{host}/"
        f"{year}/"
        f"{month}/"
        f"{candidate_name}/"
        f"{date_only}/"
        f"{time_folder}/"
        f"{meeting_id_folder}/"
    )


def s3_head_object(bucket, key):
    try:
        head = s3.head_object(Bucket=bucket, Key=key)
        return {
            "exists": True,
            "size": int(head.get("ContentLength", -1)),
            "etag": head.get("ETag"),
            "content_type": head.get("ContentType"),
        }
    except ClientError as e:
        code = (e.response or {}).get("Error", {}).get("Code", "")
        if code in {"404", "NoSuchKey", "NotFound"}:
            return {"exists": False}
        if code in {"403", "AccessDenied"}:
            raise RuntimeError(
                f"S3 object check failed with {code} for s3://{bucket}/{key}. "
                f"Make sure IAM allows s3:GetObject on {bucket}/* and s3:ListBucket on {bucket}."
            ) from e
        raise


def s3_object_is_secured(bucket, key, expected_size):
    head = s3_head_object(bucket, key)
    if not head.get("exists"):
        return False
    if not REQUIRE_S3_SIZE_MATCH or expected_size in (None, "", -1):
        return True
    try:
        return int(head.get("size", -1)) == int(expected_size)
    except Exception:
        return False


def init_stats():
    department_stats = {}
    for dept in DEPARTMENT_PRIORITY:
        department_stats[dept] = {
            "hosts_matched": 0,
            "meetings_processed": 0,
            "meetings_without_recording_files": 0,
            "meetings_skipped_missing_ids": 0,
            "recording_files_seen": 0,
            "uploaded": 0,
            "already_in_s3": 0,
            "deleted_from_zoom": 0,
            "delete_skipped_unsecured": 0,
            "delete_failed": 0,
            "skipped_unwanted_type": 0,
            "skipped_not_completed": 0,
            "missing_download_url": 0,
            "size_mismatch_existing": 0,
            "refreshed_download_metadata": 0,
            "participants_manifests": 0,
            "failed": 0,
            "dry_run": 0,
        }

    return {
        "hosts_matched": 0,
        "meetings_processed": 0,
        "meetings_without_recording_files": 0,
        "meetings_skipped_missing_ids": 0,
        "recording_files_seen": 0,
        "uploaded": 0,
        "already_in_s3": 0,
        "deleted_from_zoom": 0,
        "delete_skipped_unsecured": 0,
        "delete_failed": 0,
        "skipped_unwanted_type": 0,
        "skipped_not_completed": 0,
        "missing_download_url": 0,
        "size_mismatch_existing": 0,
        "refreshed_download_metadata": 0,
        "participants_manifests": 0,
        "failed": 0,
        "dry_run": 0,
        "csv_rows": 0,
        "csv_unique_meeting_ids": 0,
        "instances_listed": 0,
        "instances_without_recordings": 0,
        "instances_without_files": 0,
        "meeting_id_fallback_used": 0,
        "meetings_no_recordings": 0,
        "skipped_no_department": 0,
        "skipped_department_filter": 0,
        "department_stats": department_stats,
    }


stats = init_stats()


def bump_stat(key, department=None, amount=1):
    with stats_lock:
        stats[key] += amount
        if department:
            stats["department_stats"][department][key] += amount


def set_hosts_matched(department, count):
    with stats_lock:
        stats["hosts_matched"] += count
        stats["department_stats"][department]["hosts_matched"] = count


def snapshot_stats():
    with stats_lock:
        return json.loads(json.dumps(stats))


def audit_event(event_type, **fields):
    if not AUDIT_LOG_PATH:
        return
    rec = {
        "ts_utc": datetime.now(timezone.utc).isoformat(),
        "event": event_type,
        **fields,
    }
    line = json.dumps(rec, ensure_ascii=False)
    with audit_lock:
        with open(AUDIT_LOG_PATH, "a", encoding="utf-8") as f:
            f.write(line + "\n")


def append_query_params(url, extra_params):
    parts = urlsplit(url)
    existing = dict(parse_qsl(parts.query, keep_blank_values=True))
    for k, v in extra_params.items():
        if v is not None and v != "":
            existing[k] = str(v)
    new_query = urlencode(existing)
    return urlunsplit((parts.scheme, parts.netloc, parts.path, new_query, parts.fragment))


def download_response_looks_invalid(resp):
    content_type = (resp.headers.get("Content-Type") or "").lower()
    if "text/html" in content_type or "application/xhtml" in content_type:
        return True
    return False


def build_download_strategies(token_manager, file_url, detail_tokens):
    strategies = []
    seen = set()

    def add(label, url, headers=None, headers_factory=None, on_401=None):
        key = (
            label,
            url,
            json.dumps(headers or {}, sort_keys=True),
            bool(headers_factory),
        )
        if key in seen:
            return
        seen.add(key)
        strategies.append({
            "label": label,
            "url": url,
            "headers": headers,
            "headers_factory": headers_factory,
            "on_401": on_401,
        })

    download_access_token = (detail_tokens.get("download_access_token") or "").strip()
    recording_access_token = (detail_tokens.get("recording_access_token") or "").strip()

    if download_access_token:
        add(
            "header:download_access_token",
            file_url,
            headers={"Authorization": f"Bearer {download_access_token}"},
        )
        add(
            "query:download_access_token",
            append_query_params(file_url, {"download_access_token": download_access_token}),
        )

    if recording_access_token:
        add(
            "header:recording_access_token",
            file_url,
            headers={"Authorization": f"Bearer {recording_access_token}"},
        )
        add(
            "query:access_token",
            append_query_params(file_url, {"access_token": recording_access_token}),
        )

    add(
        "header:s2s_access_token",
        file_url,
        headers_factory=lambda: zoom_headers_factory(token_manager),
        on_401=zoom_refresh_callback(token_manager),
    )

    return strategies


def open_download_stream(token_manager, file_url, detail_tokens):
    errors = []

    for strat in build_download_strategies(token_manager, file_url, detail_tokens):
        resp = None
        try:
            resp = request_with_retry(
                "GET",
                strat["url"],
                headers=strat.get("headers"),
                headers_factory=strat.get("headers_factory"),
                stream=True,
                timeout=DOWNLOAD_TIMEOUT_SECONDS,
                on_401=strat.get("on_401"),
            )
            if download_response_looks_invalid(resp):
                raise RuntimeError(
                    f"Unexpected HTML response for download using strategy={strat['label']} "
                    f"url={strat['url']}"
                )
            return resp, strat["label"]
        except Exception as e:
            errors.append(f"{strat['label']} failed: {e}")
            if resp is not None:
                try:
                    resp.close()
                except Exception:
                    pass

    raise RuntimeError(" ; ".join(errors) if errors else f"Could not download {file_url}")


def find_recording_file(detail, recording_id, raw_file_type):
    for rf in extract_recording_files(detail):
        rid = str(rf.get("id") or rf.get("recording_id") or "")
        rtype = (rf.get("file_type") or "").upper()
        if rid == str(recording_id) and rtype == raw_file_type:
            return rf
    return None


def is_recording_file_ready(recording_file):
    status = (recording_file.get("status") or "").strip().lower()
    if not status:
        return True
    return status == "completed"


def extract_expected_size(recording_file):
    size = recording_file.get("file_size")
    try:
        return int(size) if size not in (None, "") else None
    except Exception:
        return None


def upload_stream_to_s3(bucket, key, resp):
    content_type = resp.headers.get("Content-Type")
    resp.raw.decode_content = True
    extra_args = {"ContentType": content_type} if content_type else None
    if extra_args:
        s3.upload_fileobj(resp.raw, bucket, key, ExtraArgs=extra_args, Config=S3_TRANSFER_CONFIG)
    else:
        s3.upload_fileobj(resp.raw, bucket, key, Config=S3_TRANSFER_CONFIG)


def upload_recording_once(token_manager, bucket, key, recording_file, detail_tokens):
    expected_size = extract_expected_size(recording_file)
    head = s3_head_object(bucket, key)

    if DRY_RUN:
        print(f"[DRY RUN] Would upload if missing: s3://{bucket}/{key}")
        return {
            "result": "dry_run",
            "expected_size": expected_size,
            "strategy": None,
        }

    if head.get("exists"):
        if s3_object_is_secured(bucket, key, expected_size):
            print(f"Already in S3 and size-validated: s3://{bucket}/{key}")
            return {
                "result": "already_in_s3",
                "expected_size": expected_size,
                "strategy": None,
            }
        print(
            f"Existing S3 object size mismatch or unvalidated; will overwrite: "
            f"s3://{bucket}/{key}; expected_size={expected_size}; existing_size={head.get('size')}"
        )

    download_url = recording_file.get("download_url")
    if not download_url:
        raise RuntimeError("download_url missing")

    resp, strategy = open_download_stream(token_manager, download_url, detail_tokens)
    try:
        upload_stream_to_s3(bucket, key, resp)
    finally:
        try:
            resp.close()
        except Exception:
            pass

    if REQUIRE_S3_SIZE_MATCH and expected_size not in (None, -1):
        if not s3_object_is_secured(bucket, key, expected_size):
            head_after = s3_head_object(bucket, key)
            raise RuntimeError(
                f"Uploaded object size mismatch for s3://{bucket}/{key}; "
                f"expected={expected_size}; actual={head_after.get('size')}"
            )

    print(f"Uploaded to S3 using {strategy}: s3://{bucket}/{key}")
    return {
        "result": "uploaded",
        "expected_size": expected_size,
        "strategy": strategy,
    }


def upload_recording_with_refresh(
    token_manager,
    department_folder,
    bucket,
    key,
    *,
    meeting_id,
    meeting_uuid,
    meeting_start_time,
    recording_id,
    raw_file_type,
    initial_recording_file,
    initial_detail_tokens,
):
    try:
        return upload_recording_once(token_manager, bucket, key, initial_recording_file, initial_detail_tokens)
    except Exception as first_error:
        should_recheck = raw_file_type in TEXTUAL_FILE_TYPES
        if not should_recheck:
            raise

        print(
            f"Initial download failed for textual file; will recheck metadata: "
            f"meeting_id={meeting_id} meeting_uuid={meeting_uuid} recording_id={recording_id} "
            f"file_type={raw_file_type} error={first_error}"
        )

        sleep_s = TRANSCRIPT_RECHECK_INITIAL_SLEEP_SECONDS
        last_error = first_error

        for attempt in range(1, TRANSCRIPT_RECHECK_ATTEMPTS + 1):
            print(
                f"[TEXT RECHECK] attempt={attempt}/{TRANSCRIPT_RECHECK_ATTEMPTS}; "
                f"sleep={sleep_s}s; meeting_id={meeting_id}; recording_id={recording_id}; file_type={raw_file_type}"
            )
            time.sleep(sleep_s)
            sleep_s = min(max(sleep_s * 2, 1), TRANSCRIPT_RECHECK_MAX_SLEEP_SECONDS)

            try:
                detail = get_recording_detail(
                    token_manager,
                    meeting_uuid,
                    meeting_id,
                    requested_start_time=meeting_start_time,
                )
                detail_tokens = extract_download_tokens(detail)
                refreshed_rf = find_recording_file(detail, recording_id, raw_file_type)

                if not refreshed_rf:
                    last_error = RuntimeError(
                        f"Recording file disappeared from refreshed metadata: "
                        f"recording_id={recording_id} file_type={raw_file_type}"
                    )
                    continue

                if not is_recording_file_ready(refreshed_rf):
                    last_error = RuntimeError(
                        f"Recording file still not completed after refresh: recording_id={recording_id} "
                        f"file_type={raw_file_type} status={refreshed_rf.get('status')}"
                    )
                    continue

                if not refreshed_rf.get("download_url"):
                    last_error = RuntimeError(
                        f"Recording file still missing download_url after refresh: "
                        f"recording_id={recording_id} file_type={raw_file_type}"
                    )
                    continue

                bump_stat("refreshed_download_metadata", department_folder, 1)
                return upload_recording_once(token_manager, bucket, key, refreshed_rf, detail_tokens)

            except Exception as e:
                last_error = e
                print(
                    f"[TEXT RECHECK FAILED] meeting_id={meeting_id}; recording_id={recording_id}; "
                    f"file_type={raw_file_type}; error={e}"
                )

        raise RuntimeError(f"Textual file never became downloadable: {last_error}") from first_error


def transfer_recording_file(
    token_manager,
    department_folder,
    *,
    meeting_id,
    meeting_uuid,
    meeting_start_time,
    recording_id,
    raw_file_type,
    s3_key,
    recording_file,
    detail_tokens,
):
    try:
        initial_expected_size = extract_expected_size(recording_file)
        preexisting = s3_head_object(S3_BUCKET_NAME, s3_key)

        if preexisting.get("exists") and REQUIRE_S3_SIZE_MATCH and initial_expected_size not in (None, -1):
            if int(preexisting.get("size", -1)) != int(initial_expected_size):
                bump_stat("size_mismatch_existing", department_folder, 1)

        upload_info = upload_recording_with_refresh(
            token_manager,
            department_folder,
            S3_BUCKET_NAME,
            s3_key,
            meeting_id=meeting_id,
            meeting_uuid=meeting_uuid,
            meeting_start_time=meeting_start_time,
            recording_id=recording_id,
            raw_file_type=raw_file_type,
            initial_recording_file=recording_file,
            initial_detail_tokens=detail_tokens,
        )

        result = upload_info["result"]
        final_expected_size = upload_info.get("expected_size")

        if result == "uploaded":
            bump_stat("uploaded", department_folder, 1)
        elif result == "already_in_s3":
            bump_stat("already_in_s3", department_folder, 1)
        elif result == "dry_run":
            bump_stat("dry_run", department_folder, 1)

        audit_event(
            "transfer_result",
            department=department_folder,
            meeting_id=meeting_id,
            meeting_uuid=str(meeting_uuid),
            recording_id=str(recording_id),
            file_type=raw_file_type,
            s3_bucket=S3_BUCKET_NAME,
            s3_key=s3_key,
            result=result,
            expected_size=final_expected_size,
        )
        return {
            "result": result,
            "expected_size": final_expected_size,
        }

    except Exception as e:
        bump_stat("failed", department_folder, 1)
        audit_event(
            "transfer_failed",
            department=department_folder,
            meeting_id=meeting_id,
            meeting_uuid=str(meeting_uuid),
            recording_id=str(recording_id),
            file_type=raw_file_type,
            s3_bucket=S3_BUCKET_NAME,
            s3_key=s3_key,
            error=str(e),
        )
        print(f"Transfer failed for s3://{S3_BUCKET_NAME}/{s3_key}: {e}")
        return {
            "result": "failed",
            "expected_size": extract_expected_size(recording_file),
        }


def delete_recording_file(token_manager, meeting_id, meeting_uuid, recording_id):
    if DRY_RUN or not DELETE_FROM_ZOOM:
        print(
            f"[DRY RUN] Would delete Zoom recording file meeting_id={meeting_id} "
            f"meeting_uuid={meeting_uuid} recording_id={recording_id} action={DELETE_ACTION}"
        )
        return "dry_run"

    if DELETE_ACTION not in {"trash", "delete"}:
        raise RuntimeError("DELETE_ACTION must be either 'trash' or 'delete'")

    rec_id = quote(str(recording_id), safe="")
    candidates = []
    if meeting_uuid:
        candidates.append(("meeting_uuid", encode_zoom_uuid(meeting_uuid)))
    if meeting_id:
        candidates.append(("meeting_id", str(meeting_id)))

    errors = []
    for label, meeting_ref in candidates:
        try:
            status = zoom_delete(
                token_manager,
                f"/meetings/{meeting_ref}/recordings/{rec_id}",
                params={"action": DELETE_ACTION},
            )
            print(
                f"Deleted Zoom recording file using {label}={meeting_ref}; "
                f"recording_id={recording_id}; action={DELETE_ACTION}; status={status}"
            )
            return "deleted"
        except Exception as e:
            errors.append(f"{label} failed: {e}")
            print(f"Delete using {label} failed for recording_id={recording_id}: {e}")

    raise RuntimeError(" ; ".join(errors) if errors else "Could not delete recording file")


def write_participants_manifest(base_prefix, department_folder, meeting, storage_info, host_display_name):
    """NEW: Advanced-Training only — full candidate list to participants.json."""
    all_candidates = storage_info.get("all_candidates")
    if not all_candidates:
        return

    key = f"{base_prefix}participants.json"

    if DRY_RUN:
        print(f"[DRY RUN] Would write participants.json ({len(all_candidates)} candidates): s3://{S3_BUCKET_NAME}/{key}")
        return

    try:
        manifest = {
            "meeting_id": str(meeting.get("id")),
            "topic": meeting.get("topic", "") or "",
            "department": department_folder,
            "host": host_display_name,
            "host_email": "",
            "start_time": meeting.get("start_time", "") or "",
            "candidate_count": len(all_candidates),
            "candidates": all_candidates,
        }
        s3.put_object(
            Bucket=S3_BUCKET_NAME,
            Key=key,
            Body=json.dumps(manifest, indent=2).encode(),
            ContentType="application/json",
        )
        bump_stat("participants_manifests", department_folder, 1)
        print(f"participants.json written ({len(all_candidates)} candidates): s3://{S3_BUCKET_NAME}/{key}")
    except Exception as exc:
        print(f"Failed writing participants.json for {base_prefix}: {exc}")


# ══════════════════════════════════════════════════════════════════════════════
#  CSV-DRIVEN DRIVER
#
#  Flow:  Zoom admin CSV (Host, Topic, ID)
#           -> unique meeting IDs
#           -> /past_meetings/{id}/instances  (ALL occurrences / UUIDs)
#           -> /meetings/{uuid}/recordings    (files for each occurrence)
#           -> S3 secured?  yes -> delete from Zoom (if enabled)
#                           no  -> upload -> size-verify -> delete (if enabled)
# ══════════════════════════════════════════════════════════════════════════════

def zoom_get_optional(token_manager, path, params=None):
    """zoom_get, but returns None on 404 (recording/instance/user not found)."""
    try:
        return zoom_get(token_manager, path, params=params)
    except requests.HTTPError as e:
        resp = getattr(e, "response", None)
        if resp is not None and resp.status_code == 404:
            return None
        if "404" in str(e):
            return None
        raise


def parse_recordings_csv(path):
    """
    Zoom admin export columns: Host, Topic, ID  (ID like '956 2591 3483').
    Returns (total_rows, ordered dict {meeting_id_digits: {'host_email','topic'}}).
    Header matching is case-insensitive and tolerant of extra columns.
    """
    unique = {}
    total = 0

    with open(path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        fields = {(k or "").strip().lower(): k for k in (reader.fieldnames or [])}

        def col(*names):
            for n in names:
                if n in fields:
                    return fields[n]
            return None

        id_col = col("id", "meeting id", "meeting_id")
        host_col = col("host", "host email", "email")
        topic_col = col("topic", "meeting topic", "name")

        if not id_col:
            raise RuntimeError(
                f"CSV {path} has no ID column. Found columns: {list(fields.keys())}"
            )

        for row in reader:
            total += 1
            mid = normalize_meeting_id_value(row.get(id_col))
            if not mid:
                continue
            host_email = (row.get(host_col) or "").strip().lower() if host_col else ""
            topic = (row.get(topic_col) or "").strip() if topic_col else ""
            if mid not in unique:
                unique[mid] = {"host_email": host_email, "topic": topic}

    return total, unique


def get_meeting_instances(token_manager, meeting_id):
    """All past occurrences (UUIDs) of a meeting ID. Empty list if none/error."""
    data = zoom_get_optional(token_manager, f"/past_meetings/{meeting_id}/instances")
    if not data:
        return []
    return [m for m in (data.get("meetings") or []) if isinstance(m, dict)]


def fetch_recordings_by_uuid(token_manager, meeting_uuid):
    return zoom_get_optional(
        token_manager, f"/meetings/{encode_zoom_uuid(meeting_uuid)}/recordings"
    )


def fetch_recordings_by_meeting_id(token_manager, meeting_id):
    return zoom_get_optional(token_manager, f"/meetings/{meeting_id}/recordings")


# ── Zoom user cache (dept + name resolution; deleted users -> None) ───────────
_USER_CACHE = {}
_USER_CACHE_LOCK = threading.Lock()


def get_zoom_user(token_manager, host_id, fallback_email=""):
    key = str(host_id or "") + "|" + (fallback_email or "").strip().lower()
    with _USER_CACHE_LOCK:
        if key in _USER_CACHE:
            return _USER_CACHE[key]

    user = None
    for ident in (host_id, (fallback_email or "").strip().lower()):
        if not ident:
            continue
        try:
            user = zoom_get_optional(
                token_manager, f"/users/{quote(str(ident), safe='')}"
            )
        except Exception as e:
            print(f"User lookup failed for {ident}: {e}")
            user = None
        if user:
            break

    with _USER_CACHE_LOCK:
        _USER_CACHE[key] = user
    return user


# ── Per-instance report CSV ────────────────────────────────────────────────────
REPORT_FIELDS = [
    "meeting_id", "uuid", "start_time", "department", "host", "s3_prefix",
    "files_seen", "uploaded", "already_in_s3", "dry_run", "failed",
    "deleted_from_zoom", "delete_skipped", "status",
]
_REPORT_LOCK = threading.Lock()
_REPORT_STARTED = False


def write_report_row(**fields):
    global _REPORT_STARTED
    if not REPORT_PATH:
        return
    row = {k: fields.get(k, "") for k in REPORT_FIELDS}
    with _REPORT_LOCK:
        new_file = not _REPORT_STARTED and not os.path.exists(REPORT_PATH)
        with open(REPORT_PATH, "a", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=REPORT_FIELDS)
            if new_file:
                writer.writeheader()
            writer.writerow(row)
        _REPORT_STARTED = True


def process_instance(
    token_manager,
    transfer_executor,
    transfer_semaphore,
    detail,
    csv_row,
):
    """One recording occurrence: resolve dept + path, secure files in S3, delete."""
    meeting_id = detail.get("id") or csv_row.get("meeting_id")
    meeting_uuid = detail.get("uuid") or ""
    start_time = detail.get("start_time", "") or ""
    topic = (detail.get("topic") or csv_row.get("topic") or "").strip()
    host_id = detail.get("host_id")
    csv_host_email = csv_row.get("host_email", "")

    print("\n" + "=" * 100)
    print(f"Meeting ID   : {meeting_id}")
    print(f"Meeting UUID : {meeting_uuid}")
    print(f"Start time   : {start_time}")
    print(f"Topic        : {topic}")

    recording_files = extract_recording_files(detail)
    detail_tokens = extract_download_tokens(detail)

    if not recording_files:
        bump_stat("instances_without_files")
        write_report_row(
            meeting_id=meeting_id, uuid=meeting_uuid, start_time=start_time,
            status="no_files_in_instance",
        )
        print("No recording files in this instance — skipping")
        return

    # ── Resolve host user -> department ────────────────────────────────────
    user = get_zoom_user(token_manager, host_id, csv_host_email)
    raw_dept = ((user or {}).get("dept") or "").strip()
    department_folder = normalize_department(raw_dept)

    if not department_folder:
        if INCLUDE_OTHER_DEPARTMENT:
            department_folder = OTHER_DEPARTMENT_FOLDER
            print(f"[OTHER] host={csv_host_email or host_id} raw_dept={raw_dept!r} -> {OTHER_DEPARTMENT_FOLDER}")
        else:
            bump_stat("skipped_no_department")
            write_report_row(
                meeting_id=meeting_id, uuid=meeting_uuid, start_time=start_time,
                host=csv_host_email, status="skipped_no_department",
            )
            print(f"Skipping — no recognised department (raw_dept={raw_dept!r})")
            return

    if department_folder not in TARGET_DEPARTMENTS:
        bump_stat("skipped_department_filter")
        write_report_row(
            meeting_id=meeting_id, uuid=meeting_uuid, start_time=start_time,
            department=department_folder, host=csv_host_email,
            status="skipped_department_filter",
        )
        return

    host_email = ((user or {}).get("email") or csv_host_email or "").strip().lower()
    if user:
        host_name = build_host_name(user)
    else:
        host_name = sanitize_name(
            (csv_host_email.split("@")[0] if csv_host_email else "") or "Unknown_Host"
        )
        print(f"Host user not found in Zoom (deleted?) — using '{host_name}' from CSV")

    print(f"Department   : {department_folder}")
    print(f"Host         : {host_name}")

    # ── Participants (same rules as the backfill) ──────────────────────────
    participants = []
    need_participants = not SKIP_PARTICIPANTS_LOOKUP
    if department_folder == "Interview-Success" and parse_interview_success_topic(topic):
        need_participants = False
    if department_folder in {"HR", "Advanced-Training"}:
        need_participants = True
    elif department_folder == "Training" and not parse_training_topic(topic):
        need_participants = True

    if need_participants and meeting_uuid:
        participants = list_all_participants(token_manager, meeting_uuid)

    storage_info = resolve_storage_info(
        department_folder=department_folder,
        topic=topic,
        participants=participants,
        host_email=host_email,
        meeting_id=meeting_id,
        host_name=host_name,
    )
    candidate_name = storage_info["candidate_name"]
    company_name = storage_info["company_name"]
    round_name = storage_info["round_name"]
    trainer_name = storage_info["trainer_name"]
    hr_person_name = storage_info["hr_person_name"]
    canonical_host_name = storage_info.get("canonical_host_name")

    year, month, date_only, time_folder = build_path_parts(start_time)
    base_prefix = build_base_prefix(
        department_folder=department_folder,
        host_name=host_name,
        year=year,
        month=month,
        candidate_name=candidate_name,
        date_only=date_only,
        time_folder=time_folder,
        company_name=company_name,
        round_name=round_name,
        meeting_id=meeting_id,
        trainer_name=trainer_name,
        hr_person_name=hr_person_name,
        canonical_host_name=canonical_host_name,
    )

    print(f"S3 base prefix: s3://{S3_BUCKET_NAME}/{base_prefix}")
    bump_stat("meetings_processed", department_folder, 1)

    write_participants_manifest(
        base_prefix=base_prefix,
        department_folder=department_folder,
        meeting=detail,
        storage_info=storage_info,
        host_display_name=canonical_host_name or host_name,
    )

    # ── Queue transfers ────────────────────────────────────────────────────
    jobs = []
    files_seen = 0
    for idx, rf in enumerate(recording_files, start=1):
        bump_stat("recording_files_seen", department_folder, 1)
        files_seen += 1

        raw_file_type = (rf.get("file_type") or "UNKNOWN").upper()
        if not file_type_allowed(raw_file_type):
            bump_stat("skipped_unwanted_type", department_folder, 1)
            print(f"Skipping unwanted file type: {raw_file_type}")
            continue

        if not is_recording_file_ready(rf):
            bump_stat("skipped_not_completed", department_folder, 1)
            print(f"Skipping not-completed file: type={raw_file_type}, status={rf.get('status')}")
            continue

        download_url = rf.get("download_url")
        if not download_url:
            bump_stat("missing_download_url", department_folder, 1)
            print(f"Skipping file because download_url is missing for file_type={raw_file_type}")
            continue

        recording_id = rf.get("id") or rf.get("recording_id") or f"{meeting_id}_{idx}"
        file_extension = extract_extension(rf)
        filename = build_recording_filename(recording_id, file_extension)
        s3_key = f"{base_prefix}{raw_file_type}/{filename}"

        transfer_semaphore.acquire()
        future = transfer_executor.submit(
            transfer_recording_file,
            token_manager,
            department_folder,
            meeting_id=meeting_id,
            meeting_uuid=meeting_uuid,
            meeting_start_time=start_time,
            recording_id=recording_id,
            raw_file_type=raw_file_type,
            s3_key=s3_key,
            recording_file=rf,
            detail_tokens=detail_tokens,
        )

        def _release(_f, sem=transfer_semaphore):
            try:
                _f.result()
            except Exception:
                pass
            finally:
                sem.release()

        future.add_done_callback(_release)
        jobs.append({
            "future": future,
            "recording_id": recording_id,
            "file_type": raw_file_type,
            "s3_key": s3_key,
        })

    # ── Wait + verified delete gate (per file) ─────────────────────────────
    ct = {"uploaded": 0, "already_in_s3": 0, "dry_run": 0, "failed": 0,
          "deleted_from_zoom": 0, "delete_skipped": 0}

    for job in jobs:
        try:
            job_result = job["future"].result()
        except Exception:
            job_result = {"result": "failed", "expected_size": None}

        result = job_result.get("result", "failed")
        final_expected_size = job_result.get("expected_size")

        if result in ct:
            ct[result] += 1

        if result not in {"uploaded", "already_in_s3", "dry_run"}:
            ct["delete_skipped"] += 1
            bump_stat("delete_skipped_unsecured", department_folder, 1)
            print(
                f"Zoom delete skipped because file is not secured in S3 yet: "
                f"file_type={job['file_type']} s3_key={job['s3_key']} result={result}"
            )
            audit_event(
                "delete_skipped_unsecured",
                department=department_folder, meeting_id=meeting_id,
                meeting_uuid=str(meeting_uuid), recording_id=str(job["recording_id"]),
                file_type=job["file_type"], s3_key=job["s3_key"], result=result,
            )
            continue

        if REQUIRE_S3_SIZE_MATCH and result != "dry_run":
            if not s3_object_is_secured(S3_BUCKET_NAME, job["s3_key"], final_expected_size):
                ct["delete_skipped"] += 1
                bump_stat("delete_skipped_unsecured", department_folder, 1)
                print(
                    f"Zoom delete skipped because S3 object failed final size check: "
                    f"file_type={job['file_type']} s3_key={job['s3_key']} expected_size={final_expected_size}"
                )
                audit_event(
                    "delete_skipped_size_mismatch",
                    department=department_folder, meeting_id=meeting_id,
                    meeting_uuid=str(meeting_uuid), recording_id=str(job["recording_id"]),
                    file_type=job["file_type"], s3_key=job["s3_key"],
                    expected_size=final_expected_size,
                )
                continue

        try:
            delete_result = delete_recording_file(
                token_manager,
                meeting_id=meeting_id,
                meeting_uuid=meeting_uuid,
                recording_id=job["recording_id"],
            )
            if delete_result == "deleted":
                ct["deleted_from_zoom"] += 1
                bump_stat("deleted_from_zoom", department_folder, 1)
            elif delete_result == "dry_run":
                bump_stat("dry_run", department_folder, 1)

            audit_event(
                "delete_result",
                department=department_folder, meeting_id=meeting_id,
                meeting_uuid=str(meeting_uuid), recording_id=str(job["recording_id"]),
                file_type=job["file_type"], s3_key=job["s3_key"],
                result=delete_result, delete_action=DELETE_ACTION,
            )
        except Exception as e:
            ct["delete_skipped"] += 1
            bump_stat("delete_failed", department_folder, 1)
            audit_event(
                "delete_failed",
                department=department_folder, meeting_id=meeting_id,
                meeting_uuid=str(meeting_uuid), recording_id=str(job["recording_id"]),
                file_type=job["file_type"], s3_key=job["s3_key"],
                error=str(e), delete_action=DELETE_ACTION,
            )
            print(
                f"Zoom delete failed for recording_id={job['recording_id']} "
                f"file_type={job['file_type']} s3_key={job['s3_key']}: {e}"
            )

    if ct["failed"] > 0 or ct["delete_skipped"] > 0:
        status = "attention_needed"
    elif DRY_RUN:
        status = "dry_run_ok"
    else:
        status = "ok"

    write_report_row(
        meeting_id=meeting_id, uuid=meeting_uuid, start_time=start_time,
        department=department_folder, host=host_name, s3_prefix=base_prefix,
        files_seen=files_seen, uploaded=ct["uploaded"],
        already_in_s3=ct["already_in_s3"], dry_run=ct["dry_run"],
        failed=ct["failed"], deleted_from_zoom=ct["deleted_from_zoom"],
        delete_skipped=ct["delete_skipped"], status=status,
    )


def process_meeting_id(
    token_manager,
    transfer_executor,
    transfer_semaphore,
    meeting_id,
    csv_row,
):
    """One CSV meeting ID -> ALL its recording occurrences (UUIDs)."""
    try:
        print("\n" + "#" * 100)
        print(f"CSV MEETING ID: {meeting_id}  host={csv_row.get('host_email')}  topic={csv_row.get('topic')!r}")

        instances = get_meeting_instances(token_manager, meeting_id)
        bump_stat("instances_listed", amount=len(instances))

        processed = 0
        seen_uuids = set()

        for inst in instances:
            uuid = inst.get("uuid")
            if not uuid or uuid in seen_uuids:
                continue
            seen_uuids.add(uuid)

            detail = fetch_recordings_by_uuid(token_manager, uuid)
            if detail is None:
                bump_stat("instances_without_recordings")
                continue

            process_instance(
                token_manager, transfer_executor, transfer_semaphore,
                detail, csv_row,
            )
            processed += 1

        # Fallback: instances API empty/blocked -> latest recording by meeting ID
        if processed == 0 and not instances:
            detail = fetch_recordings_by_meeting_id(token_manager, meeting_id)
            if detail and extract_recording_files(detail):
                bump_stat("meeting_id_fallback_used")
                print(f"Instances API empty for {meeting_id}; using direct meeting-ID lookup")
                process_instance(
                    token_manager, transfer_executor, transfer_semaphore,
                    detail, csv_row,
                )
                processed += 1

        if processed == 0:
            bump_stat("meetings_no_recordings")
            write_report_row(
                meeting_id=meeting_id, host=csv_row.get("host_email", ""),
                status="no_recordings_found",
            )
            print(f"No recordings found anywhere for CSV meeting ID {meeting_id}")

    except Exception as e:
        bump_stat("failed")
        write_report_row(
            meeting_id=meeting_id, host=csv_row.get("host_email", ""),
            status=f"error: {e}",
        )
        print(f"Meeting ID {meeting_id} failed: {e}")


def main():
    print("=== CSV -> ZOOM CLOUD -> S3 VERIFY -> OPTIONAL ZOOM DELETE ===")
    print(f"AWS_REGION                        = {AWS_REGION}")
    print(f"ZOOM_SECRET_NAME                  = {ZOOM_SECRET_NAME}")
    print(f"S3_BUCKET_NAME                    = {S3_BUCKET_NAME}")
    print(f"CSV_PATH                          = {CSV_PATH}")
    print(f"REPORT_PATH                       = {REPORT_PATH}")
    print(f"TARGET_DEPARTMENTS                = {TARGET_DEPARTMENTS}")
    print(f"ONLY_HOST_EMAIL                   = {ONLY_HOST_EMAIL or '(all)'}")
    print(f"ONLY_MEETING_ID                   = {ONLY_MEETING_ID or '(all)'}")
    print(f"UPLOAD_FILE_TYPES                 = {'ALL' if UPLOAD_ALL_FILE_TYPES else sorted(ALLOWED_FILE_TYPES)}")
    print(f"DRY_RUN                           = {DRY_RUN}")
    print(f"DELETE_FROM_ZOOM                  = {DELETE_FROM_ZOOM}")
    print(f"DELETE_ACTION                     = {DELETE_ACTION}")
    print(f"REQUIRE_S3_SIZE_MATCH             = {REQUIRE_S3_SIZE_MATCH}")
    print(f"INCLUDE_OTHER_DEPARTMENT          = {INCLUDE_OTHER_DEPARTMENT}")
    print(f"SF_LOOKUP_ENABLED                 = {SF_LOOKUP_ENABLED}")
    print(f"MEETING_WORKERS                   = {MEETING_WORKERS}")
    print(f"TRANSFER_WORKERS                  = {TRANSFER_WORKERS}")
    print(f"MAX_PENDING_TRANSFERS             = {MAX_PENDING_TRANSFERS}")
    print(f"AUDIT_LOG_PATH                    = {AUDIT_LOG_PATH or '(disabled)'}")

    if DELETE_ACTION not in {"trash", "delete"}:
        raise RuntimeError("DELETE_ACTION must be either 'trash' or 'delete'")

    if not os.path.exists(CSV_PATH):
        raise RuntimeError(
            f"CSV file not found: {CSV_PATH} — put the Zoom export next to this "
            f"script or set CSV_PATH in .env"
        )

    total_rows, unique_meetings = parse_recordings_csv(CSV_PATH)
    bump_stat("csv_rows", amount=total_rows)
    bump_stat("csv_unique_meeting_ids", amount=len(unique_meetings))
    print(f"csv_rows                          = {total_rows}")
    print(f"csv_unique_meeting_ids            = {len(unique_meetings)}")

    if ONLY_HOST_EMAIL:
        unique_meetings = {
            mid: info for mid, info in unique_meetings.items()
            if info.get("host_email") == ONLY_HOST_EMAIL
        }
        print(f"after ONLY_HOST_EMAIL filter      = {len(unique_meetings)}")

    if ONLY_MEETING_ID:
        want = normalize_meeting_id_value(ONLY_MEETING_ID)
        unique_meetings = {mid: info for mid, info in unique_meetings.items() if mid == want}
        print(f"after ONLY_MEETING_ID filter      = {len(unique_meetings)}")

    secret_obj = get_zoom_secret()
    token_manager = ZoomTokenManager(secret_obj)

    transfer_semaphore = threading.BoundedSemaphore(MAX_PENDING_TRANSFERS)

    with ThreadPoolExecutor(max_workers=TRANSFER_WORKERS) as transfer_executor:
        with ThreadPoolExecutor(max_workers=MEETING_WORKERS) as meeting_executor:
            futures = [
                meeting_executor.submit(
                    process_meeting_id,
                    token_manager,
                    transfer_executor,
                    transfer_semaphore,
                    meeting_id,
                    csv_row,
                )
                for meeting_id, csv_row in unique_meetings.items()
            ]

            done = 0
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception as e:
                    bump_stat("failed")
                    print(f"Meeting processing failed: {e}")
                done += 1
                if done % 100 == 0:
                    print(f"\n>>> PROGRESS: {done}/{len(futures)} meeting IDs processed <<<\n")

    print("\n=== FINAL SUMMARY ===")
    print(json.dumps(snapshot_stats(), indent=2))
    print(f"\nPer-meeting report: {REPORT_PATH}")


if __name__ == "__main__":
    main()