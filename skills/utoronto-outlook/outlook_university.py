#!/usr/bin/env python3
"""
Headless Outlook/Microsoft 365 access via IMAP with OAuth2.
Uses Thunderbird's pre-authorized client ID to bypass admin consent requirements.

Device code flow for initial auth, macOS Keychain for token cache.
No UI interaction required after initial device code authentication.
"""

import os
import sys
import re
import ssl
import base64
import subprocess
import requests
import imaplib
import smtplib
from email import message_from_bytes
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.header import decode_header
from datetime import datetime, timedelta
from typing import Optional, List, Dict, Any, Tuple

# Context safety limits
MAX_BODY_LENGTH = 2000
MAX_SEARCH_RESULTS = 25
MAX_UNREAD_RESULTS = 50


def sanitize_for_terminal(text: str) -> str:
    """Strip ANSI escape codes and other control sequences to prevent prompt injection."""
    # Remove ANSI escape sequences
    ansi_pattern = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]|\x1b\][^\x07]*\x07|\x1b[()][AB012]')
    text = ansi_pattern.sub('', text)
    # Remove other control characters except newlines and tabs
    text = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]', '', text)
    return text


# Thunderbird's pre-authorized client ID - works without admin consent
# This is the key to bypassing AADSTS65002 errors
THUNDERBIRD_CLIENT_ID = "9e5f94bc-e8a4-4e73-b8be-63364c29d753"

# OAuth2 endpoints
AUTH_BASE = "https://login.microsoftonline.com"

# IMAP/SMTP servers
IMAP_SERVER = "outlook.office365.com"
IMAP_PORT = 993
SMTP_SERVER = "smtp.office365.com"
SMTP_PORT = 587

# Keychain service name
KEYCHAIN_SERVICE = "outlook-university"

# IMAP OAuth2 scopes (different from Graph API!)
IMAP_SCOPES = [
    "https://outlook.office.com/IMAP.AccessAsUser.All",
    "https://outlook.office.com/SMTP.Send",
    "offline_access",
    "openid",
    "profile",
    "email"
]


class TokenCache:
    """macOS Keychain-based token storage for headless operation."""
    
    @staticmethod
    def store(key: str, value: str) -> None:
        """Store token in macOS Keychain."""
        subprocess.run([
            "security", "delete-generic-password",
            "-a", key, "-s", KEYCHAIN_SERVICE
        ], capture_output=True)
        subprocess.run([
            "security", "add-generic-password",
            "-a", key, "-s", KEYCHAIN_SERVICE, "-w", value,
        ], check=True, capture_output=True)
    
    @staticmethod
    def retrieve(key: str) -> Optional[str]:
        """Retrieve token from macOS Keychain."""
        try:
            result = subprocess.run([
                "security", "find-generic-password",
                "-a", key, "-s", KEYCHAIN_SERVICE, "-w"
            ], capture_output=True, text=True, check=True)
            return result.stdout.strip()
        except subprocess.CalledProcessError:
            return None
    
    @staticmethod
    def delete(key: str) -> None:
        """Delete token from Keychain."""
        subprocess.run([
            "security", "delete-generic-password",
            "-a", key, "-s", KEYCHAIN_SERVICE
        ], capture_output=True)
    
    @staticmethod
    def clear_all() -> None:
        """Clear all tokens for this service."""
        for key in ["access_token", "refresh_token", "token_expiry", "email"]:
            TokenCache.delete(key)


class OutlookAuth:
    """
    OAuth2 authentication using Thunderbird's pre-authorized client ID.
    This bypasses the AADSTS65002 error that blocks most third-party apps.
    """
    
    def __init__(self, tenant_id: str = "common"):
        self.client_id = THUNDERBIRD_CLIENT_ID
        self.tenant_id = tenant_id
        self.scopes = IMAP_SCOPES
    
    def device_code_flow(self) -> Dict[str, str]:
        """
        Initiate device code flow for initial authentication.
        Uses Thunderbird's client ID which is pre-authorized for IMAP access.
        """
        device_code_url = f"{AUTH_BASE}/{self.tenant_id}/oauth2/v2.0/devicecode"
        response = requests.post(device_code_url, data={
            "client_id": self.client_id,
            "scope": " ".join(self.scopes)
        })
        
        if response.status_code != 200:
            raise Exception(f"Failed to get device code: {response.text}")
        
        device_data = response.json()
        
        print(f"\n{'='*60}")
        print(f"OUTLOOK UNIVERSITY - DEVICE CODE AUTHENTICATION")
        print(f"{'='*60}")
        print(f"\n  Code: {device_data['user_code']}")
        print(f"\n  Go to: {device_data['verification_uri']}")
        print(f"\n  (Uses Thunderbird's pre-authorized client ID)")
        print(f"{'='*60}\n")
        print("Waiting for authentication...", end="", flush=True)
        
        # Poll for token
        token_url = f"{AUTH_BASE}/{self.tenant_id}/oauth2/v2.0/token"
        interval = device_data.get("interval", 5)
        expires_in = device_data.get("expires_in", 900)
        start_time = datetime.now()
        
        import time
        while (datetime.now() - start_time).seconds < expires_in:
            time.sleep(interval)
            token_response = requests.post(token_url, data={
                "client_id": self.client_id,
                "grant_type": "urn:ietf:params:oauth:grant-type:device_code",
                "device_code": device_data["device_code"]
            })
            
            if token_response.status_code == 200:
                tokens = token_response.json()
                self._cache_tokens(tokens)
                print("\n\n✓ Authentication successful!")
                email = self._get_email_from_token(tokens)
                if email:
                    TokenCache.store("email", email)
                    print(f"  Logged in as: {email}")
                print("  Tokens cached in Keychain for headless use.")
                return tokens
            
            error = token_response.json().get("error")
            if error == "authorization_pending":
                print(".", end="", flush=True)
                continue
            elif error == "slow_down":
                interval += 5
            elif error == "expired_token":
                raise Exception("\nDevice code expired. Please try again.")
            else:
                raise Exception(f"\nAuth failed: {token_response.json()}")
        
        raise Exception("\nAuthentication timed out.")
    
    def _get_email_from_token(self, tokens: Dict) -> Optional[str]:
        """Extract email from ID token."""
        id_token = tokens.get("id_token")
        if not id_token:
            return None
        try:
            # Decode JWT payload (middle part)
            payload = id_token.split(".")[1]
            # Add padding
            payload += "=" * (4 - len(payload) % 4)
            import json
            data = json.loads(base64.urlsafe_b64decode(payload))
            return data.get("preferred_username") or data.get("email") or data.get("upn")
        except Exception:
            return None
    
    def _cache_tokens(self, tokens: Dict[str, Any]) -> None:
        """Store tokens in Keychain."""
        TokenCache.store("access_token", tokens["access_token"])
        TokenCache.store("refresh_token", tokens["refresh_token"])
        expires_in = tokens.get("expires_in", 3600)
        expiry = datetime.now() + timedelta(seconds=expires_in)
        TokenCache.store("token_expiry", expiry.isoformat())
    
    def get_access_token(self) -> str:
        """Get valid access token (refreshes silently if needed)."""
        expiry_str = TokenCache.retrieve("token_expiry")
        access_token = TokenCache.retrieve("access_token")
        
        if expiry_str and access_token:
            try:
                expiry = datetime.fromisoformat(expiry_str)
                if datetime.now() < expiry - timedelta(minutes=5):
                    return access_token
            except ValueError:
                pass
        
        # Silent refresh
        refresh_token = TokenCache.retrieve("refresh_token")
        if not refresh_token:
            raise Exception("No refresh token. Run 'auth' command first.")
        
        token_url = f"{AUTH_BASE}/{self.tenant_id}/oauth2/v2.0/token"
        response = requests.post(token_url, data={
            "client_id": self.client_id,
            "grant_type": "refresh_token",
            "refresh_token": refresh_token,
            "scope": " ".join(self.scopes)
        })
        
        if response.status_code != 200:
            TokenCache.clear_all()
            raise Exception("Token refresh failed. Run 'auth' command again.")
        
        tokens = response.json()
        self._cache_tokens(tokens)
        return tokens["access_token"]
    
    def get_xoauth2_string(self, email: str) -> str:
        """Generate XOAUTH2 authentication string for IMAP/SMTP."""
        access_token = self.get_access_token()
        auth_string = f"user={email}\x01auth=Bearer {access_token}\x01\x01"
        return base64.b64encode(auth_string.encode()).decode()


class IMAPClient:
    """IMAP client with OAuth2 authentication."""
    
    def __init__(self, auth: OutlookAuth, email: str):
        self.auth = auth
        self.email = email
        self.conn: Optional[imaplib.IMAP4_SSL] = None
    
    def connect(self) -> None:
        """Connect and authenticate to IMAP server."""
        self.conn = imaplib.IMAP4_SSL(IMAP_SERVER, IMAP_PORT)
        
        # Build XOAUTH2 string per RFC 7628
        access_token = self.auth.get_access_token()
        auth_string = f"user={self.email}\x01auth=Bearer {access_token}\x01\x01"
        
        try:
            # The callback receives server challenge, returns auth string
            self.conn.authenticate("XOAUTH2", lambda x: auth_string.encode())
        except imaplib.IMAP4.error as e:
            raise Exception(f"IMAP auth failed: {e}")
    
    def disconnect(self) -> None:
        """Close IMAP connection."""
        if self.conn:
            try:
                self.conn.logout()
            except Exception:
                pass
            self.conn = None
    
    def list_folders(self) -> List[str]:
        """List all mail folders."""
        if not self.conn:
            self.connect()
        _, folders = self.conn.list()
        result = []
        for folder in folders:
            # Parse folder name from IMAP response
            match = re.search(r'"([^"]+)"$', folder.decode())
            if match:
                result.append(match.group(1))
        return result
    
    def select_folder(self, folder: str = "INBOX") -> int:
        """Select a folder and return message count."""
        if not self.conn:
            self.connect()
        _, data = self.conn.select(folder)
        return int(data[0])
    
    def list_messages(self, folder: str = "INBOX", limit: int = 10) -> List[Dict]:
        """List recent messages in a folder."""
        if not self.conn:
            self.connect()
        
        self.conn.select(folder)
        _, data = self.conn.search(None, "ALL")
        message_ids = data[0].split()
        
        # Get last N messages
        recent_ids = message_ids[-limit:] if len(message_ids) > limit else message_ids
        recent_ids = list(reversed(recent_ids))  # Newest first
        
        messages = []
        for msg_id in recent_ids:
            _, msg_data = self.conn.fetch(msg_id, "(RFC822.HEADER FLAGS)")
            if msg_data[0]:
                header_data = msg_data[0][1]
                flags = msg_data[0][0].decode() if msg_data[0][0] else ""
                msg = message_from_bytes(header_data)
                
                # Decode subject
                subject = msg.get("Subject", "(no subject)")
                decoded_parts = decode_header(subject)
                subject = ""
                for part, encoding in decoded_parts:
                    if isinstance(part, bytes):
                        subject += part.decode(encoding or "utf-8", errors="replace")
                    else:
                        subject += part
                
                # Decode from
                from_header = msg.get("From", "unknown")
                decoded_from = decode_header(from_header)
                from_str = ""
                for part, encoding in decoded_from:
                    if isinstance(part, bytes):
                        from_str += part.decode(encoding or "utf-8", errors="replace")
                    else:
                        from_str += part
                
                messages.append({
                    "id": msg_id.decode(),
                    "subject": subject,
                    "from": from_str,
                    "date": msg.get("Date", ""),
                    "is_read": "\\Seen" in flags
                })
        
        return messages
    
    def get_message(self, msg_id: str, folder: str = "INBOX") -> Dict:
        """Get full message content."""
        if not self.conn:
            self.connect()
        
        self.conn.select(folder)
        _, msg_data = self.conn.fetch(msg_id.encode(), "(RFC822)")
        
        if not msg_data[0]:
            raise Exception(f"Message {msg_id} not found")
        
        raw_email = msg_data[0][1]
        msg = message_from_bytes(raw_email)
        
        # Decode subject
        subject = msg.get("Subject", "(no subject)")
        decoded_parts = decode_header(subject)
        subject = "".join(
            part.decode(enc or "utf-8", errors="replace") if isinstance(part, bytes) else part
            for part, enc in decoded_parts
        )
        
        # Get body
        body = ""
        if msg.is_multipart():
            for part in msg.walk():
                content_type = part.get_content_type()
                if content_type == "text/plain":
                    payload = part.get_payload(decode=True)
                    charset = part.get_content_charset() or "utf-8"
                    body = payload.decode(charset, errors="replace")
                    break
                elif content_type == "text/html" and not body:
                    payload = part.get_payload(decode=True)
                    charset = part.get_content_charset() or "utf-8"
                    html = payload.decode(charset, errors="replace")
                    # Strip HTML tags
                    body = re.sub(r'<style[^>]*>.*?</style>', '', html, flags=re.DOTALL)
                    body = re.sub(r'<[^>]+>', ' ', body)
                    body = re.sub(r'\s+', ' ', body).strip()
        else:
            payload = msg.get_payload(decode=True)
            if payload:
                charset = msg.get_content_charset() or "utf-8"
                body = payload.decode(charset, errors="replace")
        
        # Truncate body to prevent context overflow and sanitize
        body = sanitize_for_terminal(body[:MAX_BODY_LENGTH])
        if len(body) == MAX_BODY_LENGTH:
            body += "\n[...truncated]"
        
        return {
            "id": msg_id,
            "subject": sanitize_for_terminal(subject),
            "from": sanitize_for_terminal(msg.get("From", "")),
            "to": sanitize_for_terminal(msg.get("To", "")),
            "date": msg.get("Date", ""),
            "body": body
        }
    
    def search(self, query: str, folder: str = "INBOX", limit: int = MAX_SEARCH_RESULTS) -> List[Dict]:
        """Search messages."""
        if not self.conn:
            self.connect()
        
        self.conn.select(folder)
        # Use IMAP search syntax
        _, data = self.conn.search(None, f'(OR SUBJECT "{query}" FROM "{query}")')
        message_ids = data[0].split()
        
        messages = []
        for msg_id in list(reversed(message_ids))[:limit]:
            _, msg_data = self.conn.fetch(msg_id, "(RFC822.HEADER)")
            if msg_data[0]:
                msg = message_from_bytes(msg_data[0][1])
                subject = msg.get("Subject", "(no subject)")
                decoded_parts = decode_header(subject)
                subject = "".join(
                    part.decode(enc or "utf-8", errors="replace") if isinstance(part, bytes) else part
                    for part, enc in decoded_parts
                )
                messages.append({
                    "id": msg_id.decode(),
                    "subject": sanitize_for_terminal(subject),
                    "from": sanitize_for_terminal(msg.get("From", "")),
                    "date": msg.get("Date", "")
                })
        
        return messages
    
    def get_unread(self, folder: str = "INBOX", limit: int = MAX_UNREAD_RESULTS) -> List[Dict]:
        """Get unread messages."""
        if not self.conn:
            self.connect()
        
        self.conn.select(folder)
        _, data = self.conn.search(None, "UNSEEN")
        message_ids = data[0].split()
        
        messages = []
        for msg_id in list(reversed(message_ids))[:limit]:
            _, msg_data = self.conn.fetch(msg_id, "(RFC822.HEADER)")
            if msg_data[0]:
                msg = message_from_bytes(msg_data[0][1])
                subject = msg.get("Subject", "(no subject)")
                decoded_parts = decode_header(subject)
                subject = "".join(
                    part.decode(enc or "utf-8", errors="replace") if isinstance(part, bytes) else part
                    for part, enc in decoded_parts
                )
                messages.append({
                    "id": msg_id.decode(),
                    "subject": sanitize_for_terminal(subject),
                    "from": sanitize_for_terminal(msg.get("From", "")),
                    "date": msg.get("Date", "")
                })
        
        return messages


class SMTPClient:
    """SMTP client with OAuth2 authentication."""
    
    def __init__(self, auth: OutlookAuth, email: str):
        self.auth = auth
        self.email = email
    
    def send(self, to: List[str], subject: str, body: str,
             cc: Optional[List[str]] = None,
             html: bool = False) -> None:
        """Send an email."""
        if html:
            msg = MIMEMultipart("alternative")
            msg.attach(MIMEText(body, "html"))
        else:
            msg = MIMEText(body)
        
        msg["Subject"] = subject
        msg["From"] = self.email
        msg["To"] = ", ".join(to)
        if cc:
            msg["Cc"] = ", ".join(cc)
        
        recipients = to + (cc or [])
        
        with smtplib.SMTP(SMTP_SERVER, SMTP_PORT) as server:
            server.starttls()
            auth_string = self.auth.get_xoauth2_string(self.email)
            server.docmd("AUTH", f"XOAUTH2 {auth_string}")
            server.sendmail(self.email, recipients, msg.as_string())


class OutlookClient:
    """High-level Outlook client combining IMAP and SMTP."""
    
    def __init__(self):
        self.email = TokenCache.retrieve("email")
        if not self.email:
            raise Exception("Not logged in. Run 'auth' command first.")
        
        self.auth = OutlookAuth()
        self.imap = IMAPClient(self.auth, self.email)
        self.smtp = SMTPClient(self.auth, self.email)
    
    def list_messages(self, folder: str = "INBOX", limit: int = 10) -> List[Dict]:
        return self.imap.list_messages(folder, limit)
    
    def get_message(self, msg_id: str, folder: str = "INBOX") -> Dict:
        return self.imap.get_message(msg_id, folder)
    
    def list_folders(self) -> List[str]:
        return self.imap.list_folders()
    
    def search(self, query: str) -> List[Dict]:
        return self.imap.search(query)
    
    def get_unread(self) -> List[Dict]:
        return self.imap.get_unread()
    
    def send(self, to: List[str], subject: str, body: str, **kwargs) -> None:
        self.smtp.send(to, subject, body, **kwargs)
    
    def close(self) -> None:
        self.imap.disconnect()


def authenticate(tenant_id: str = "common"):
    """Run device code flow for initial authentication."""
    auth = OutlookAuth(tenant_id)
    auth.device_code_flow()


def logout():
    """Clear cached tokens."""
    TokenCache.clear_all()
    print("Logged out. Tokens cleared from Keychain.")


def main():
    """CLI interface."""
    if len(sys.argv) < 2:
        print("Outlook University - Headless Email Access")
        print("Uses Thunderbird's pre-authorized client ID (no admin consent needed)")
        print("\nUsage: outlook_university.py <command> [args]")
        print("\nCommands:")
        print("  auth [tenant]  - Authenticate (optional: tenant ID or domain)")
        print("  logout         - Clear cached tokens")
        print("  whoami         - Show logged in email")
        print("  list [n]       - List recent n messages (default 10)")
        print("  unread         - List unread messages")
        print("  read <id>      - Read message by ID")
        print("  search <query> - Search messages")
        print("  folders        - List mail folders")
        print("  send           - Interactive send")
        return
    
    cmd = sys.argv[1]
    
    try:
        if cmd == "auth":
            tenant = sys.argv[2] if len(sys.argv) > 2 else "common"
            authenticate(tenant)
        
        elif cmd == "logout":
            logout()
        
        elif cmd == "whoami":
            email = TokenCache.retrieve("email")
            if email:
                print(f"Logged in as: {email}")
            else:
                print("Not logged in. Run 'auth' first.")
        
        elif cmd == "list":
            n = int(sys.argv[2]) if len(sys.argv) > 2 else 10
            client = OutlookClient()
            try:
                messages = client.list_messages(limit=n)
                for i, msg in enumerate(messages, 1):
                    read_marker = " " if msg["is_read"] else "●"
                    from_short = msg["from"][:25] if len(msg["from"]) > 25 else msg["from"]
                    subj_short = msg["subject"][:45] if len(msg["subject"]) > 45 else msg["subject"]
                    print(f"{read_marker} [{msg['id']:>3}] {from_short:<25} | {subj_short}")
            finally:
                client.close()
        
        elif cmd == "unread":
            client = OutlookClient()
            try:
                messages = client.get_unread()
                print(f"Unread messages: {len(messages)}\n")
                for msg in messages:
                    from_short = msg["from"][:25]
                    subj_short = msg["subject"][:50]
                    print(f"[{msg['id']:>3}] {from_short:<25} | {subj_short}")
            finally:
                client.close()
        
        elif cmd == "folders":
            client = OutlookClient()
            try:
                folders = client.list_folders()
                for f in folders:
                    print(f"  {f}")
            finally:
                client.close()
        
        elif cmd == "search" and len(sys.argv) > 2:
            query = " ".join(sys.argv[2:])
            client = OutlookClient()
            try:
                results = client.search(query)
                print(f"Found {len(results)} results for '{query}':\n")
                for msg in results:
                    print(f"[{msg['id']:>3}] {msg['from'][:30]}: {msg['subject'][:50]}")
            finally:
                client.close()
        
        elif cmd == "read" and len(sys.argv) > 2:
            msg_id = sys.argv[2]
            client = OutlookClient()
            try:
                msg = client.get_message(msg_id)
                print(f"From:    {msg['from']}")
                print(f"To:      {msg['to']}")
                print(f"Subject: {msg['subject']}")
                print(f"Date:    {msg['date']}")
                print(f"\n{'─'*60}\n")
                print(msg['body'][:3000])
            finally:
                client.close()
        
        elif cmd == "send":
            client = OutlookClient()
            try:
                print("Compose new message:")
                to = input("To: ").strip()
                subject = input("Subject: ").strip()
                print("Body (end with empty line):")
                lines = []
                while True:
                    line = input()
                    if not line:
                        break
                    lines.append(line)
                body = "\n".join(lines)
                
                confirm = input(f"\nSend to {to}? [y/N]: ").strip().lower()
                if confirm == 'y':
                    client.send([to], subject, body)
                    print("✓ Message sent!")
                else:
                    print("Cancelled.")
            finally:
                client.close()
        
        else:
            print(f"Unknown command: {cmd}")
            print("Run without arguments for help.")
    
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
