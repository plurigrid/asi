#!/usr/bin/env python3
"""Tailscale + LocalSend peer discovery with Gay.jl colors"""

import json
import socket
import struct
import subprocess
import hashlib
from dataclasses import dataclass
from typing import Optional, Callable
import urllib.request

# Gay.jl constants
GAY_SEED = 0x6761795f636f6c6f
GOLDEN = 0x9e3779b97f4a7c15
MASK64 = 0xffffffffffffffff

# LocalSend constants
LOCALSEND_MULTICAST = "224.0.0.167"
LOCALSEND_PORT = 53317


def splitmix64(state: int) -> tuple[int, int]:
    """SplitMix64 PRNG step"""
    s = (state + GOLDEN) & MASK64
    z = ((s ^ (s >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK64
    return s, z ^ (z >> 31)


def gay_color_at(index: int, seed: int = GAY_SEED) -> str:
    """Get deterministic hex color at index"""
    state = seed
    for _ in range(index):
        state, _ = splitmix64(state)
    _, val = splitmix64(state)
    
    # Extract RGB from hash
    r = (val >> 16) & 0xFF
    g = (val >> 8) & 0xFF  
    b = val & 0xFF
    return f"#{r:02X}{g:02X}{b:02X}"


@dataclass
class Peer:
    name: str
    tailscale_ip: Optional[str] = None
    localsend_port: int = LOCALSEND_PORT
    fingerprint: Optional[str] = None
    color: str = "#FFFFFF"
    
    def to_dict(self):
        return {
            'name': self.name,
            'tailscale_ip': self.tailscale_ip,
            'localsend_port': self.localsend_port,
            'fingerprint': self.fingerprint,
            'color': self.color
        }


class TailscaleLocalSend:
    def __init__(self, seed: int = GAY_SEED):
        self.seed = seed
        self._peers: list[Peer] = []
    
    def discover_tailscale(self) -> list[Peer]:
        """Discover peers via tailscale status"""
        try:
            result = subprocess.run(
                ["tailscale", "status", "--json"],
                capture_output=True, text=True, timeout=5
            )
            if result.returncode != 0:
                return []
            
            status = json.loads(result.stdout)
            peers = []
            
            # Add self
            if 'Self' in status:
                self_info = status['Self']
                peers.append(Peer(
                    name=self_info.get('HostName', 'self'),
                    tailscale_ip=self_info.get('TailscaleIPs', [None])[0]
                ))
            
            # Add peers
            peer_map = status.get('Peer', {})
            if isinstance(peer_map, dict):
                for key, peer_info in peer_map.items():
                    ips = peer_info.get('TailscaleIPs', [])
                    peers.append(Peer(
                        name=peer_info.get('HostName', key[:8]),
                        tailscale_ip=ips[0] if ips else None,
                        fingerprint=key
                    ))
            
            return peers
        except (subprocess.TimeoutExpired, FileNotFoundError, json.JSONDecodeError):
            return []
    
    def discover_localsend(self, timeout: float = 2.0) -> list[Peer]:
        """Discover LocalSend peers via multicast"""
        peers = []
        
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.settimeout(timeout)
            
            # Join multicast group
            mreq = struct.pack("4sl", socket.inet_aton(LOCALSEND_MULTICAST), socket.INADDR_ANY)
            sock.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP, mreq)
            sock.bind(('', LOCALSEND_PORT))
            
            # Send announce
            announce = json.dumps({
                "alias": socket.gethostname(),
                "version": "2.0",
                "deviceType": "desktop",
                "fingerprint": hashlib.sha256(socket.gethostname().encode()).hexdigest()[:16],
                "port": LOCALSEND_PORT,
                "protocol": "http"
            }).encode()
            sock.sendto(announce, (LOCALSEND_MULTICAST, LOCALSEND_PORT))
            
            # Listen for responses
            end_time = __import__('time').time() + timeout
            while __import__('time').time() < end_time:
                try:
                    data, addr = sock.recvfrom(4096)
                    info = json.loads(data.decode())
                    peers.append(Peer(
                        name=info.get('alias', addr[0]),
                        tailscale_ip=None,  # Will be merged later
                        localsend_port=info.get('port', LOCALSEND_PORT),
                        fingerprint=info.get('fingerprint')
                    ))
                except socket.timeout:
                    break
                except json.JSONDecodeError:
                    continue
            
            sock.close()
        except OSError:
            pass
        
        return peers
    
    def discover(self) -> list[Peer]:
        """Discover peers on both Tailscale and LocalSend"""
        ts_peers = {p.name: p for p in self.discover_tailscale()}
        ls_peers = {p.name: p for p in self.discover_localsend()}
        
        # Merge peers
        all_names = set(ts_peers.keys()) | set(ls_peers.keys())
        merged = []
        
        for i, name in enumerate(sorted(all_names)):
            ts = ts_peers.get(name)
            ls = ls_peers.get(name)
            
            peer = Peer(
                name=name,
                tailscale_ip=ts.tailscale_ip if ts else None,
                localsend_port=ls.localsend_port if ls else LOCALSEND_PORT,
                fingerprint=(ts.fingerprint if ts else None) or (ls.fingerprint if ls else None),
                color=gay_color_at(i, self.seed)
            )
            merged.append(peer)
        
        self._peers = merged
        return merged
    
    def send(self, peer: str, file: str) -> bool:
        """Send file to peer via LocalSend"""
        target = next((p for p in self._peers if p.name == peer), None)
        if not target:
            return False
        
        ip = target.tailscale_ip or peer
        url = f"http://{ip}:{target.localsend_port}/api/localsend/v2/prepare-upload"
        
        # Prepare upload
        import os
        metadata = {
            "info": {"alias": socket.gethostname()},
            "files": {
                "file1": {
                    "id": "file1",
                    "fileName": os.path.basename(file),
                    "size": os.path.getsize(file),
                    "fileType": "application/octet-stream"
                }
            }
        }
        
        try:
            req = urllib.request.Request(
                url,
                data=json.dumps(metadata).encode(),
                headers={"Content-Type": "application/json"},
                method="POST"
            )
            resp = urllib.request.urlopen(req, timeout=10)
            session = json.loads(resp.read())
            
            # Upload file
            session_id = session.get('sessionId')
            token = session.get('files', {}).get('file1')
            if session_id and token:
                upload_url = f"http://{ip}:{target.localsend_port}/api/localsend/v2/upload?sessionId={session_id}&fileId=file1&token={token}"
                with open(file, 'rb') as f:
                    upload_req = urllib.request.Request(upload_url, data=f.read(), method="POST")
                    urllib.request.urlopen(upload_req, timeout=60)
                return True
        except Exception:
            pass
        
        return False
    
    def receive(self, callback: Callable[[str], None], port: int = LOCALSEND_PORT):
        """Start LocalSend receive server"""
        from http.server import HTTPServer, BaseHTTPRequestHandler
        import tempfile
        
        class Handler(BaseHTTPRequestHandler):
            def do_POST(self):
                if '/prepare-upload' in self.path:
                    self.send_response(200)
                    self.send_header('Content-Type', 'application/json')
                    self.end_headers()
                    self.wfile.write(json.dumps({
                        'sessionId': 'sess1',
                        'files': {'file1': 'token1'}
                    }).encode())
                elif '/upload' in self.path:
                    length = int(self.headers.get('Content-Length', 0))
                    data = self.rfile.read(length)
                    with tempfile.NamedTemporaryFile(delete=False) as f:
                        f.write(data)
                        callback(f.name)
                    self.send_response(200)
                    self.end_headers()
            
            def log_message(self, *args): pass
        
        server = HTTPServer(('', port), Handler)
        server.serve_forever()


if __name__ == "__main__":
    tls = TailscaleLocalSend()
    peers = tls.discover()
    print(json.dumps([p.to_dict() for p in peers], indent=2))
