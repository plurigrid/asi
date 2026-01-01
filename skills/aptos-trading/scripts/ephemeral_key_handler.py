#!/usr/bin/env python3
"""
Ephemeral Key Handler for Aptos Trading

Provides AIP-61 keyless authentication support for the alpha executor.
Generates and manages ephemeral keys with automatic rotation.
"""

import os
import time
import json
import hashlib
import secrets
from pathlib import Path
from typing import Optional, Dict, Any, Tuple
from dataclasses import dataclass, asdict
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization

# =============================================================================
# Constants
# =============================================================================

DEFAULT_EXPIRY_SECS = 86400  # 24 hours
MIN_REMAINING_VALIDITY_SECS = 300  # 5 minutes
EPHEMERAL_KEYS_PATH = Path.home() / ".aptos" / "ephemeral_keys.json"

# =============================================================================
# Types
# =============================================================================

@dataclass
class EphemeralKeyState:
    private_key_hex: str
    public_key_hex: str
    created_at: int
    expires_at: int
    world_id: Optional[str] = None

    def is_valid(self, min_remaining: int = MIN_REMAINING_VALIDITY_SECS) -> bool:
        now = int(time.time())
        return self.expires_at - now > min_remaining

    def remaining_secs(self) -> int:
        now = int(time.time())
        return max(0, self.expires_at - now)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "EphemeralKeyState":
        return cls(**d)

# =============================================================================
# Key Generation
# =============================================================================

def generate_ephemeral_keypair(
    world_id: Optional[str] = None,
    expiry_secs: int = DEFAULT_EXPIRY_SECS
) -> EphemeralKeyState:
    """Generate a new ephemeral Ed25519 keypair."""
    now = int(time.time())

    # Generate random private key
    private_bytes = secrets.token_bytes(32)
    private_key = Ed25519PrivateKey.from_private_bytes(private_bytes)

    # Get public key
    public_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw
    )

    return EphemeralKeyState(
        private_key_hex=private_bytes.hex(),
        public_key_hex=public_bytes.hex(),
        created_at=now,
        expires_at=now + expiry_secs,
        world_id=world_id
    )

def generate_from_seed(
    seed: str,
    world_id: Optional[str] = None,
    expiry_secs: int = DEFAULT_EXPIRY_SECS
) -> EphemeralKeyState:
    """Generate ephemeral keypair from deterministic seed."""
    now = int(time.time())

    # Derive private key from seed
    private_bytes = hashlib.sha256(seed.encode()).digest()
    private_key = Ed25519PrivateKey.from_private_bytes(private_bytes)

    # Get public key
    public_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw
    )

    return EphemeralKeyState(
        private_key_hex=private_bytes.hex(),
        public_key_hex=public_bytes.hex(),
        created_at=now,
        expires_at=now + expiry_secs,
        world_id=world_id
    )

# =============================================================================
# Key Manager
# =============================================================================

class EphemeralKeyManager:
    """Manages ephemeral keys for Aptos transactions."""

    def __init__(self, persist_path: Optional[Path] = None):
        self.persist_path = persist_path or EPHEMERAL_KEYS_PATH
        self.keys: Dict[str, EphemeralKeyState] = {}
        self._load()

    def _load(self) -> None:
        """Load persisted keys from disk."""
        if self.persist_path.exists():
            try:
                data = json.loads(self.persist_path.read_text())
                for key_id, key_data in data.items():
                    self.keys[key_id] = EphemeralKeyState.from_dict(key_data)
            except Exception as e:
                print(f"Warning: Could not load ephemeral keys: {e}")

    def _save(self) -> None:
        """Persist keys to disk."""
        self.persist_path.parent.mkdir(parents=True, exist_ok=True)
        data = {k: v.to_dict() for k, v in self.keys.items()}
        self.persist_path.write_text(json.dumps(data, indent=2))

    def get_or_create(self, world_id: Optional[str] = None) -> EphemeralKeyState:
        """Get existing key or create new one."""
        key_id = f"world-{world_id}" if world_id else "default"
        existing = self.keys.get(key_id)

        if existing and existing.is_valid():
            return existing

        # Generate new key
        new_key = generate_ephemeral_keypair(world_id)
        self.keys[key_id] = new_key
        self._save()
        return new_key

    def rotate(self, world_id: Optional[str] = None) -> EphemeralKeyState:
        """Force rotate key for a world."""
        key_id = f"world-{world_id}" if world_id else "default"
        new_key = generate_ephemeral_keypair(world_id)
        self.keys[key_id] = new_key
        self._save()
        return new_key

    def rotate_all(self) -> None:
        """Force rotate all keys."""
        for key_id in list(self.keys.keys()):
            world_id = key_id.replace("world-", "") if key_id != "default" else None
            self.keys[key_id] = generate_ephemeral_keypair(world_id)
        self._save()

    def get_status(self) -> Dict[str, Dict[str, Any]]:
        """Get status of all keys."""
        return {
            key_id: {
                "valid": state.is_valid(),
                "remaining_secs": state.remaining_secs(),
                "expires_at": state.expires_at
            }
            for key_id, state in self.keys.items()
        }

    def clear(self) -> None:
        """Clear all keys."""
        self.keys.clear()
        if self.persist_path.exists():
            self.persist_path.unlink()

# =============================================================================
# JWT Sourcing
# =============================================================================

def fetch_jwt(source_type: str, source_value: str) -> str:
    """
    Fetch JWT from source.

    Source types:
    - env: Environment variable name
    - file: Path to file containing JWT
    - inline: JWT string directly (for testing)
    """
    if source_type == "env":
        jwt = os.environ.get(source_value)
        if not jwt:
            raise ValueError(f"JWT not found in env var: {source_value}")
        return jwt

    elif source_type == "file":
        path = Path(source_value)
        if not path.exists():
            raise FileNotFoundError(f"JWT file not found: {source_value}")
        return path.read_text().strip()

    elif source_type == "inline":
        return source_value

    else:
        raise ValueError(f"Unknown JWT source type: {source_type}")

def parse_jwt_source(source_str: str) -> Tuple[str, str]:
    """Parse JWT source string 'type:value'."""
    if ":" not in source_str:
        return "env", source_str

    idx = source_str.index(":")
    return source_str[:idx], source_str[idx + 1:]

# =============================================================================
# Keyless Config Building
# =============================================================================

def build_keyless_config(
    jwt: str,
    world_id: Optional[str] = None,
    manager: Optional[EphemeralKeyManager] = None
) -> Dict[str, str]:
    """Build keyless config for Aptos SDK."""
    if manager is None:
        manager = EphemeralKeyManager()

    key_state = manager.get_or_create(world_id)

    return {
        "jwt": jwt,
        "ephemeral_private_key": f"0x{key_state.private_key_hex}",
        "ephemeral_expiry_secs": str(key_state.expires_at),
    }

def get_env_vars_for_mcp(
    jwt: str,
    world_id: Optional[str] = None,
    network: str = "mainnet"
) -> Dict[str, str]:
    """Get environment variables for MCP server with keyless auth."""
    config = build_keyless_config(jwt, world_id)

    return {
        "APTOS_NETWORK": network,
        "APTOS_KEYLESS_JWT": config["jwt"],
        "APTOS_KEYLESS_EPK_PRIVATE_KEY": config["ephemeral_private_key"],
        "APTOS_KEYLESS_EPK_EXPIRY_SECS": config["ephemeral_expiry_secs"],
        "APTOS_WORLD_ID": world_id or "default",
    }

# =============================================================================
# Integration with Alpha Executor
# =============================================================================

def get_keyless_signer(jwt_source: Optional[str] = None) -> Tuple[str, str]:
    """
    Get keyless signer credentials.

    Returns (private_key_hex, jwt) for use with Aptos SDK.
    """
    # Get JWT
    if jwt_source:
        source_type, source_value = parse_jwt_source(jwt_source)
        jwt = fetch_jwt(source_type, source_value)
    else:
        # Try default env vars
        jwt = os.environ.get("APTOS_KEYLESS_JWT") or os.environ.get("APTOS_OIDC_JWT")
        if not jwt:
            raise ValueError(
                "No JWT configured. Set APTOS_KEYLESS_JWT or APTOS_OIDC_JWT, "
                "or pass jwt_source parameter."
            )

    # Get or create ephemeral key
    manager = EphemeralKeyManager()
    key_state = manager.get_or_create()

    return key_state.private_key_hex, jwt

# =============================================================================
# CLI
# =============================================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Ephemeral Key Handler")
    subparsers = parser.add_subparsers(dest="command")

    # generate command
    gen_parser = subparsers.add_parser("generate", help="Generate new ephemeral key")
    gen_parser.add_argument("--world", "-w", help="World ID")
    gen_parser.add_argument("--seed", "-s", help="Deterministic seed")

    # status command
    status_parser = subparsers.add_parser("status", help="Show key status")

    # rotate command
    rotate_parser = subparsers.add_parser("rotate", help="Rotate key(s)")
    rotate_parser.add_argument("--all", action="store_true", help="Rotate all keys")
    rotate_parser.add_argument("--world", "-w", help="World ID to rotate")

    # env-vars command
    env_parser = subparsers.add_parser("env-vars", help="Print env vars for MCP")
    env_parser.add_argument("jwt_source", help="JWT source (type:value)")
    env_parser.add_argument("--world", "-w", help="World ID")
    env_parser.add_argument("--network", "-n", default="mainnet")

    args = parser.parse_args()
    manager = EphemeralKeyManager()

    if args.command == "generate":
        if args.seed:
            key = generate_from_seed(args.seed, args.world)
        else:
            key = manager.get_or_create(args.world)
        print(json.dumps(key.to_dict(), indent=2))

    elif args.command == "status":
        status = manager.get_status()
        for key_id, info in status.items():
            print(f"{key_id}: valid={info['valid']} remaining={info['remaining_secs']}s")

    elif args.command == "rotate":
        if args.all:
            manager.rotate_all()
            print(f"Rotated {len(manager.keys)} keys")
        else:
            key = manager.rotate(args.world)
            print(f"Rotated key for {args.world or 'default'}")
            print(json.dumps(key.to_dict(), indent=2))

    elif args.command == "env-vars":
        source_type, source_value = parse_jwt_source(args.jwt_source)
        jwt = fetch_jwt(source_type, source_value)
        env_vars = get_env_vars_for_mcp(jwt, args.world, args.network)
        for k, v in env_vars.items():
            print(f'export {k}="{v}"')

    else:
        parser.print_help()
