#!/bin/sh
unset PYTHONPATH
export EXOPRIORS_API_KEY="$(/Users/alice/.cargo/bin/fnox get EXOPRIORS_API_KEY --age-key-file /Users/alice/.age/key.txt -c /Users/alice/v/instance-onboarding/fnox.toml)"
export EXOPRIORS_SOCKS_PROXY="socks5h://localhost:19050"
exec uvx --from 'mcp[cli]' --with httpx --with 'httpx[socks]' --with h2 python /Users/alice/.claude/skills/exopriors-scry/scry_mcp.py
