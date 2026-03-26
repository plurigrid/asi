#!/usr/bin/env bash
# gx10-offload: Send inference requests to GX10 DGX Spark via Ollama
set -euo pipefail

GX10_HOST="${GX10_HOST:-10.0.0.234}"
GX10_USER="${GX10_USER:-a}"
GX10_PASS="${GX10_PASS:-aaaaaa}"
DEFAULT_MODEL="${GX10_MODEL:-devstral}"
OLLAMA_PORT=11434
SSHPASS="$(command -v sshpass 2>/dev/null || find /Users/alice/v/.flox/run -name sshpass 2>/dev/null | head -1 || echo sshpass)"
SSH="$(command -v ssh 2>/dev/null || echo /usr/bin/ssh)"
SSH_OPTS="-o StrictHostKeyChecking=accept-new -o ConnectTimeout=10 -o PreferredAuthentications=password -o PubkeyAuthentication=no"

ssh_cmd() {
    "$SSHPASS" -p "$GX10_PASS" "$SSH" $SSH_OPTS "$GX10_USER@$GX10_HOST" "$@"
}

ensure_ollama() {
    ssh_cmd 'pgrep -x ollama > /dev/null || (nohup ollama serve > /tmp/ollama.log 2>&1 & sleep 2)'
}

status() {
    echo "=== GX10 Offload Status ==="
    if ping -c 1 -W 2 "$GX10_HOST" &>/dev/null; then
        echo "Host: REACHABLE ($GX10_HOST)"
    else
        echo "Host: UNREACHABLE ($GX10_HOST)"
        exit 1
    fi
    echo ""
    echo "=== GPU ==="
    ssh_cmd 'nvidia-smi --query-gpu=name,memory.total,memory.used,temperature.gpu --format=csv,noheader 2>/dev/null || echo "nvidia-smi unavailable"'
    echo ""
    echo "=== Memory ==="
    ssh_cmd 'free -h | head -2'
    echo ""
    echo "=== Ollama ==="
    ensure_ollama
    ssh_cmd "curl -s http://localhost:$OLLAMA_PORT/api/tags" | python3 -c "
import sys, json
data = json.load(sys.stdin)
for m in data.get('models', []):
    print(f\"  {m['name']:30s} {m['size']/(1<<30):.1f}GB  modified: {m.get('modified_at','?')[:10]}\")
" 2>/dev/null || echo "  Could not list models"
}

generate() {
    local prompt="$1"
    local model="${2:-$DEFAULT_MODEL}"

    ensure_ollama

    # Escape prompt for JSON
    local json_prompt
    json_prompt=$(python3 -c "import json,sys; print(json.dumps(sys.argv[1]))" "$prompt")

    ssh_cmd "curl -s http://localhost:$OLLAMA_PORT/api/generate -d '{\"model\":\"$model\",\"prompt\":$json_prompt,\"stream\":false}'" \
        | python3 -c "import sys,json; print(json.load(sys.stdin).get('response','[no response]'))" 2>/dev/null
}

chat() {
    local content="$1"
    local model="${2:-$DEFAULT_MODEL}"
    local system="${3:-You are a helpful coding assistant. Be concise and provide working code.}"

    ensure_ollama

    local payload
    payload=$(python3 -c "
import json, sys
print(json.dumps({
    'model': sys.argv[1],
    'messages': [
        {'role': 'system', 'content': sys.argv[3]},
        {'role': 'user', 'content': sys.argv[2]}
    ],
    'stream': False
}))
" "$model" "$content" "$system")

    ssh_cmd "curl -s http://localhost:$OLLAMA_PORT/api/chat -d '$(echo "$payload" | sed "s/'/'\\\\''/g")'" \
        | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('message',{}).get('content','[no response]'))" 2>/dev/null
}

batch() {
    local file="$1"
    local model="${2:-$DEFAULT_MODEL}"
    local i=0

    while IFS= read -r line; do
        [ -z "$line" ] && continue
        i=$((i + 1))
        echo "--- [$i] ---"
        generate "$line" "$model"
        echo ""
    done < "$file"
}

# --- Main ---
case "${1:-}" in
    --status|-s)
        status
        ;;
    --batch|-b)
        [ -z "${2:-}" ] && { echo "Usage: $0 --batch <file> [model]"; exit 1; }
        batch "$2" "${3:-$DEFAULT_MODEL}"
        ;;
    --chat|-c)
        [ -z "${2:-}" ] && { echo "Usage: $0 --chat <message> [model] [system_prompt]"; exit 1; }
        chat "$2" "${3:-$DEFAULT_MODEL}" "${4:-}"
        ;;
    --help|-h)
        cat <<'EOF'
gx10-offload: Offload inference to local GX10 DGX Spark

Usage:
  offload.sh "prompt"                     Generate with default model (devstral)
  offload.sh "prompt" model-name          Generate with specific model
  offload.sh --chat "message" [model]     Chat completion
  offload.sh --batch file.txt [model]     Process prompts from file
  offload.sh --status                     Check GX10 status and models

Environment:
  GX10_HOST    Override host (default: 10.0.0.234)
  GX10_USER    Override user (default: a)
  GX10_PASS    Override password (default: aaaaaa)
  GX10_MODEL   Override default model (default: devstral)

Models:
  devstral         14GB  Fast coding, lightweight
  devstral-2:123b  74GB  Heavy reasoning, complex code
  devstral2-4k     74GB  Same, 4k context
EOF
        ;;
    "")
        echo "Usage: $0 <prompt> [model] | --status | --batch <file> | --chat <msg>"
        exit 1
        ;;
    *)
        generate "$1" "${2:-$DEFAULT_MODEL}"
        ;;
esac
