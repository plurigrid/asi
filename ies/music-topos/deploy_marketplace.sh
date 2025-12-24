#!/bin/bash
#
# Marketplace Gateway Deployment Script
#
# Usage:
#   ./deploy_marketplace.sh [start|stop|restart|status|test]
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GATEWAY_SCRIPT="$SCRIPT_DIR/marketplace_gateway.py"
PID_FILE="$SCRIPT_DIR/.marketplace_gateway.pid"
LOG_FILE="$SCRIPT_DIR/marketplace_gateway.log"
HOST="${GATEWAY_HOST:-0.0.0.0}"
PORT="${GATEWAY_PORT:-8080}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

# Check if gateway is running
is_running() {
    if [ -f "$PID_FILE" ]; then
        PID=$(cat "$PID_FILE")
        if ps -p "$PID" > /dev/null 2>&1; then
            return 0
        fi
    fi
    return 1
}

# Start gateway
start_gateway() {
    info "Starting Marketplace Gateway..."

    if is_running; then
        warning "Gateway is already running (PID: $(cat $PID_FILE))"
        return 1
    fi

    # Check dependencies
    info "Checking dependencies..."
    python3 -c "import aiohttp, numpy" 2>/dev/null || {
        error "Missing dependencies. Install with: pip install aiohttp numpy"
        return 1
    }

    # Check if port is available
    if lsof -Pi :$PORT -sTCP:LISTEN -t >/dev/null 2>&1; then
        error "Port $PORT is already in use"
        return 1
    fi

    # Start server in background
    info "Starting server on $HOST:$PORT"
    nohup python3 "$GATEWAY_SCRIPT" --host "$HOST" --port "$PORT" > "$LOG_FILE" 2>&1 &
    echo $! > "$PID_FILE"

    # Wait for server to start
    sleep 2

    # Check if started successfully
    if is_running; then
        success "Gateway started successfully (PID: $(cat $PID_FILE))"
        info "Logs: $LOG_FILE"
        info "Endpoints:"
        echo "  GET  http://$HOST:$PORT/apps"
        echo "  POST http://$HOST:$PORT/execute"
        echo "  POST http://$HOST:$PORT/compose"
        echo "  GET  http://$HOST:$PORT/health"
        echo "  WS   ws://$HOST:$PORT/stream"
        return 0
    else
        error "Failed to start gateway"
        cat "$LOG_FILE"
        return 1
    fi
}

# Stop gateway
stop_gateway() {
    info "Stopping Marketplace Gateway..."

    if ! is_running; then
        warning "Gateway is not running"
        return 1
    fi

    PID=$(cat "$PID_FILE")
    info "Killing process $PID"
    kill "$PID" 2>/dev/null || true

    # Wait for process to stop
    sleep 2

    if ! is_running; then
        rm -f "$PID_FILE"
        success "Gateway stopped successfully"
        return 0
    else
        error "Failed to stop gateway"
        return 1
    fi
}

# Restart gateway
restart_gateway() {
    info "Restarting Marketplace Gateway..."
    stop_gateway || true
    sleep 1
    start_gateway
}

# Check status
check_status() {
    info "Checking Marketplace Gateway status..."

    if is_running; then
        PID=$(cat "$PID_FILE")
        success "Gateway is running (PID: $PID)"

        # Try health check
        if command -v curl > /dev/null 2>&1; then
            info "Running health check..."
            if curl -s "http://localhost:$PORT/health" > /dev/null 2>&1; then
                success "Health check passed"
                curl -s "http://localhost:$PORT/health" | python3 -m json.tool
            else
                warning "Health check failed"
            fi
        fi
        return 0
    else
        error "Gateway is not running"
        return 1
    fi
}

# Run tests
run_tests() {
    info "Running test suite..."

    # Check if pytest is available
    if ! command -v pytest > /dev/null 2>&1; then
        error "pytest not found. Install with: pip install pytest pytest-asyncio"
        return 1
    fi

    # Run tests
    cd "$SCRIPT_DIR"
    pytest test_marketplace_gateway.py -v --tb=short

    if [ $? -eq 0 ]; then
        success "All tests passed"
        return 0
    else
        error "Tests failed"
        return 1
    fi
}

# Show logs
show_logs() {
    if [ -f "$LOG_FILE" ]; then
        tail -f "$LOG_FILE"
    else
        error "Log file not found: $LOG_FILE"
        return 1
    fi
}

# Main command handler
case "${1:-}" in
    start)
        start_gateway
        ;;
    stop)
        stop_gateway
        ;;
    restart)
        restart_gateway
        ;;
    status)
        check_status
        ;;
    test)
        run_tests
        ;;
    logs)
        show_logs
        ;;
    *)
        echo "Marketplace Gateway Deployment Script"
        echo ""
        echo "Usage: $0 {start|stop|restart|status|test|logs}"
        echo ""
        echo "Commands:"
        echo "  start    - Start the gateway server"
        echo "  stop     - Stop the gateway server"
        echo "  restart  - Restart the gateway server"
        echo "  status   - Check server status and health"
        echo "  test     - Run test suite"
        echo "  logs     - Show server logs (tail -f)"
        echo ""
        echo "Environment variables:"
        echo "  GATEWAY_HOST - Server host (default: 0.0.0.0)"
        echo "  GATEWAY_PORT - Server port (default: 8080)"
        echo ""
        exit 1
        ;;
esac
