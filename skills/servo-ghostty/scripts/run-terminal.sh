#!/bin/bash
# Servo-Ghostty Terminal Launcher
# Starts ghostty-web server + Servo browser with terminal UI

set -e

echo "Servo-Ghostty Terminal"
echo "======================"
echo ""

# Configuration
GHOSTTY_WEB="/Users/bob/i/zig-syrup/zig-out/bin/ghostty-web"
TERMINAL_HTML="$(dirname "$0")/../examples/ghostty-terminal.html"
GHOSTTY_WS_PORT=7070

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check dependencies
check_dependency() {
    if ! command -v "$1" &> /dev/null; then
        echo -e "${RED}✗ $1 not found${NC}"
        echo "  Install: $2"
        exit 1
    fi
    echo -e "${GREEN}✓ $1 found${NC}"
}

echo "Checking dependencies..."
check_dependency "servo" "brew install servo"
check_dependency "lsof" "Built-in on macOS"

# Check if ghostty-web binary exists
if [ ! -f "$GHOSTTY_WEB" ]; then
    echo -e "${RED}✗ ghostty-web not found${NC}"
    echo "  Expected: $GHOSTTY_WEB"
    echo "  Build: cd ~/i/zig-syrup && zig build"
    exit 1
fi
echo -e "${GREEN}✓ ghostty-web binary found${NC}"

# Check if HTML file exists
if [ ! -f "$TERMINAL_HTML" ]; then
    echo -e "${RED}✗ Terminal HTML not found${NC}"
    echo "  Expected: $TERMINAL_HTML"
    exit 1
fi
echo -e "${GREEN}✓ Terminal HTML found${NC}"

echo ""

# Check if ghostty-web is already running
if lsof -Pi :$GHOSTTY_WS_PORT -sTCP:LISTEN -t >/dev/null 2>&1 ; then
    echo -e "${YELLOW}⚠ ghostty-web already running on :$GHOSTTY_WS_PORT${NC}"
    echo "  Kill with: pkill ghostty-web"
else
    echo "Starting ghostty-web server..."
    $GHOSTTY_WEB &
    GHOSTTY_PID=$!
    echo -e "${GREEN}✓ ghostty-web started (PID: $GHOSTTY_PID)${NC}"

    # Wait for server to be ready
    echo "Waiting for WebSocket server..."
    for i in {1..10}; do
        if lsof -Pi :$GHOSTTY_WS_PORT -sTCP:LISTEN -t >/dev/null 2>&1 ; then
            echo -e "${GREEN}✓ WebSocket ready on :$GHOSTTY_WS_PORT${NC}"
            break
        fi
        sleep 0.5
    done
fi

echo ""
echo "Launching Servo browser..."
echo "  HTML: $TERMINAL_HTML"
echo ""

# Launch Servo
servo "$TERMINAL_HTML"

# Cleanup on exit
if [ ! -z "$GHOSTTY_PID" ]; then
    echo ""
    echo "Shutting down ghostty-web (PID: $GHOSTTY_PID)..."
    kill $GHOSTTY_PID 2>/dev/null || true
fi

echo ""
echo "Done ✓"
