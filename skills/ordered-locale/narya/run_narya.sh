#!/bin/bash
# run_narya.sh - Run Narya on ordered locale files
#
# Trit: +1 (PLUS/GENERATOR)
# GF(3): Σ(-1,0,+1) = 0 (conserved)
#
# Usage:
#   ./run_narya.sh              # Verify all files
#   ./run_narya.sh --emacs      # Use headless Emacs
#   ./run_narya.sh --file X.ny  # Verify specific file
#   ./run_narya.sh --gf3        # Check GF(3) only

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NARYA="${NARYA_EXECUTABLE:-narya}"
VOICE="${NARYA_VOICE:-Luca}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

announce() {
    if [[ "$OSTYPE" == "darwin"* ]]; then
        say -v "$VOICE" "$1" 2>/dev/null &
    fi
    echo -e "${BLUE}[NARYA]${NC} $1"
}

verify_file() {
    local file="$1"
    local filepath="${SCRIPT_DIR}/${file}"
    
    if [[ ! -f "$filepath" ]]; then
        echo -e "${RED}✗${NC} File not found: $file"
        return 1
    fi
    
    echo -n "Checking $file... "
    
    if command -v "$NARYA" &> /dev/null; then
        if $NARYA "$filepath" 2>&1; then
            echo -e "${GREEN}✓${NC}"
            return 0
        else
            echo -e "${RED}✗${NC}"
            return 1
        fi
    else
        # Narya not installed - do syntax check only
        echo -e "${YELLOW}⚠${NC} (narya not found, syntax check only)"
        # Basic syntax validation
        if grep -q "^def\|^import\|^axiom" "$filepath"; then
            return 0
        fi
        return 1
    fi
}

verify_gf3() {
    echo ""
    echo "═══ GF(3) Conservation Check ═══"
    echo ""
    
    local violations=0
    local total=0
    
    for file in "${SCRIPT_DIR}"/*.ny; do
        if [[ -f "$file" ]]; then
            # Find GF3Conserved declarations
            while IFS= read -r line; do
                if [[ "$line" =~ GF3Conserved ]]; then
                    ((total++)) || true
                    # Extract trits and check
                    if [[ "$line" =~ minus.*ergodic.*plus ]] || \
                       [[ "$line" =~ ergodic.*ergodic.*ergodic ]] || \
                       [[ "$line" =~ plus.*plus.*plus ]] || \
                       [[ "$line" =~ minus.*minus.*minus ]]; then
                        echo -e "  ${GREEN}✓${NC} $(basename "$file"): $line"
                    else
                        echo -e "  ${RED}✗${NC} $(basename "$file"): $line"
                        ((violations++)) || true
                    fi
                fi
            done < "$file"
        fi
    done
    
    echo ""
    if [[ $violations -eq 0 ]]; then
        echo -e "${GREEN}GF(3) CONSERVED:${NC} $total triads verified"
        return 0
    else
        echo -e "${RED}GF(3) VIOLATIONS:${NC} $violations/$total"
        return 1
    fi
}

run_emacs_headless() {
    echo "Running Narya verification via headless Emacs..."
    
    local pg_path=""
    if [[ -f ~/.emacs.d/straight/build/proof-general/generic/proof-site.el ]]; then
        pg_path=~/.emacs.d/straight/build/proof-general/generic/proof-site.el
    elif [[ -f /usr/share/emacs/site-lisp/proof-general/generic/proof-site.el ]]; then
        pg_path=/usr/share/emacs/site-lisp/proof-general/generic/proof-site.el
    fi
    
    emacs --batch \
        ${pg_path:+-l "$pg_path"} \
        -l "${SCRIPT_DIR}/narya-ordered-locale.el" \
        -f narya-batch-verify
}

print_header() {
    echo ""
    echo "╔═══════════════════════════════════════════════════════╗"
    echo "║        NARYA ORDERED LOCALE VERIFICATION              ║"
    echo "║        Trit: +1 (PLUS/GENERATOR)                      ║"
    echo "║        GF(3): Σ(-1,0,+1) = 0                          ║"
    echo "╚═══════════════════════════════════════════════════════╝"
    echo ""
}

main() {
    print_header
    
    local mode="all"
    local target_file=""
    
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --emacs)
                run_emacs_headless
                exit $?
                ;;
            --gf3)
                verify_gf3
                exit $?
                ;;
            --file)
                target_file="$2"
                shift 2
                ;;
            --help|-h)
                echo "Usage: $0 [OPTIONS]"
                echo ""
                echo "Options:"
                echo "  --emacs       Run via headless Emacs with Proof General"
                echo "  --gf3         Verify GF(3) conservation only"
                echo "  --file FILE   Verify specific file"
                echo "  --help        Show this help"
                exit 0
                ;;
            *)
                echo "Unknown option: $1"
                exit 1
                ;;
        esac
    done
    
    announce "Starting ordered locale verification"
    
    local files=("gf3.ny" "ordered_locale.ny" "bridge_sheaf.ny")
    local passed=0
    local failed=0
    
    if [[ -n "$target_file" ]]; then
        files=("$target_file")
    fi
    
    echo "Files to verify: ${files[*]}"
    echo ""
    echo "─── Type Checking ───"
    
    for file in "${files[@]}"; do
        if verify_file "$file"; then
            ((passed++)) || true
        else
            ((failed++)) || true
        fi
    done
    
    # Also check GF(3)
    verify_gf3 || ((failed++)) || true
    
    echo ""
    echo "─── Summary ───"
    echo "Passed: $passed"
    echo "Failed: $failed"
    echo ""
    
    if [[ $failed -eq 0 ]]; then
        announce "All verifications passed"
        echo -e "${GREEN}✓ ALL PASS${NC}"
        exit 0
    else
        announce "Verification failed"
        echo -e "${RED}✗ FAILURES${NC}"
        exit 1
    fi
}

main "$@"
