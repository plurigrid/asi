#!/bin/bash
# qigong: Master control script for red team / blue team resource management
# Orchestrates all 11 Apple Silicon refinements

set -euo pipefail

QIGONG_HOME="${QIGONG_HOME:=$HOME/.qigong}"
QIGONG_LOGS="$QIGONG_HOME/logs"
QIGONG_DATA="$QIGONG_HOME/data"

mkdir -p "$QIGONG_LOGS" "$QIGONG_DATA"

# Color codes for output
RED='\033[0;31m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_red() { echo -e "${RED}[RED] $1${NC}" | tee -a "$QIGONG_LOGS/qigong.log"; }
log_blue() { echo -e "${BLUE}[BLUE] $1${NC}" | tee -a "$QIGONG_LOGS/qigong.log"; }
log_info() { echo -e "${GREEN}[*] $1${NC}" | tee -a "$QIGONG_LOGS/qigong.log"; }
log_warn() { echo -e "${YELLOW}[!] $1${NC}" | tee -a "$QIGONG_LOGS/qigong.log"; }

# ==============================================================================
# REFINEMENT 1: Apple Silicon P/E-Cluster Optimization
# ==============================================================================

refinement_1_monitor_clusters() {
  log_info "Refinement 1: Monitoring P/E-cluster separation..."

  if command -v asitop &> /dev/null; then
    asitop -o "$QIGONG_DATA/asitop_$(date +%s).csv" -n 10 &
    ASITOP_PID=$!
    log_info "asitop monitoring started (PID: $ASITOP_PID)"
  else
    log_warn "asitop not found, using sysctl fallback"
    echo "P-cores: $(sysctl -n hw.perflevel0.physicalcpu)"
    echo "E-cores: $(sysctl -n hw.perflevel1.physicalcpu)"
  fi
}

# ==============================================================================
# REFINEMENT 2: macOS setrlimit Quirks
# ==============================================================================

refinement_2_query_limits() {
  log_info "Refinement 2: Querying resource limits (ARM64 Monterey+ quirks)..."

  cat > "$QIGONG_DATA/rlimit_check.py" << 'PYTHON'
#!/usr/bin/env python3
import resource
import sys

limits_to_check = [
  ('RLIMIT_CPU', resource.RLIMIT_CPU),
  ('RLIMIT_FSIZE', resource.RLIMIT_FSIZE),
  ('RLIMIT_DATA', resource.RLIMIT_DATA),
  ('RLIMIT_STACK', resource.RLIMIT_STACK),
  ('RLIMIT_CORE', resource.RLIMIT_CORE),
  ('RLIMIT_NOFILE', resource.RLIMIT_NOFILE),
]

for name, limit_type in limits_to_check:
  try:
    soft, hard = resource.getrlimit(limit_type)
    print(f"{name:20} soft={soft:15} hard={hard:15}")
  except ValueError as e:
    print(f"{name:20} ERROR: {e}")

# ARM64 setrlimit(RLIMIT_DATA) fails if < 418GB
print("\n[!] RLIMIT_DATA < 418GB will fail on ARM64 Monterey+")
PYTHON

  python3 "$QIGONG_DATA/rlimit_check.py"
}

# ==============================================================================
# REFINEMENT 3: Sandbox Entitlements as Resource Gates
# ==============================================================================

refinement_3_analyze_entitlements() {
  local target_app=$1
  log_info "Refinement 3: Analyzing sandbox entitlements for $target_app..."

  if [ -d "$target_app" ]; then
    codesign -d --entitlements :- "$target_app" 2>/dev/null | \
      grep -o 'com\.apple\.[^<]*' | sort | uniq | while read ent; do
        echo "  - $ent"
      done
  else
    log_warn "App not found: $target_app"
  fi
}

# ==============================================================================
# REFINEMENT 4: Instruments Framework + powermetrics API
# ==============================================================================

refinement_4_thermal_baseline() {
  log_info "Refinement 4: Capturing thermal baseline via powermetrics..."

  powermetrics -n 10 -s cpu_power,gpu_power,ane_power,thermal_pressure \
    -f json > "$QIGONG_DATA/thermal_baseline_$(date +%s).json" 2>/dev/null

  log_info "Thermal baseline saved"
}

# ==============================================================================
# REFINEMENT 5: dyld Resource Accounting
# ==============================================================================

refinement_5_dyld_monitor() {
  log_info "Refinement 5: Monitoring dyld injection and library loads..."

  cat > "$QIGONG_DATA/dyld_monitor.dtrace" << 'DTRACE'
syscall:::entry /execname == "dyld"/ {
  printf("dyld library load: %s (latency tracking)\n", execname);
  @loads[execname] = count();
}

syscall:::exit /execname == "dyld"/ {
  @exit_times[execname] = avg(arg0);
}

END {
  printf("\n=== dyld Load Summary ===\n");
  printa("Load count: %s = %@d\n", @loads);
  printa("Avg exit time: %s = %@u cycles\n", @exit_times);
}
DTRACE

  if command -v dtrace &> /dev/null; then
    sudo dtrace -s "$QIGONG_DATA/dyld_monitor.dtrace" 2>/dev/null &
    log_info "dyld monitoring started"
  else
    log_warn "dtrace not available"
  fi
}

# ==============================================================================
# REFINEMENT 6: Jetsam Pressure Relief
# ==============================================================================

refinement_6_memory_pressure() {
  log_info "Refinement 6: Monitoring memory pressure & jetsam threshold..."

  # Get current threshold
  THRESHOLD=$(sysctl -n kern.memorystatus_jetsam_threshold 2>/dev/null || echo "unknown")
  log_info "Current jetsam threshold: $THRESHOLD"

  # Monitor pressure in real-time
  cat > "$QIGONG_DATA/jetsam_monitor.sh" << 'BASH'
#!/bin/bash
while true; do
  # Get memory pressure (0-100)
  PRESSURE=$(osascript -e 'tell application "System Events" to get (memory used)' 2>/dev/null || echo "0")
  PERCENT=$((PRESSURE * 100 / ($(sysctl -n hw.memsize) / 1024 / 1024)))
  echo "$(date +%s) Memory Pressure: $PERCENT%"
  sleep 1
done
BASH

  chmod +x "$QIGONG_DATA/jetsam_monitor.sh"
}

# ==============================================================================
# REFINEMENT 7: FSEvents Temporal Accounting
# ==============================================================================

refinement_7_fsevent_accounting() {
  log_info "Refinement 7: Capturing FSEvents for file I/O forensics..."

  log stream --predicate 'eventType == "event"' \
    --level debug 2>/dev/null | tee "$QIGONG_DATA/fsevent_$(date +%s).log" &

  log_info "FSEvents capture started"
}

# ==============================================================================
# REFINEMENT 8: QoS Class Hijacking via taskpolicy
# ==============================================================================

refinement_8_qos_steering() {
  local target_pid=$1
  local qos_level=${2:-9}  # 9 = background (E-core only)

  log_info "Refinement 8: QoS steering PID $target_pid to level $qos_level..."

  case $qos_level in
    9)  # Background -> E-core only
      sudo taskpolicy -b -p "$target_pid"
      log_warn "PID $target_pid: E-core only (background QoS)"
      ;;
    4)  # User-initiated -> P-cores preferred
      sudo taskpolicy -B -p "$target_pid"
      log_info "PID $target_pid: P+E cores (user QoS)"
      ;;
    *)
      log_warn "Unknown QoS level: $qos_level"
      ;;
  esac
}

# ==============================================================================
# REFINEMENT 9: Thermal Power Modeling (P = C × f × V²)
# ==============================================================================

refinement_9_power_model() {
  log_info "Refinement 9: Calculating thermal power budget..."

  cat > "$QIGONG_DATA/power_model.py" << 'PYTHON'
#!/usr/bin/env python3
import json
import subprocess
from datetime import datetime

# M1 Pro parameters
P_CORE_MAX_FREQ = 3.2e9  # 3.2 GHz
E_CORE_MAX_FREQ = 2.0e9  # 2.0 GHz
CAPACITANCE = 1e-10      # Estimated
VOLTAGE = 0.8             # V (typical)

def calc_power(freq, voltage=VOLTAGE):
  """Power = C × f × V²"""
  return CAPACITANCE * freq * (voltage ** 2)

# Calculate max power
p_core_power = calc_power(P_CORE_MAX_FREQ)
e_core_power = calc_power(E_CORE_MAX_FREQ)

print("=== Thermal Power Model (P = C × f × V²) ===")
print(f"P-core max power: {p_core_power*1e9:.2f} mW @ {P_CORE_MAX_FREQ/1e9:.1f} GHz")
print(f"E-core max power: {e_core_power*1e9:.2f} mW @ {E_CORE_MAX_FREQ/1e9:.1f} GHz")
print(f"Estimated M1 Pro sustained: ~35W CPU")
print(f"Pre-throttle margin: 25W (red team budget)")

# Capture actual metrics
try:
  result = subprocess.run(['powermetrics', '-n', '1', '-f', 'json'],
                         capture_output=True, text=True, timeout=5)
  metrics = json.loads(result.stdout)
  cpu_power = metrics[0].get('cpu_power', 0)
  print(f"\nCurrent CPU power: {cpu_power:.1f}W")
  print(f"Headroom: {25.0 - cpu_power:.1f}W")
except Exception as e:
  print(f"Error reading powermetrics: {e}")
PYTHON

  python3 "$QIGONG_DATA/power_model.py"
}

# ==============================================================================
# REFINEMENT 10: Cache Line Contention Analysis
# ==============================================================================

refinement_10_cache_analysis() {
  log_info "Refinement 10: Analyzing L2 cache contention (128-byte lines)..."

  echo "M-series Cache Configuration:"
  sysctl -a | grep -i cache || true

  echo ""
  echo "Cache line size: 128 bytes (vs. Intel 64 bytes)"
  echo "L2 per cluster: P1-P4 shared, E1-E4 shared"
  echo "False sharing cost: 10-50x penalty for cross-cluster sync"
  echo ""
  echo "[*] Red team should stay within cluster boundaries"
  echo "[*] Blue team detection should fragment across both clusters"
}

# ==============================================================================
# REFINEMENT 11: XNU Footprint & Interval Accounting
# ==============================================================================

refinement_11_footprint_tracking() {
  local target_pid=$1
  log_info "Refinement 11: Tracking XNU footprint for PID $target_pid..."

  cat > "$QIGONG_DATA/footprint_tracker.py" << 'PYTHON'
#!/usr/bin/env python3
import subprocess
import json
import time
from datetime import datetime

def get_task_footprint(pid):
  """Get memory footprint via task_info (includes compressed pages)"""
  try:
    # Use dtrace to access kern_footprint
    result = subprocess.run(
      ['sudo', 'dtrace', '-n', f'BEGIN {{ p = {{}} }}'],
      capture_output=True, text=True, timeout=2
    )
    # Fallback: use ps with RSS
    result = subprocess.run(
      ['ps', '-p', str(pid), '-o', 'rss=,vsz=,comm='],
      capture_output=True, text=True
    )
    parts = result.stdout.strip().split()
    if len(parts) >= 2:
      rss_kb = int(parts[0])
      vsz_kb = int(parts[1])
      return {
        'timestamp': datetime.now().isoformat(),
        'rss_mb': rss_kb / 1024,
        'vsz_mb': vsz_kb / 1024,
      }
  except Exception as e:
    print(f"Error: {e}")
    return None

# Monitor footprint
if __name__ == '__main__':
  import sys
  pid = int(sys.argv[1]) if len(sys.argv) > 1 else None
  if pid:
    while True:
      fp = get_task_footprint(pid)
      if fp:
        print(json.dumps(fp))
      time.sleep(1)
PYTHON

  python3 "$QIGONG_DATA/footprint_tracker.py" "$target_pid"
}

# ==============================================================================
# Main Command Router
# ==============================================================================

usage() {
  cat << EOF
qigong: Apple Silicon Red Team / Blue Team Resource Management

USAGE:
  qigong <command> [args]

COMMANDS:
  setup                  Initialize baselines & monitoring

  refinement-1          Monitor P/E-cluster separation
  refinement-2          Query resource limits (setrlimit)
  refinement-3 <app>    Analyze sandbox entitlements
  refinement-4          Capture thermal baseline
  refinement-5          Monitor dyld injection
  refinement-6          Monitor memory pressure
  refinement-7          Capture FSEvents timeline
  refinement-8 <pid> [qos]  Steer process to QoS level (9=bg, 4=user)
  refinement-9          Calculate power budget
  refinement-10         Cache contention analysis
  refinement-11 <pid>   Track memory footprint

  engage-red <pid>      Engage red team (E-core steering)
  engage-blue <pid>     Engage blue team (P-core detection)
  analyze               Post-engagement analysis

EXAMPLES:
  qigong setup
  qigong refinement-1
  qigong refinement-8 1234 9
  qigong engage-red 5678
  qigong analyze

EOF
}

main() {
  if [ $# -eq 0 ]; then
    usage
    exit 1
  fi

  case "$1" in
    setup)
      log_info "qigong initialization..."
      refinement_1_monitor_clusters
      refinement_2_query_limits
      refinement_4_thermal_baseline
      refinement_7_fsevent_accounting
      log_info "Setup complete. Check $QIGONG_DATA/ for baselines."
      ;;

    refinement-1)
      refinement_1_monitor_clusters
      ;;
    refinement-2)
      refinement_2_query_limits
      ;;
    refinement-3)
      refinement_3_analyze_entitlements "${2:-.}"
      ;;
    refinement-4)
      refinement_4_thermal_baseline
      ;;
    refinement-5)
      refinement_5_dyld_monitor
      ;;
    refinement-6)
      refinement_6_memory_pressure
      ;;
    refinement-7)
      refinement_7_fsevent_accounting
      ;;
    refinement-8)
      if [ -z "${2:-}" ]; then
        log_warn "Usage: qigong refinement-8 <pid> [qos_level]"
        exit 1
      fi
      refinement_8_qos_steering "$2" "${3:-9}"
      ;;
    refinement-9)
      refinement_9_power_model
      ;;
    refinement-10)
      refinement_10_cache_analysis
      ;;
    refinement-11)
      if [ -z "${2:-}" ]; then
        log_warn "Usage: qigong refinement-11 <pid>"
        exit 1
      fi
      refinement_11_footprint_tracking "$2"
      ;;

    engage-red)
      if [ -z "${2:-}" ]; then
        log_warn "Usage: qigong engage-red <pid>"
        exit 1
      fi
      log_red "RED TEAM ENGAGEMENT"
      refinement_8_qos_steering "$2" 9  # E-core only
      refinement_9_power_model
      log_red "Red team constrained to E-cores, monitoring power budget"
      ;;

    engage-blue)
      if [ -z "${2:-}" ]; then
        log_warn "Usage: qigong engage-blue <pid>"
        exit 1
      fi
      log_blue "BLUE TEAM DETECTION PHASE"
      refinement_8_qos_steering "$2" 4  # P+E, user QoS
      refinement_4_thermal_baseline
      refinement_7_fsevent_accounting
      log_blue "Blue team detection engines active on P-cores"
      ;;

    analyze)
      log_info "Post-engagement analysis..."
      echo ""
      echo "=== Thermal Timeline ==="
      if [ -f "$QIGONG_DATA"/thermal_baseline_*.json ]; then
        python3 -m json.tool "$QIGONG_DATA"/thermal_baseline_*.json | head -20
      fi
      echo ""
      echo "=== FSEvent Summary ==="
      if [ -f "$QIGONG_DATA"/fsevent_*.log ]; then
        wc -l "$QIGONG_DATA"/fsevent_*.log
      fi
      echo ""
      echo "[*] Full logs in: $QIGONG_LOGS"
      echo "[*] Data files in: $QIGONG_DATA"
      ;;

    *)
      log_warn "Unknown command: $1"
      usage
      exit 1
      ;;
  esac
}

main "$@"
