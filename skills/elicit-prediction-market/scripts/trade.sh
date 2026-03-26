#!/bin/bash
# Usage: ./trade.sh [login|me|markets|market|preview|buy|sell|claim|portfolio|users|trades]
#
# Examples:
#   ./trade.sh login
#   ./trade.sh markets
#   ./trade.sh market 5
#   ./trade.sh preview buy 5 yes 50      # preview buying $50 YES on market 5
#   ./trade.sh preview sell 5 yes 10     # preview selling 10 YES shares on market 5
#   ./trade.sh buy 5 yes 50             # buy $50 YES on market 5
#   ./trade.sh buy 5 no 50              # buy $50 NO on market 5
#   ./trade.sh sell 5 yes 10            # sell 10 YES shares on market 5
#   ./trade.sh claim 4                  # claim payout from resolved market 4
#   ./trade.sh portfolio                # your positions + P&L
#   ./trade.sh users                    # leaderboard
#   ./trade.sh trades 5                 # trade history for market 5

BASE="https://elicit.attic.codes"
JAR="/tmp/elicit_cookies"
CSRF="-H X-Basin-Request:1"
CT="-H Content-Type:application/json"

outcome_num() {
  case "$1" in
    yes|YES|1) echo 1 ;;
    no|NO|0) echo 0 ;;
    *) echo "$1" ;;
  esac
}

case "$1" in
  login)
    curl -s -c "$JAR" -X POST "$BASE/api/auth/login" \
      $CT -d '{"username":"yulia","password":"normalizedvector"}' | python3 -m json.tool
    ;;
  me)
    curl -s -b "$JAR" "$BASE/api/auth/me" | python3 -m json.tool
    ;;
  markets)
    curl -s -b "$JAR" "$BASE/api/markets" | python3 -c "
import sys,json
data = json.load(sys.stdin)
for m in data['markets']:
    s = m['status']
    yes_p = m['outcomes'][1]['probability']*100
    print(f\"  {m['id']:>2}  {yes_p:5.1f}% YES  {m['num_trades']:>2}t  \${m['volume']:>8.0f}  {s:<20s}  {m['question'][:60]}\")
"
    ;;
  market)
    curl -s -b "$JAR" "$BASE/api/markets/$2" | python3 -m json.tool
    ;;
  preview)
    ACTION="$2"; MID="$3"; SIDE=$(outcome_num "$4"); AMT="$5"
    curl -s -b "$JAR" "$BASE/api/markets/$MID/preview?action=$ACTION&outcome=$SIDE&amount=$AMT" | python3 -m json.tool
    ;;
  buy)
    MID="$2"; SIDE=$(outcome_num "$3"); AMT="$4"
    curl -s -b "$JAR" -X POST "$BASE/api/markets/$MID/buy" \
      $CT -H "X-Basin-Request: 1" \
      -d "{\"outcome\": $SIDE, \"amount\": $AMT}" | python3 -m json.tool
    ;;
  sell)
    MID="$2"; SIDE=$(outcome_num "$3"); SHARES="$4"
    curl -s -b "$JAR" -X POST "$BASE/api/markets/$MID/sell" \
      $CT -H "X-Basin-Request: 1" \
      -d "{\"outcome\": $SIDE, \"shares\": $SHARES}" | python3 -m json.tool
    ;;
  claim)
    curl -s -b "$JAR" -X POST "$BASE/api/markets/$2/claim" \
      $CT -H "X-Basin-Request: 1" -d '{}' | python3 -m json.tool
    ;;
  portfolio)
    curl -s -b "$JAR" "$BASE/api/users/10" | python3 -c "
import sys,json
u = json.load(sys.stdin)
print(f\"User: {u['display_name']} | Balance: \${u['balance']:.2f} | Realized P&L: \${u['total_realized_pnl']:.2f}\")
for mid, outcomes in u.get('positions',{}).items():
    for oidx, pos in outcomes.items():
        side = 'YES' if oidx == '1' else 'NO'
        print(f\"  Market {mid}: {pos['shares']:.2f} {side} shares @ \${pos['avg_cost']:.4f} avg | Unrealized: \${pos['unrealized_pnl']:.2f}\")
"
    ;;
  users)
    curl -s -b "$JAR" "$BASE/api/users/directory" | python3 -c "
import sys,json
users = sorted(json.load(sys.stdin)['users'], key=lambda u: -u['balance'])
for u in users:
    print(f\"  {u['id']:>2}  \${u['balance']:>10.2f}  {u['display_name']:<15s}  {u['role']}\")
"
    ;;
  trades)
    curl -s -b "$JAR" "$BASE/api/markets/$2/trades?limit=20" | python3 -c "
import sys,json
data = json.load(sys.stdin)
for t in data['trades']:
    pnl = f\" P&L:\${t['realized_pnl']:.2f}\" if 'realized_pnl' in t and t.get('action')=='sell' else ''
    print(f\"  {t['action']:>4} {t['outcome_label']:>3} {t['shares']:>10.2f} shares  \${t['cost']:>8.2f}  by {t['username']:<12s}{pnl}\")
"
    ;;
  history)
    curl -s -b "$JAR" "$BASE/api/markets/$2/history" | python3 -c "
import sys,json,datetime
data = json.load(sys.stdin)
for h in data['history']:
    ts = datetime.datetime.fromtimestamp(h['t']/1000).strftime('%m/%d %H:%M')
    print(f\"  {ts}  NO:{h['p'][0]*100:5.1f}%  YES:{h['p'][1]*100:5.1f}%\")
"
    ;;
  *)
    echo "Usage: $0 [login|me|markets|market|preview|buy|sell|claim|portfolio|users|trades|history]"
    echo ""
    echo "  login                       - authenticate"
    echo "  me                          - current user"
    echo "  markets                     - list all markets"
    echo "  market <id>                 - market detail"
    echo "  preview buy <id> yes <amt>  - preview buy"
    echo "  preview sell <id> yes <n>   - preview sell"
    echo "  buy <id> yes|no <amount>    - place buy"
    echo "  sell <id> yes|no <shares>   - place sell"
    echo "  claim <id>                  - claim payout"
    echo "  portfolio                   - your positions"
    echo "  users                       - leaderboard"
    echo "  trades <id>                 - market trade log"
    echo "  history <id>                - price history"
    ;;
esac
