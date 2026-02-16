#!/usr/bin/env bash
set -e

OUI_DIR="$HOME/i/asi/docs/oui"
STATE_DIR="$HOME/i/asi/docs"
TS=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

mkdir -p "$OUI_DIR"

echo "🌐 Fetching OUI databases..."
curl -sL "https://standards-oui.ieee.org/oui/oui.txt" -o "$OUI_DIR/ieee_oui.txt" &
curl -sL "https://standards-oui.ieee.org/oui28/mam.txt" -o "$OUI_DIR/ieee_mam.txt" &
curl -sL "https://standards-oui.ieee.org/oui36/oui36.txt" -o "$OUI_DIR/ieee_mas.txt" &
curl -sL "https://www.wireshark.org/download/automated/data/manuf" -o "$OUI_DIR/wireshark_manuf.txt" &
wait
echo "✅ OUI databases: $OUI_DIR"

echo "📡 Scanning network..."
ARP_JSON=$(arp -a | grep -v incomplete | awk '{
  gsub(/[()]/, "", $2);
  gsub(/[()]/, "", $4);
  if ($2 ~ /^[0-9]/) print "{\"ip\":\"" $2 "\",\"mac\":\"" $4 "\",\"host\":\"" $1 "\"}"
}' | jq -s '.')

cat > "$STATE_DIR/network_snapshot.json" << EOF
{
  "timestamp": "$TS",
  "interface": "en0",
  "devices": $ARP_JSON,
  "oui_db": "$OUI_DIR/ieee_oui.txt"
}
EOF
echo "💾 Serialized: $STATE_DIR/network_snapshot.json"

echo ";; Snapshot $TS" >> "$STATE_DIR/network_state.edn"

echo "🔍 Google OUIs: $(grep -ci 'google' "$OUI_DIR/ieee_oui.txt" 2>/dev/null || echo 0)"
echo "🔍 Tesla OUIs: $(grep -ci 'tesla' "$OUI_DIR/ieee_oui.txt" 2>/dev/null || echo 0)"
echo "🍎 Apple OUIs: $(grep -ci 'apple' "$OUI_DIR/ieee_oui.txt" 2>/dev/null || echo 0)"

echo -e "\n📋 Devices:"
echo "$ARP_JSON" | jq -r '.[] | "\(.ip)\t\(.mac)\t\(.host)"' | while read line; do
  MAC=$(echo "$line" | cut -f2 | tr -d ':' | cut -c1-6 | tr '[:lower:]' '[:upper:]')
  VENDOR=$(grep -i "^$MAC" "$OUI_DIR/wireshark_manuf.txt" 2>/dev/null | head -1 | cut -f2- || echo "?")
  echo -e "$line\t$VENDOR"
done | column -t -s $'\t' | head -20

echo -e "\n🛠️  recon-env: flox activate -d ~/i/recon-env"
