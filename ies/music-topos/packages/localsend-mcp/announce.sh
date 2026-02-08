#!/bin/bash
# Gay-colored LocalSend announcer with varying speech rate
# Voice: Samantha (best English)
# Base rate: 69, varied by Gay.jl color chain

DNS_NAME="causality.pirate-dragon.ts.net"
PORT="53317"
IP="100.69.33.107"
VOICE="Samantha"
BASE_RATE=69

# SplitMix64 constants
GAY_SEED=7523094288207667311  # 0x6761795f636f6c6f
GOLDEN=11400714819323198485   # 0x9e3779b97f4a7c15

seed=$GAY_SEED

splitmix64() {
    seed=$(( (seed + GOLDEN) & 0xFFFFFFFFFFFFFFFF ))
    local z=$seed
    z=$(( ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF ))
    z=$(( ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF ))
    echo $(( z ^ (z >> 31) ))
}

get_rate() {
    local val=$(splitmix64)
    # Rate varies from 50 to 250, centered around 69
    local variation=$(( (val % 100) - 50 ))
    echo $(( BASE_RATE + variation + 100 ))  # 119 to 219 range for audibility
}

get_color() {
    local val=$(splitmix64)
    local r=$(( (val >> 16) & 0xFF ))
    local g=$(( (val >> 8) & 0xFF ))
    local b=$(( val & 0xFF ))
    printf "#%02X%02X%02X" $r $g $b
}

announce() {
    local rate=$(get_rate)
    local color=$(get_color)
    
    echo "🌈 Color: $color | Rate: $rate"
    
    say -v "$VOICE" -r $rate "Attention! LocalSend peer available! Connect to causality dot pirate dragon dot t s dot net, port 53317. I repeat: causality, pirate dragon, t s net, port 5 3 3 1 7. IP address: 100 dot 69 dot 33 dot 107. Awaiting file transfers now!" &
}

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  🏴‍☠️ LocalSend Announcer - causality.pirate-dragon.ts.net    ║"
echo "║  Port: $PORT | IP: $IP                              ║"
echo "║  Voice: $VOICE | Base Rate: $BASE_RATE                           ║"
echo "╚══════════════════════════════════════════════════════════════╝"

# Redundant announcements
for i in {1..5}; do
    echo ""
    echo "📢 Announcement $i/5"
    announce
    sleep 8
done

echo ""
echo "✅ All announcements complete!"
echo "🔗 Send files to: http://$DNS_NAME:$PORT"
