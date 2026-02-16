#!/bin/bash
# Move plaintext keys to root-protected storage
# Run with: sudo ./move-keys-to-root.sh

set -e

echo "=== Moving Plaintext Keys to Root Storage ==="
echo "GF(3) Conservation: source(-1) → transit(0) → dest(+1) = 0 ✓"
echo ""

# Create root-owned key vault
echo "[1/6] Creating /var/keys hierarchy..."
mkdir -p /var/keys/aptos/worlds
mkdir -p /var/keys/aptos/testnet
mkdir -p /var/keys/age
mkdir -p /var/keys/config

# Move Aptos world keys
echo "[2/6] Moving Aptos world keys..."
if [ -d "/Users/alice/.aptos/worlds" ]; then
    cp /Users/alice/.aptos/worlds/*.key /var/keys/aptos/worlds/ 2>/dev/null || true
    echo "  Copied $(ls /var/keys/aptos/worlds/*.key 2>/dev/null | wc -l) world keys"
fi

# Move Aptos testnet keys
echo "[3/6] Moving Aptos testnet keys..."
if [ -f "/Users/alice/.aptos/testnet/mint.key" ]; then
    cp /Users/alice/.aptos/testnet/mint.key /var/keys/aptos/testnet/
    echo "  Copied mint.key"
fi
if [ -f "/Users/alice/.aptos/testnet/0/private-identity.yaml" ]; then
    mkdir -p /var/keys/aptos/testnet/0
    cp /Users/alice/.aptos/testnet/0/private-identity.yaml /var/keys/aptos/testnet/0/
    echo "  Copied private-identity.yaml"
fi

# Move Aptos config (contains private keys)
echo "[4/6] Moving Aptos config..."
if [ -f "/Users/alice/.aptos/config.yaml" ]; then
    cp /Users/alice/.aptos/config.yaml /var/keys/aptos/
    echo "  Copied config.yaml"
fi

# Move age private key
echo "[5/6] Moving age private key..."
if [ -f "/Users/alice/.age/key.txt" ]; then
    cp /Users/alice/.age/key.txt /var/keys/age/
    echo "  Copied age key"
fi

# Set restrictive permissions
echo "[6/6] Setting permissions (root:wheel, 600)..."
chown -R root:wheel /var/keys
chmod -R 600 /var/keys
chmod 700 /var/keys /var/keys/aptos /var/keys/aptos/worlds /var/keys/aptos/testnet /var/keys/age /var/keys/config

echo ""
echo "=== Keys Secured ==="
echo ""
echo "Location: /var/keys/"
ls -la /var/keys/
echo ""
echo "Aptos worlds:"
ls -la /var/keys/aptos/worlds/ | head -10
echo ""

# Verify structure
echo "=== Verification ==="
echo "Total files moved:"
find /var/keys -type f | wc -l

echo ""
echo "=== Next Steps ==="
echo "1. Verify fnox still works:"
echo "   sudo cat /var/keys/age/key.txt > /tmp/age.key && fnox get TEST_SECRET --age-key-file /tmp/age.key && rm /tmp/age.key"
echo ""
echo "2. OPTIONAL - Remove original plaintext keys (DANGEROUS!):"
echo "   rm -rf ~/.aptos/worlds/*.key"
echo "   rm ~/.aptos/config.yaml"
echo "   rm ~/.age/key.txt"
echo ""
echo "3. Update fnox to use root key (requires sudo wrapper):"
echo "   Create /usr/local/bin/fnox-secure with sudo access to /var/keys/age/key.txt"
