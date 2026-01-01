#!/bin/bash
# fnox-secure: wrapper to use fnox with root-protected age key
# Install: sudo cp fnox-secure-wrapper.sh /usr/local/bin/fnox-secure && sudo chmod +x /usr/local/bin/fnox-secure

# Temporary key file (only accessible during command execution)
TEMP_KEY=$(mktemp)
trap "rm -f $TEMP_KEY" EXIT

# Copy root key to temp (requires sudo)
sudo cat /var/keys/age/key.txt > "$TEMP_KEY" 2>/dev/null
if [ $? -ne 0 ]; then
    echo "Error: Cannot access /var/keys/age/key.txt (need sudo)"
    exit 1
fi

chmod 600 "$TEMP_KEY"

# Run fnox with the temporary key
~/.cargo/bin/fnox --age-key-file "$TEMP_KEY" "$@"
