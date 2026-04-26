---
name: ios-wifi-provenance-diff
description: Diagnose why an iPhone's Wi-Fi password row shows but cannot be copied. Diff the per-network provenance attributes between a "can copy" device and a "cannot copy" device, classify each delta as a GF(3) trit, and surface the exact flag the Settings UI gates Copy on. Authorized-owner use only.
---

# ios-wifi-provenance-diff

## Bound triad

```
play    (+1)  iphone-tb-control          ← acquisition (sysdiagnose / backup)
witness ( 0)  performing-mobile-device-  ← runs iLEAPP appleWifiPlist.py
              forensics-with-cellebrite
coplay  (−1)  r2frida                    ← static/dynamic RE of WiFiSettings.bundle
                                           WFPasswordController gate
———————————————————————————————————————————————————————————————————————
                                                          GF(3) sum = 0
```

## When to use

- Two iPhones on the same Apple ID, same SSID. Phone A reveals + copies; Phone B reveals but Copy is greyed.
- User wants to know **which exact attribute** of the known-network record causes the asymmetry, not just "it's a sync thing."
- Building a forensic case where Wi-Fi credential provenance (typed vs synced vs shared) is itself the artifact.

**Not** for:
- Extracting passwords from a device the user does not own. Refuse.
- Bypassing MDM-pushed Wi-Fi profiles. Refuse.

## Causal chain (recap)

The password bytes sync via the **AppleWiFiPassword** keychain view (CKKS). The provenance metadata does not — it's reconstructed locally on the receiving device by `wifid` and written into `/var/preferences/SystemConfiguration/com.apple.wifi.known-networks.plist`. The Settings UI gates Copy on that local metadata, not on the keychain item.

Two predicates evaluated independently in `WiFiSettings.bundle`:
```
REVEAL_OK = LAContext succeeded ∧ keychain item present
COPY_OK   = REVEAL_OK ∧ AddReason=="Manual"
                      ∧ ShareableInfo present
                      ∧ ¬RestrictedToOriginalDevice
```
(Attribute names are reconstructed across iOS 16–18 community RE; exact names on iOS 26+ are confirmed at runtime by step 3 below.)

## Pipeline

### 1. Acquire — both phones

Dispatch via `iphone-tb-control`. Sysdiagnose is preferred (smaller, no decryption):

```sh
# per phone, ECID-bound
pymobiledevice3 diagnostics sysdiagnose ./sysdiag-A
pymobiledevice3 diagnostics sysdiagnose ./sysdiag-B
```

Fallback if sysdiagnose lacks the plist: full unencrypted backup via `idevicebackup2 backup --full`.

Locate the plist:
```sh
find sysdiag-A -name 'com.apple.wifi.known-networks.plist'
```

### 2. Parse — iLEAPP

Use `iLEAPP`'s `appleWifiPlist.py` artifact (already cited in `performing-mobile-device-forensics-with-cellebrite`). It surfaces `AddReason`, `BundleID`, `Hidden`, `__OSSpecific__.{BSSID,networkUsage,CarPlayNetwork}`, `CaptiveProfile.{CaptiveNetwork,UserPortalURL}`.

```sh
python3 -m ileapp -t fs -i sysdiag-A -o ileapp-A
python3 -m ileapp -t fs -i sysdiag-B -o ileapp-B
```

Output: `ileapp-{A,B}/_HTML/WiFi Connections/WiFi Known Networks Info.html` plus a TSV.

For full-attribute fidelity (iLEAPP drops some keys), augment with `mac_apt`'s `airport_preferences.py` which preserves `AddedAt`, `JoinedBySystemAt`, `JoinedByUserAt`, `UpdatedAt`, `LastDiscoveredAt`, `SystemMode`, `PossiblyHiddenNetwork`.

### 3. Confirm the gate predicate (one-time per iOS major)

Pull `/System/Library/PreferenceBundles/WiFiSettings.bundle/WiFiSettings` from an IPSW for the target iOS build. In Binary Ninja or Ghidra:

1. XRef the `@"Copy"` Foundation string.
2. Find `-[WFPasswordController _updateCopyButtonState]` (selector name preserved).
3. Read the predicate immediately above `setCopyButtonEnabled:`.
4. The attribute keys passed into `WiFiManagerClientCopyNetworkProperty` are the canonical names — log them.

Cross-reference those names against the columns iLEAPP emitted in step 2. The match is your gate flag.

For runtime confirmation, hook with `r2frida`:
```
r2 frida://attach/usb//com.apple.Preferences
:i ObjC.classes.WFPasswordController
:i ObjC.classes.WFPasswordController["- _updateCopyButtonState"]
```
Or Frida directly:
```js
var c = ObjC.classes.WFPasswordController["- _updateCopyButtonState"];
Interceptor.attach(c.implementation, {
  onEnter: function() { console.log(ObjC.Object(this.context.x0)._network()); }
});
```

### 4. Diff + classify (GF(3) trit)

Use the companion script `diff.bb` in this skill directory. It loads both plists via `plutil` (no native binary-plist parser in babashka), normalizes the schema across iOS pre-16 (`List of known networks` array) and iOS 16+ (`{ssid_str => entry-map}`), classifies each entry, and emits DuckDB DDL+INSERTs on stdout and a per-SSID diff on stderr.

```sh
# CLI form (run via mcp__flox__run_command or babashka MCP, not the Bash tool)
diff.bb sysdiag-A/.../known-networks.plist sysdiag-B/.../known-networks.plist \
        7046328158928924 <ECID-of-B>
```

Or REPL-loadable via forj into a project nREPL (do **not** use the nash-ducklake REPL — see `feedback_no_forj_nash_ducklake`):
```clojure
(load-file ".../ios-wifi-provenance-diff/diff.bb")
(ios-wifi-provenance.diff/run! plist-a "ECID-A" plist-b "ECID-B")
```

Classification:
```
trit(SSID) = +1 if AddReason == "Manual"          (typed locally)
              0 if AddReason == "iCloudSync"      (Keychain sync)
             −1 if AddReason == "NetworkSharing"  (Share Password sheet)
              0 otherwise (mark unclassified)
```

Per-SSID `:trit-delta` ≠ 0 (mod 3) flags asymmetric provenance — these are the rows whose Copy state will likely diverge between the two phones. Healthy/symmetric SSIDs have `:trit-delta = 0`.

### 5. Persist (reuses `citizen-lab-forensics` DuckDB schema)

`diff.bb` emits the DDL inline; pipe stdout into DuckDB. The schema (defined in `diff.bb` as `schema-ddl`):

```sql
CREATE TABLE IF NOT EXISTS wifi_provenance_diff (
    id INTEGER, ssid VARCHAR NOT NULL, device_ecid VARCHAR NOT NULL,
    add_reason VARCHAR, bundle_id VARCHAR, hidden BOOLEAN, bssid VARCHAR,
    added_at TIMESTAMP, joined_by_system_at TIMESTAMP,
    joined_by_user_at TIMESTAMP, updated_at TIMESTAMP,
    system_mode BOOLEAN, has_shareable_info BOOLEAN,
    has_password_enclave BOOLEAN, provenance_trit TINYINT,
    copy_enabled BOOLEAN,           -- observed UI state, manually labeled
    sysdiag_path VARCHAR, captured_at TIMESTAMP
);
```

GF(3) audit query — non-zero rows are where the gate predicate likely breaks:
```sql
SELECT ssid,
       MOD(SUM(CASE WHEN device_ecid='<A>' THEN provenance_trit ELSE 0 END)
         - SUM(CASE WHEN device_ecid='<B>' THEN provenance_trit ELSE 0 END), 3) AS delta
FROM wifi_provenance_diff
GROUP BY ssid HAVING delta <> 0;
```

## Reverse the asymmetry (no RE needed)

On Phone B for a single SSID:
1. Settings → Wi-Fi → (i) → **Forget This Network**.
2. Rejoin by **typing** the password (don't accept Share Password prompt).
3. New keychain entry created with `AddReason="Manual"` and full `ShareableInfo`. Copy enables.

If retyping fixes it → metadata-vs-bytes split confirmed (the causal-chain model holds). If it doesn't → there's an additional clause in the predicate (Screen Time restriction, MDM profile, or a build-specific iOS bug); go to step 3 to find it.

Note on path selection: steps 1+2+4+5 (acquire → iLEAPP → diff → persist) are sufficient to identify *which* attribute is asymmetric between phones. Step 3 (IPSW + Binary Ninja or `r2frida` runtime hook) is only needed to confirm *why the UI gates on it* — i.e. to verify that the asymmetric attribute is actually the one `setCopyButtonEnabled:` reads. Skip step 3 unless you need that confirmation or the iLEAPP-only diff is inconclusive.

## Anti-patterns

- Trying to read the password directly from the keychain on Phone B and concluding the gate is keychain-side. The bytes are there; the gate is in the plist + Settings binary.
- Using the Bash tool. This is a Clojure-flavored workspace — wrap shell calls via `mcp__flox__run_command` or babashka MCP. The diff/classify step belongs in `babashka` or the project REPL via forj.
- Naming any specific iOS version's attribute keys without re-verifying against the IPSW for that build. The schema rotated between iOS 16 → 17 (keys moved under `__OSSpecific__`); assume rotation again on 26+.
- Recommending Forget+rejoin on a managed Wi-Fi profile (MDM-pushed). It will silently re-push. Check `Settings → General → VPN & Device Management` first.

## Verification

**Smoke test (no device needed).** `diff.bb` ends in a `(comment ...)` block of REPL-callable assertions over synthetic plist EDN — covers `classify`, both schema versions (pre-16 array, 16+ map), end-to-end diff, and SQL escaping. From a fresh bb nREPL (not nash-ducklake): `(load-file ".../diff.bb")` then run the block via forj `eval_comment_block`. Final form returns `:all-smoke-pass` on green.

**Live round-trip** on the bound iPhone Air (ECID `7046328158928924`) and a second iCloud-paired iPhone:
1. Sysdiagnose both.
2. Pick one SSID where Phone A copies and Phone B doesn't.
3. Run pipeline → expect non-zero per-SSID trit sum.
4. Forget+retype on Phone B → re-sysdiag → re-run → expect trit sum 0 and Copy enabled.

Pass condition: the attribute the diff identifies in step 3 is the same attribute whose value flipped after the retype.

## See also

- `iphone-tb-control` — acquisition (sibling, +1 in triad)
- `performing-mobile-device-forensics-with-cellebrite` — iLEAPP recipe (sibling, 0)
- `r2frida`, `ghidra-mcp`, `radare2-hatchery` — RE of `WiFiSettings.bundle` (sibling, −1)
- `citizen-lab-forensics` — DuckDB schema source
- `bartons-law-cech` (memory note, not a skill) — the H¹ framing: "Copy disabled" is a cocycle obstruction at the gauge layer
