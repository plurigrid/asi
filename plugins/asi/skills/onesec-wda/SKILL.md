---
name: onesec-wda
description: Automate "one sec" app-blocking setup on iOS via Shortcuts automations using WebDriverAgent (WDA). Use when the user wants to bulk-configure one sec for multiple apps on a connected iPhone.
---

# one sec WDA Automation

Bulk-create iOS Shortcuts automations that trigger "one sec" when apps are opened, driven by WebDriverAgent.

## Prerequisites

1. **iPhone connected via USB** with developer mode enabled
2. **WebDriverAgent running** via xcodebuild:
   ```bash
   xcodebuild test-without-building \
     -xctestrun <path-to>/WebDriverAgentRunner_iphoneos*.xctestrun \
     -destination id=<DEVICE_UDID> \
     -allowProvisioningUpdates
   ```
3. **WDA accessible** at `http://localhost:8100` (use `pymobiledevice3 remote start-tunnel` + port forward if needed)
4. **one sec app installed** on the device with Shortcuts integration enabled

## Usage

```bash
# Test with one app first
python3 /path/to/onesec_setup.py --test

# Run for all apps
python3 /path/to/onesec_setup.py
```

The script is at: `<skill-dir>/scripts/onesec_setup.py`

## Workflow per App

1. Tap "+" on Shortcuts Automation tab
2. Select "App" trigger
3. Search for and select the target app
4. Confirm "Is Opened" trigger, tap Done
5. Search for "one sec" action
6. Select "Activate one sec (when app opens)"
7. Tap Done to save

Screenshots are saved to `/tmp/onesec_step*` and `/tmp/onesec_fail*` for debugging.

## Customization

Edit `APPS_TO_PROTECT` list in the script. Move completed apps to `ALREADY_DONE` to skip them on re-runs.

## WDA Helpers

The script provides reusable WDA functions (no pip dependencies):
- `wda(method, path, data)` — raw HTTP to WDA
- `find(using, value)` / `find_one(using, value)` — element lookup
- `tap(element_id)` / `tap_name(name)` / `tap_label(label)` — tap elements
- `type_text(text)` — type into active element
- `swipe(x1, y1, x2, y2)` — drag gesture
- `screenshot(path)` — save screenshot as PNG

## Troubleshooting

- **WDA connection refused**: Ensure xcodebuild test is running and port 8100 is reachable
- **pymobiledevice3 tunnel timeout**: Restart tunnel with `sudo pymobiledevice3 remote start-tunnel`
- **Element not found**: Check screenshots in `/tmp/onesec_fail_*` to see actual UI state
- **App not in picker**: App name must match exactly as shown on device home screen
