#!/usr/bin/env python3
"""Bulk-create iOS Shortcuts automations for one sec app via WebDriverAgent."""
import json, time, sys, urllib.request, urllib.error

WDA_URL = "http://localhost:8100"
SCREENSHOT_DIR = "/tmp"

APPS_TO_PROTECT = [
    "Instagram", "Twitter", "TikTok", "Reddit", "YouTube",
    "Facebook", "Snapchat", "LinkedIn", "Threads", "Bluesky",
]
ALREADY_DONE = []

def wda(method, path, data=None):
    body = json.dumps(data).encode() if data else None
    req = urllib.request.Request(f"{WDA_URL}{path}", data=body, method=method,
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return json.loads(resp.read())
    except urllib.error.URLError as e:
        print(f"WDA error: {e}", file=sys.stderr)
        return None

def find(using, value):
    r = wda("POST", "/session/0/elements", {"using": using, "value": value})
    return r.get("value", []) if r else []

def find_one(using, value):
    r = wda("POST", "/session/0/element", {"using": using, "value": value})
    return r.get("value", {}).get("ELEMENT") if r else None

def tap(element_id):
    wda("POST", f"/session/0/element/{element_id}/click")

def tap_name(name):
    el = find_one("name", name)
    if el: tap(el)
    else: print(f"  ! not found: {name}", file=sys.stderr)
    return el is not None

def tap_label(label):
    el = find_one("accessibility id", label)
    if el: tap(el)
    else: print(f"  ! label not found: {label}", file=sys.stderr)
    return el is not None

def type_text(text):
    wda("POST", "/session/0/element/0/value", {"value": list(text)})

def screenshot(path):
    r = wda("GET", "/screenshot")
    if r and "value" in r:
        import base64
        with open(path, "wb") as f:
            f.write(base64.b64decode(r["value"]))

def swipe(x1, y1, x2, y2, duration=0.5):
    wda("POST", "/session/0/wda/dragfromtoforduration",
        {"fromX": x1, "fromY": y1, "toX": x2, "toY": y2, "duration": duration})

def setup_one_app(app_name):
    print(f"Setting up: {app_name}")
    time.sleep(0.5)

    # Step 1: Tap + to create automation
    if not tap_name("Add"): tap_label("Add")
    time.sleep(1)

    # Step 2: Select App trigger
    tap_name("App")
    time.sleep(1)

    # Step 3: Search for app
    tap_name("Choose")
    time.sleep(0.5)
    type_text(app_name)
    time.sleep(1)
    tap_name(app_name)
    time.sleep(0.5)

    # Step 4: Confirm Is Opened, tap Done
    tap_name("Done")
    time.sleep(1)

    # Step 5: Search for one sec action
    type_text("one sec")
    time.sleep(1)
    tap_name("Activate one sec (when app opens)")
    time.sleep(0.5)

    # Step 6: Save
    tap_name("Done")
    time.sleep(1)
    screenshot(f"{SCREENSHOT_DIR}/onesec_done_{app_name}.png")
    print(f"  done: {app_name}")

def main():
    test_mode = "--test" in sys.argv
    apps = APPS_TO_PROTECT[:1] if test_mode else APPS_TO_PROTECT

    # Verify WDA connection
    status = wda("GET", "/status")
    if not status:
        print("ERROR: Cannot reach WDA at", WDA_URL, file=sys.stderr)
        print("Start WDA first: xcodebuild test-without-building ...", file=sys.stderr)
        sys.exit(1)

    print(f"WDA connected. Setting up {len(apps)} app(s)...")
    for app in apps:
        if app in ALREADY_DONE:
            print(f"  skip (already done): {app}")
            continue
        try:
            setup_one_app(app)
        except Exception as e:
            screenshot(f"{SCREENSHOT_DIR}/onesec_fail_{app}.png")
            print(f"  FAILED: {app}: {e}", file=sys.stderr)

if __name__ == "__main__":
    main()
