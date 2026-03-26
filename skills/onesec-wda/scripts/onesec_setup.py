#!/usr/bin/env python3
"""Automate one sec setup for all apps via WDA."""

import json
import time
import urllib.request
import sys

WDA_BASE = "http://localhost:8100"
SID = None

# Apps to set up (from earlier device scan, excluding one sec itself and system utilities)
APPS_TO_PROTECT = [
    "Tally", "Airbnb", "Claude", "Keynote", "Numbers", "Pages", "iMovie",
    "GarageBand", "Apple Store", "Petra", "Beeper", "Pixel Pals", "Clipper",
    "Costco", "Duo Mobile", "Fastmail", "Termux", "Goblin Tools",
    "Authenticator", "Google Maps", "NotebookLM", "Gemini", "Discord",
    "Pi", "Shopify", "2048", "Mercury", "MagicTodoWatch", "ChatGPT",
    "Partiful", "Business", "Poe", "Reddit", "Spotify", "Starlink",
    "Taskrabbit", "TD Bank (US)", "Uber", "Vacasa", "Vrbo", "Waymo",
    "GoblinTools", "PayPal", "Tailscale", "Venmo", "Signal", "Telegram",
    "Hustle",
    # Visible system apps
    "App Store", "Files", "Fitness", "Health", "Home",
    "Maps", "Messages", "Music",
    "Wallet", "Passwords", "Settings",
    "Translate", "Voice Memos", "Calculator", "Camera",
    "FaceTime", "Find My", "Freeform", "Games", "Books",
    "Journal", "Calendar", "Mail", "Notes",
    "Phone", "Safari", "Photos", "Clock",
    "News", "Podcasts", "Reminders", "Stocks",
    "Tips", "TV",
]

# Already set up
ALREADY_DONE = ["Weather"]


def wda(method, path, data=None):
    url = f"{WDA_BASE}{path}"
    body = json.dumps(data).encode() if data else None
    req = urllib.request.Request(url, data=body, method=method,
                                headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read())
    except Exception as e:
        print(f"  WDA error: {e}")
        return None


def find(using, value):
    r = wda("POST", f"/session/{SID}/elements", {"using": using, "value": value})
    if r and r.get("value"):
        return [e["ELEMENT"] for e in r["value"]]
    return []


def find_one(using, value):
    elems = find(using, value)
    return elems[0] if elems else None


def tap(element_id):
    wda("POST", f"/session/{SID}/element/{element_id}/click", {})


def tap_name(name):
    eid = find_one("name", name)
    if eid:
        tap(eid)
        return True
    print(f"  Could not find element: {name}")
    return False


def tap_label(label):
    eid = find_one("accessibility id", label)
    if eid:
        tap(eid)
        return True
    # Fallback to name
    return tap_name(label)


def screenshot(path):
    r = wda("GET", f"/session/{SID}/screenshot")
    if r and r.get("value"):
        import base64
        with open(path, "wb") as f:
            f.write(base64.b64decode(r["value"]))


def type_text(text):
    # Find active element and type
    r = wda("GET", f"/session/{SID}/element/active")
    if r and r.get("value") and r["value"].get("ELEMENT"):
        eid = r["value"]["ELEMENT"]
        wda("POST", f"/session/{SID}/element/{eid}/value", {"value": list(text)})


def swipe(start_x, start_y, end_x, end_y, duration=0.5):
    wda("POST", f"/session/{SID}/wda/dragfromtoforduration", {
        "fromX": start_x, "fromY": start_y,
        "toX": end_x, "toY": end_y,
        "duration": duration
    })


def setup_one_app(app_name):
    """Create automation: When [app_name] is opened → Activate one sec"""
    print(f"\n{'='*50}")
    print(f"Setting up: {app_name}")
    print(f"{'='*50}")

    # Step 1: Tap "+" to add new automation
    if not tap_name("automations.add"):
        print("  FAIL: Can't find + button")
        return False
    time.sleep(1.5)

    # Step 2: Find and tap "App" trigger (for "When app is opened")
    # The new automation screen shows trigger options
    time.sleep(1)
    screenshot(f"/tmp/onesec_step2_{app_name[:10]}.png")

    # Look for "App" option
    if not tap_name("App"):
        # Try alternative names
        if not tap_name("App Is Opened"):
            if not tap_label("App"):
                print("  FAIL: Can't find App trigger")
                screenshot(f"/tmp/onesec_fail_{app_name[:10]}.png")
                return False
    time.sleep(1.5)

    # Step 3: We should now see the app picker. Search for the app.
    screenshot(f"/tmp/onesec_step3_{app_name[:10]}.png")

    # Find search field and type app name
    search = find_one("class name", "XCUIElementTypeSearchField")
    if search:
        tap(search)
        time.sleep(0.5)
        type_text(app_name)
        time.sleep(1)
    else:
        # Try to find the app in the list directly
        pass

    # Step 4: Select the app from results
    time.sleep(1)
    app_elem = find_one("name", app_name)
    if not app_elem:
        # Try partial match
        r = wda("POST", f"/session/{SID}/elements", {"using": "partial link text", "value": app_name})
        if r and r.get("value"):
            app_elem = r["value"][0]["ELEMENT"]

    if app_elem:
        tap(app_elem)
        time.sleep(0.5)
    else:
        print(f"  WARN: Could not find '{app_name}' in picker, trying label match")
        if not tap_label(app_name):
            print(f"  FAIL: Could not select app '{app_name}'")
            # Go back
            tap_name("Cancel") or tap_name("Back")
            time.sleep(0.5)
            return False

    # Step 5: Ensure "Is Opened" is selected (should be default), tap Next/Done
    time.sleep(1)
    screenshot(f"/tmp/onesec_step5_{app_name[:10]}.png")
    tap_name("Done") or tap_name("Next")
    time.sleep(1.5)

    # Step 6: Now we need to add the one sec action
    # Search for "one sec" in the actions
    screenshot(f"/tmp/onesec_step6_{app_name[:10]}.png")

    search2 = find_one("class name", "XCUIElementTypeSearchField")
    if search2:
        tap(search2)
        time.sleep(0.5)
        type_text("one sec")
        time.sleep(1.5)

    # Step 7: Tap "Activate one sec (when app opens)" action
    onesec_action = find_one("name", "Activate one sec (when app opens)")
    if not onesec_action:
        # Try partial
        for name in ["Activate one sec", "one sec"]:
            onesec_action = find_one("name", name)
            if onesec_action:
                break

    if onesec_action:
        tap(onesec_action)
        time.sleep(1)
    else:
        print(f"  FAIL: Could not find one sec action")
        screenshot(f"/tmp/onesec_fail_action_{app_name[:10]}.png")
        tap_name("Cancel") or tap_name("Back")
        time.sleep(0.5)
        return False

    # Step 8: Tap Done to save the automation
    time.sleep(1)
    screenshot(f"/tmp/onesec_step8_{app_name[:10]}.png")
    tap_name("Done") or tap_name("Next")
    time.sleep(1)

    # May need another Done
    tap_name("Done")
    time.sleep(1)

    print(f"  SUCCESS: {app_name}")
    return True


def main():
    global SID

    # Create or reuse session
    r = wda("POST", "/session", {
        "capabilities": {
            "alwaysMatch": {
                "bundleId": "com.apple.shortcuts",
                "shouldWaitForQuiescence": False
            }
        }
    })
    if not r:
        print("Failed to create WDA session")
        sys.exit(1)

    SID = r.get("sessionId") or r.get("value", {}).get("sessionId")
    print(f"WDA Session: {SID}")

    # Navigate to Automation tab
    time.sleep(1)
    tap_name("Automation")
    time.sleep(1)

    # First, do a test run with one app to verify the flow
    apps = [a for a in APPS_TO_PROTECT if a not in ALREADY_DONE]

    if "--test" in sys.argv:
        apps = apps[:1]
        print(f"TEST MODE: Only setting up '{apps[0]}'")

    success = []
    failed = []

    for i, app in enumerate(apps):
        print(f"\n[{i+1}/{len(apps)}] ", end="")
        ok = setup_one_app(app)
        if ok:
            success.append(app)
        else:
            failed.append(app)

        # Small delay between apps
        time.sleep(0.5)

    print(f"\n\n{'='*50}")
    print(f"DONE: {len(success)} succeeded, {len(failed)} failed")
    if failed:
        print(f"Failed apps: {failed}")
    print(f"{'='*50}")


if __name__ == "__main__":
    main()
