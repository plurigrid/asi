"""
KB360 Pro as KMonad string diagrams via DisCoPy.

KMonad pipeline → symmetric monoidal category:
  Wires = typed event streams
  Boxes = processing stages
  >> = sequential composition
  @ = parallel (tensor) composition
  Trace = layer feedback loop
"""

from discopy.monoidal import Ty, Box, Id, Diagram

# =============================================================
# Wire types
# =============================================================
Key = Ty('Key')
Event = Ty('Event')
Layer = Ty('Layer')
HID = Ty('HID')
USB = Ty('USB')
BLE = Ty('BLE')
LED = Ty('LED')
Profile = Ty('Profile')

import os
os.makedirs('/Users/alice/worlds/figures', exist_ok=True)

def save(diagram, name, figsize=(12, 6)):
    path = f'/Users/alice/worlds/figures/{name}.png'
    try:
        diagram.draw(figsize=figsize, path=path, margins=(0.3, 0.15))
        print(f"OK: {name}.png")
    except Exception as e:
        print(f"ERR {name}: {e}")

# =============================================================
# 1. Single key pipeline (KMonad: defsrc → deflayer → emit)
# =============================================================
scan = Box('scan', Key, Event)
debounce = Box('debounce', Event, Event)
layer_lookup = Box('layer_lookup', Event @ Layer, HID @ Layer)
emit = Box('emit', HID, USB @ BLE)

# Key @ Layer → Event @ Layer → HID @ Layer
single_key = (scan @ Id(Layer)) >> layer_lookup
save(single_key, 'kb360-1-single-key')

# =============================================================
# 2. Four layers as parallel boxes (KMonad: deflayer ×4)
# Each layer is Event → HID
# =============================================================
base = Box('Base_0', Event, HID)
kp = Box('kp_1', Event, HID)
fn = Box('fn_2', Event, HID)
mod = Box('Mod_3', Event, HID)

four_layers = base @ kp @ fn @ mod
save(four_layers, 'kb360-2-four-layers', figsize=(14, 4))

# =============================================================
# 3. Split keyboard as tensor product then merge
# Left ⊗ Right → merge → single Event stream
# =============================================================
left_scan = Box('Left_5x10', Key, Event)
right_scan = Box('Right_5x10', Key, Event)
ble_merge = Box('BLE_merge', Event @ Event, Event)

split = (left_scan @ right_scan) >> ble_merge
save(split, 'kb360-3-split')

# =============================================================
# 4. Tap-hold decision (KMonad: tap-hold 200 ...)
# Event → HID ⊗ Layer (tap produces keycode, hold produces layer)
# =============================================================
tap_hold = Box('tap-hold_200ms', Event, HID @ Layer)
save(tap_hold, 'kb360-4-tap-hold')

# =============================================================
# 5. Layer multiplexer: Event ⊗ Layer → HID
# Selects which deflayer to route through
# =============================================================
layer_mux = Box('layer_mux', Event @ Layer, HID)
save(layer_mux, 'kb360-5-layer-mux')

# =============================================================
# 6. Full pipeline with layer threading
#
# Key @ Layer
#   → [scan ⊗ id_Layer]
#   → Event @ Layer
#   → [layer_lookup]
#   → HID @ Layer
#   → [Mod_shortcuts]
#   → HID @ Layer @ LED
#   → [emit ⊗ LED_driver]
#   → USB @ BLE @ LED
#
# The Layer wire threads through as state,
# in KMonad this is the implicit layer stack.
# =============================================================

stage1 = Box('matrix_scan', Key, Event)
stage2 = Box('layer_lookup', Event @ Layer, HID @ Layer)
stage3 = Box('Mod_shortcuts', HID @ Layer, HID @ Layer @ LED)
stage4_emit = Box('HID_emit', HID, USB @ BLE)
stage4_led = Box('WS2812', Layer @ LED, LED)

pipeline = (
    (stage1 @ Id(Layer))            # Key @ Layer → Event @ Layer
    >> stage2                        # Event @ Layer → HID @ Layer
    >> stage3                        # HID @ Layer → HID @ Layer @ LED
    >> (stage4_emit @ stage4_led)    # HID @ (Layer @ LED) → (USB @ BLE) @ LED
)

save(pipeline, 'kb360-6-full-pipeline', figsize=(16, 8))

# =============================================================
# 7. KMonad defsrc → deflayer with Copy (Markov category)
# A single physical key fans out to all layers
# =============================================================
try:
    from discopy.markov import Copy
    defsrc = Box('defsrc', Key, Event)
    copy = Copy(Event, 2)

    deflayer_base = Box('deflayer_base', Event, HID)
    deflayer_fn = Box('deflayer_fn', Event, HID)

    kmonad_fan = defsrc >> copy >> (deflayer_base @ deflayer_fn)
    save(kmonad_fan, 'kb360-7-kmonad-deflayer', figsize=(12, 8))
except Exception as e:
    print(f"ERR markov: {e}")

# =============================================================
# 8. Concatenative stack view
# KMonad processes keys like a Forth stack:
#   push(event) → lookup(layer) → emit(hid)
# =============================================================
push = Box('push', Key, Key @ Event)
lookup = Box('lookup', Key @ Event @ Layer, Key @ HID)
emit_stack = Box('emit', Key @ HID, Key @ USB)

stack_pipeline = (
    (push @ Id(Layer))          # Key @ Layer → Key @ Event @ Layer
    >> lookup                    # Key @ Event @ Layer → Key @ HID
    >> emit_stack                # Key @ HID → Key @ USB
)
save(stack_pipeline, 'kb360-8-concat-stack', figsize=(14, 6))

# =============================================================
# 9. Profile switching as morphism
# Mod+N triggers profile change → BLE reconnect
# =============================================================
mod_key = Box('Mod+N', Event, Profile)
bt_connect = Box('BT_connect', Profile, BLE)
led_update = Box('Profile_LED', Profile, LED)

profile_switch = mod_key >> (Box('copy', Profile, Profile @ Profile)
    >> (bt_connect @ led_update))
save(profile_switch, 'kb360-9-profile-switch', figsize=(12, 6))

# =============================================================
# 10. GF(3) trit-annotated recursive diagram
# Each box gets a trit; conservation must hold
#
# scan (+1, generate) → lookup (0, transport) → emit (-1, verify)
# Sum: +1 + 0 + (-1) = 0 ✓
# =============================================================
gen = Box('+1_scan', Key, Event)
transport = Box('0_layer', Event @ Layer, HID @ Layer)
verify = Box('-1_emit', HID, USB @ BLE)

triad = (gen @ Id(Layer)) >> transport >> (verify @ Id(Layer))
save(triad, 'kb360-10-gf3-triad', figsize=(14, 6))

print("\nAll diagrams saved to /Users/alice/worlds/figures/")
print("Open with: open /Users/alice/worlds/figures/kb360-*.png")
