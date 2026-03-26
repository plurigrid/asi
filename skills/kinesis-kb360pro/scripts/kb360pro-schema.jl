# KB360 Pro as ACSet Schema
# Skill: acsets (Catlab.jl)
#
# The keyboard topology is a C-set functor X: Sch(KB360) → Set
# Objects model hardware modules; morphisms model data/power paths

using Catlab.CategoricalAlgebra

@present SchKB360(FreeSchema) begin
    # Objects (hardware components)
    LeftMod::Ob       # Primary module — talks to host
    RightMod::Ob      # Secondary — wireless link to left only
    Host::Ob          # Computer (USB or BT target)
    Layer::Ob         # Keymap layer {Base=0, kp=1, fn=2, Mod=3}
    Profile::Ob       # BT profile {1..5}
    Battery::Ob       # 1500 mAh Li-ion per module

    # Morphisms (data/power paths)
    wireless::Hom(RightMod, LeftMod)       # R→L always active
    usb_data::Hom(LeftMod, Host)           # L→Host via USB-C
    bt_link::Hom(LeftMod, Host)            # L→Host via Bluetooth
    active_layer::Hom(LeftMod, Layer)      # current keymap layer
    active_profile::Hom(LeftMod, Profile)  # current BT profile
    left_bat::Hom(Battery, LeftMod)        # battery powers left
    right_bat::Hom(Battery, RightMod)      # battery powers right

    # Attributes
    ProfileID::AttrType
    LayerID::AttrType
    Charge::AttrType
    LEDColor::AttrType

    profile_id::Attr(Profile, ProfileID)   # 1..5
    layer_id::Attr(Layer, LayerID)         # 0..3
    charge_mah::Attr(Battery, Charge)      # 0..1500
    led_color::Attr(Profile, LEDColor)     # white/blue/red/green/off
end

@acset_type KB360(SchKB360, index=[:wireless, :usb_data, :bt_link, :active_layer, :active_profile])

# Instantiate the physical keyboard
function make_kb360()
    kb = KB360{Int, Int, Float64, Symbol}()

    # Parts
    left  = add_part!(kb, :LeftMod)
    right = add_part!(kb, :RightMod)
    host  = add_part!(kb, :Host)

    # 4 layers
    layers = add_parts!(kb, :Layer, 4, layer_id=[0, 1, 2, 3])

    # 5 BT profiles
    profiles = add_parts!(kb, :Profile, 5,
        profile_id=[1, 2, 3, 4, 5],
        led_color=[:white, :blue, :red, :green, :off])

    # 2 batteries
    bats = add_parts!(kb, :Battery, 2, charge_mah=[1500.0, 1500.0])

    # Morphisms
    set_subpart!(kb, right, :wireless, left)
    set_subpart!(kb, left, :usb_data, host)
    set_subpart!(kb, left, :bt_link, host)
    set_subpart!(kb, left, :active_layer, layers[1])   # Base layer
    set_subpart!(kb, left, :active_profile, profiles[5]) # Wired = P5
    set_subpart!(kb, bats[1], :left_bat, left)
    set_subpart!(kb, bats[2], :right_bat, right)

    return kb
end

# Layer switching as natural transformation
# α: active_layer → new_layer (preserves schema structure)
function switch_layer!(kb::KB360, left_id, new_layer_id)
    set_subpart!(kb, left_id, :active_layer, new_layer_id)
end

# Profile switching
function switch_profile!(kb::KB360, left_id, new_profile_id)
    set_subpart!(kb, left_id, :active_profile, new_profile_id)
end

# Battery query (Mod+O equivalent)
function battery_status(kb::KB360)
    [(i, subpart(kb, i, :charge_mah)) for i in parts(kb, :Battery)]
end
