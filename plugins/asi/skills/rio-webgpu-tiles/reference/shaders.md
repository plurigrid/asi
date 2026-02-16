# Rio WebGPU Tile Shaders

Complete WGSL shader implementations for Rio Terminal GPU tiles.

## Plasma Shader

```wgsl
// tile_plasma.wgsl - Animated plasma effect
struct Uniforms {
    position: vec2<f32>,
    size: vec2<f32>,
    time: f32,
    custom: vec4<f32>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) time: f32,
    @location(2) custom: vec4<f32>,
}

@vertex
fn vs_main(@location(0) pos: vec2<f32>, @location(1) uv: vec2<f32>) -> VertexOutput {
    var out: VertexOutput;
    let screen_pos = u.position + pos * u.size;
    out.position = vec4<f32>(screen_pos, 0.0, 1.0);
    out.uv = uv;
    out.time = u.time;
    out.custom = u.custom;
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    let t = in.time;
    let p = in.uv * 10.0;
    
    // Classic plasma formula
    let v1 = sin(p.x + t);
    let v2 = sin(p.y + t * 0.7);
    let v3 = sin(p.x + p.y + t * 1.3);
    let v4 = sin(sqrt(p.x * p.x + p.y * p.y) + t);
    let v = v1 + v2 + v3 + v4;
    
    // RGB color cycling with custom tint
    let base = 0.5 + 0.5 * sin(vec3<f32>(v, v + 2.094, v + 4.188));
    let tinted = base * (0.5 + 0.5 * in.custom.rgb);
    
    return vec4<f32>(tinted, 1.0);
}
```

## Clock Shader

```wgsl
// tile_clock.wgsl - 7-segment digital clock display
struct Uniforms {
    position: vec2<f32>,
    size: vec2<f32>,
    time: f32,
    custom: vec4<f32>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) time: f32,
    @location(2) custom: vec4<f32>,
}

// 7-segment encoding: bits = gfedcba (standard segment naming)
fn digit_segments(d: i32) -> i32 {
    switch d {
        case 0: { return 0x3F; } // 0111111
        case 1: { return 0x06; } // 0000110
        case 2: { return 0x5B; } // 1011011
        case 3: { return 0x4F; } // 1001111
        case 4: { return 0x66; } // 1100110
        case 5: { return 0x6D; } // 1101101
        case 6: { return 0x7D; } // 1111101
        case 7: { return 0x07; } // 0000111
        case 8: { return 0x7F; } // 1111111
        case 9: { return 0x6F; } // 1101111
        default: { return 0x00; }
    }
}

fn draw_segment(uv: vec2<f32>, seg: i32, thickness: f32) -> f32 {
    var p = uv;
    var d: f32 = 1000.0;
    
    // Segment positions (a=top, b=top-right, c=bot-right, d=bot, e=bot-left, f=top-left, g=middle)
    if ((seg & 0x01) != 0) { // a - top horizontal
        d = min(d, abs(p.y - 0.9) + max(abs(p.x - 0.5) - 0.3, 0.0));
    }
    if ((seg & 0x02) != 0) { // b - top-right vertical
        d = min(d, abs(p.x - 0.8) + max(abs(p.y - 0.7) - 0.15, 0.0));
    }
    if ((seg & 0x04) != 0) { // c - bot-right vertical
        d = min(d, abs(p.x - 0.8) + max(abs(p.y - 0.3) - 0.15, 0.0));
    }
    if ((seg & 0x08) != 0) { // d - bottom horizontal
        d = min(d, abs(p.y - 0.1) + max(abs(p.x - 0.5) - 0.3, 0.0));
    }
    if ((seg & 0x10) != 0) { // e - bot-left vertical
        d = min(d, abs(p.x - 0.2) + max(abs(p.y - 0.3) - 0.15, 0.0));
    }
    if ((seg & 0x20) != 0) { // f - top-left vertical
        d = min(d, abs(p.x - 0.2) + max(abs(p.y - 0.7) - 0.15, 0.0));
    }
    if ((seg & 0x40) != 0) { // g - middle horizontal
        d = min(d, abs(p.y - 0.5) + max(abs(p.x - 0.5) - 0.3, 0.0));
    }
    
    return smoothstep(thickness + 0.02, thickness, d);
}

@vertex
fn vs_main(@location(0) pos: vec2<f32>, @location(1) uv: vec2<f32>) -> VertexOutput {
    var out: VertexOutput;
    let screen_pos = u.position + pos * u.size;
    out.position = vec4<f32>(screen_pos, 0.0, 1.0);
    out.uv = uv;
    out.time = u.time;
    out.custom = u.custom;
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    var uv = in.uv;
    uv.y = 1.0 - uv.y; // Flip Y
    
    let total_seconds = i32(in.time);
    let hours = (total_seconds / 3600) % 24;
    let minutes = (total_seconds / 60) % 60;
    let seconds = total_seconds % 60;
    
    // Layout: HH:MM:SS (8 digit slots plus 2 colons)
    let digit_width = 1.0 / 8.5;
    let slot = i32(uv.x / digit_width);
    let local_x = (uv.x - f32(slot) * digit_width) / digit_width;
    let local_uv = vec2<f32>(local_x, uv.y);
    
    var color: f32 = 0.0;
    let thickness = 0.05;
    
    switch slot {
        case 0: { color = draw_segment(local_uv, digit_segments(hours / 10), thickness); }
        case 1: { color = draw_segment(local_uv, digit_segments(hours % 10), thickness); }
        case 2: { // colon
            let cy = abs(uv.y - 0.35) < 0.05 || abs(uv.y - 0.65) < 0.05;
            color = select(0.0, 1.0, cy && abs(local_x - 0.5) < 0.15);
        }
        case 3: { color = draw_segment(local_uv, digit_segments(minutes / 10), thickness); }
        case 4: { color = draw_segment(local_uv, digit_segments(minutes % 10), thickness); }
        case 5: { // colon
            let cy = abs(uv.y - 0.35) < 0.05 || abs(uv.y - 0.65) < 0.05;
            color = select(0.0, 1.0, cy && abs(local_x - 0.5) < 0.15);
        }
        case 6: { color = draw_segment(local_uv, digit_segments(seconds / 10), thickness); }
        case 7: { color = draw_segment(local_uv, digit_segments(seconds % 10), thickness); }
        default: {}
    }
    
    // Apply custom color tint
    let tint = vec3<f32>(
        0.2 + in.custom.x * 0.8,
        0.8 + in.custom.y * 0.2,
        0.3 + in.custom.z * 0.7
    );
    
    let fg = color * tint;
    let bg = vec3<f32>(0.05, 0.05, 0.1);
    
    return vec4<f32>(mix(bg, fg, color), 1.0);
}
```

## Noise Shader

```wgsl
// tile_noise.wgsl - Animated Perlin-like noise
struct Uniforms {
    position: vec2<f32>,
    size: vec2<f32>,
    time: f32,
    custom: vec4<f32>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    @location(0) uv: vec2<f32>,
    @location(1) time: f32,
    @location(2) custom: vec4<f32>,
}

fn hash(p: vec2<f32>) -> f32 {
    let h = dot(p, vec2<f32>(127.1, 311.7));
    return fract(sin(h) * 43758.5453123);
}

fn noise(p: vec2<f32>) -> f32 {
    let i = floor(p);
    let f = fract(p);
    let u = f * f * (3.0 - 2.0 * f);
    
    let a = hash(i);
    let b = hash(i + vec2<f32>(1.0, 0.0));
    let c = hash(i + vec2<f32>(0.0, 1.0));
    let d = hash(i + vec2<f32>(1.0, 1.0));
    
    return mix(mix(a, b, u.x), mix(c, d, u.x), u.y);
}

fn fbm(p: vec2<f32>) -> f32 {
    var v = 0.0;
    var a = 0.5;
    var pp = p;
    for (var i = 0; i < 5; i++) {
        v += a * noise(pp);
        pp *= 2.0;
        a *= 0.5;
    }
    return v;
}

@vertex
fn vs_main(@location(0) pos: vec2<f32>, @location(1) uv: vec2<f32>) -> VertexOutput {
    var out: VertexOutput;
    let screen_pos = u.position + pos * u.size;
    out.position = vec4<f32>(screen_pos, 0.0, 1.0);
    out.uv = uv;
    out.time = u.time;
    out.custom = u.custom;
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    let scale = 4.0 + in.custom.w * 8.0;
    let speed = 0.5 + in.custom.z;
    let p = in.uv * scale + vec2<f32>(in.time * speed, in.time * speed * 0.7);
    
    let n = fbm(p);
    let color = mix(in.custom.rgb * 0.2, in.custom.rgb, n);
    
    return vec4<f32>(color, 1.0);
}
```

## Shader Development Tips

1. **Time precision**: Use `f32` modular time (wraps every ~1000s) for GPU, `f64` on CPU
2. **UV coordinates**: Origin is bottom-left (0,0), top-right is (1,1); flip Y if needed
3. **Custom data**: Use `custom.rgba` for user-configurable parameters
4. **Performance**: Minimize branches, use built-in functions, prefer ALU over memory
5. **Debugging**: Output UV as color to verify coordinate space
