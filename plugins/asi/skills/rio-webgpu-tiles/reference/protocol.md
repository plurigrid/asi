# Rio Tile Protocol Reference

## OSC 1337 Tile Extension

### Format
```
ESC ] 1337 ; Tile = param:value,param:value,... BEL
```

Where `ESC` = `\033` and `BEL` = `\007`

### Parameters

| Parameter | Type | Required | Default | Description |
|-----------|------|----------|---------|-------------|
| `shader` | string | Yes | - | Shader identifier: `plasma`, `clock`, `noise`, or custom ID |
| `x` | f32 | Yes | - | X position in pixels from left |
| `y` | f32 | Yes | - | Y position in pixels from top |
| `w` | f32 | Yes | - | Width in pixels |
| `h` | f32 | Yes | - | Height in pixels |
| `id` | u64 | No | auto | Tile ID (0 = auto-assign) |
| `kind` | string | No | `persistent` | `persistent` or `transient` |
| `r` | f32 | No | 1.0 | Custom red channel (0.0-1.0) |
| `g` | f32 | No | 1.0 | Custom green channel (0.0-1.0) |
| `b` | f32 | No | 1.0 | Custom blue channel (0.0-1.0) |
| `a` | f32 | No | 1.0 | Custom alpha/data channel (0.0-1.0) |
| `time_offset` | f32 | No | 0.0 | Animation time offset in seconds |

### Commands

**Create/Update Tile:**
```bash
printf '\033]1337;Tile=shader:plasma,x:100,y:50,w:200,h:150\007'
```

**Remove Tile by ID:**
```bash
printf '\033]1337;Tile=remove:42\007'
```

**Clear All Tiles:**
```bash
printf '\033]1337;Tile=clear\007'
```

### Examples

```bash
# Basic plasma
printf '\033]1337;Tile=shader:plasma,x:0,y:0,w:300,h:200\007'

# Clock with custom color
printf '\033]1337;Tile=shader:clock,x:50,y:50,w:250,h:80,r:0.2,g:1.0,b:0.5\007'

# Persistent tile with explicit ID
printf '\033]1337;Tile=shader:noise,x:400,y:100,w:150,h:150,id:100,kind:persistent\007'

# Transient tile (must be re-sent each frame)
printf '\033]1337;Tile=shader:plasma,x:200,y:200,w:100,h:100,kind:transient\007'

# Remove specific tile
printf '\033]1337;Tile=remove:100\007'
```

## TileSpec Structure

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TileShader {
    Plasma,
    Clock,
    Noise,
    Custom(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TileKind {
    #[default]
    Persistent,
    Transient,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TileSpec {
    pub id: u64,              // 0 = auto-assign
    pub shader: TileShader,
    pub kind: TileKind,
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
    pub time_offset: f32,
    pub custom: [f32; 4],     // r, g, b, a
}
```

## Parser Implementation

Located at `rio-backend/src/ansi/tile_protocol.rs`:

```rust
pub fn parse(params: &[u8]) -> Option<TileSpec> {
    let s = std::str::from_utf8(params).ok()?;
    if !s.starts_with("Tile=") {
        return None;
    }
    
    let content = &s[5..];
    let mut spec = TileSpec::default();
    
    for pair in content.split(',') {
        let mut parts = pair.splitn(2, ':');
        let key = parts.next()?;
        let val = parts.next()?;
        
        match key {
            "shader" => spec.shader = parse_shader(val)?,
            "x" => spec.x = val.parse().ok()?,
            "y" => spec.y = val.parse().ok()?,
            "w" => spec.width = val.parse().ok()?,
            "h" => spec.height = val.parse().ok()?,
            "id" => spec.id = val.parse().ok()?,
            "kind" => spec.kind = parse_kind(val)?,
            "r" => spec.custom[0] = val.parse().ok()?,
            "g" => spec.custom[1] = val.parse().ok()?,
            "b" => spec.custom[2] = val.parse().ok()?,
            "a" => spec.custom[3] = val.parse().ok()?,
            "time_offset" => spec.time_offset = val.parse().ok()?,
            _ => {}
        }
    }
    
    Some(spec)
}
```

## Event Flow

```
Terminal Input (OSC 1337)
    ↓
rio-backend performer/handler.rs
    ↓ tile_protocol::parse()
TileSpec
    ↓ self.handler.insert_tile(spec)
RioEvent::InsertTile(TileSpec)
    ↓
rioterm application.rs event handler
    ↓ convert to TileScene
sugarloaf.create_persistent_tile(scene) or push_transient_tile(scene)
    ↓
TileWorldState updated
    ↓
TileBrush::render() draws all tiles
```
