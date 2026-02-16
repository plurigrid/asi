---
name: ga-visualization
description: "Geometric Algebra visualization via ganja.js graph() - SVG/WebGL rendering of multivectors"
license: MIT
metadata:
  source: ganja.js + coffeeshop examples
  trit: +1
  gf3_conserved: true
  version: 1.0.0
---

# ga-visualization

> Render geometric algebra elements as interactive SVG/WebGL graphics

**Version**: 1.0.0  
**Trit**: +1 (PLUS - generative output)

## Overview

ganja.js provides a powerful `graph()` function that automatically renders:
- **1D functions** → Canvas line plots
- **2D functions** → Canvas heatmaps
- **PGA2D elements** → SVG points/lines
- **PGA3D elements** → WebGL 3D scenes
- **CGA elements** → Circles, spheres (OPNS/IPNS)

## The graph() Function

```javascript
// From ganja.js lines 781-1000
static graph(f, options) {
  // Detect mode from input
  if (typeof f === 'function' && f.length === 1) return graphCanvas1D(f);
  if (typeof f === 'function' && f.length === 2) return graphCanvas2D(f);
  if (Array.isArray(f) || f instanceof Function) return graphSVG(f);
  // ...
}
```

## Rendering Modes

### 1. 1D Functions

```javascript
Algebra(0).graph(x => Math.sin(x * 5));
// Renders sine wave on canvas
```

### 2. 2D Functions (Heatmaps)

```javascript
Algebra(0).graph((x, y) => x * x + y * y);
// Renders radial gradient
```

### 3. PGA2D Elements (SVG)

```javascript
Algebra(2,0,1, () => {
  var point = (x,y) => 1e12 - x*1e01 + y*1e02;
  var A = point(-1, 0), B = point(1, 0.5);
  
  return this.graph([
    0xFF0000,           // Color (red)
    A, "Point A",       // Point with label
    B, "Point B",
    A & B, "Line AB",   // Vee product = join
    [A, B],             // Line segment
  ], {grid: true});
});
```

### 4. PGA3D Elements (WebGL)

```javascript
Algebra(3,0,1, () => {
  var point = (x,y,z) => 1e123 - x*1e023 + y*1e013 - z*1e012;
  var origin = 1e123;
  
  return this.graph([
    0x00FF00, origin, "Origin",
    0xFF0000, point(1, 0, 0), "X",
    0x0000FF, point(0, 1, 0), "Y",
  ], {gl: true, camera: 1 + 0.5*1e01});
});
```

### 5. CGA (Conformal) Elements

```javascript
Algebra(4,1, () => {
  // Conformal embedding
  var ni = 1e4 + 1e5, no = 0.5*(1e5 - 1e4);
  var point = (x,y,z) => no + x*1e1 + y*1e2 + z*1e3 + 0.5*(x*x+y*y+z*z)*ni;
  
  // Circle through 3 points
  var A = point(0,0,0), B = point(1,0,0), C = point(0,1,0);
  var circle = A ^ B ^ C;
  
  return this.graph([circle], {conformal: true, gl: true});
});
```

## Interactive Features

### Draggable Points

Points in 2D PGA can be made draggable:

```javascript
this.graph([
  A, B, C,  // Users can drag these
  () => A & B,  // Dynamic line updates when points move
], {animate: true});
```

### Animation

Lambda expressions are re-evaluated each frame:

```javascript
this.graph([
  () => {
    var t = Date.now() * 0.001;
    return rotor(t, 1e12) >>> point(1, 0);
  }
], {animate: true});
```

## Graph Options

| Option | Type | Description |
|--------|------|-------------|
| `grid` | bool | Show coordinate grid |
| `animate` | bool | Re-render each frame |
| `gl` | bool | Force WebGL mode |
| `conformal` | bool | CGA rendering mode |
| `camera` | motor | Initial camera position |
| `width` | number | Canvas width |
| `height` | number | Canvas height |
| `lineWidth` | number | Line thickness |
| `pointRadius` | number | Point size |
| `alpha` | bool | Enable transparency |

## Color Encoding for GF(3)

Map trits to colors for visual debugging:

```javascript
const tritColors = {
  '-1': 0xFF5555,  // MINUS: Red
  '0':  0x55FF55,  // ERGODIC: Green  
  '+1': 0x5555FF   // PLUS: Blue
};

function colorByTrit(element) {
  var trit = computeTrit(element);
  return tritColors[trit];
}

this.graph([
  colorByTrit(A), A,
  colorByTrit(B), B,
  colorByTrit(A & B), A & B,
]);
```

## SVG Element Types

From the wedge game CSS:

| Class | Element | Style |
|-------|---------|-------|
| `.pointBase` | Point circle | `fill: #fff` |
| `.pointSel` | Selection highlight | `r: 0.2, stroke: #8F8` |
| `.lineBase` | Line | `stroke: white` |
| `.lineSel` | Line selection | `stroke-width: 0.3` |

## WebGL Rendering Pipeline

```
Elements → Project to 3D → Build mesh → Vertex shader → Fragment shader → Canvas
```

### Sphere Tracing (OPNS)

For implicit surfaces defined by null vectors:

```javascript
// From ganja.js graphGL2() 
// Sphere traces the distance function defined by the algebra
```

## Integration with Gay.jl Coloring

```julia
using Gay

function visualize_with_colors(elements, seed=1069)
    Gay.seed!(seed)
    colors = [Gay.color_at(i) for i in 1:length(elements)]
    
    # Export to ganja.js format
    js_array = map(zip(colors, elements)) do (c, e)
        "0x$(c[2:end]), $(element_to_js(e))"
    end
    
    return "this.graph([$(join(js_array, ", "))])"
end
```

## GF(3) Triads

```
ga-visualization (+1) ⊗ ganja-wedge-game (+1) ⊗ three-match (-1) → need -1
→ Add: sheaf-cohomology (-1) ⊗ ga-visualization (+1) ⊗ gay-mcp (+1) → need -1
```

## Commands

```bash
# Start coffeeshop examples server
npx serve node_modules/ganja.js/examples

# Open specific example
open https://enkimute.github.io/ganja.js/examples/coffeeshop.html#pga3d_icosahedron

# Generate SVG from CLI
node -e "var A=require('ganja.js'); console.log(A(2,0,1,function(){
  return this.graph([1e12, 1e1, 1e2]).outerHTML;
})())"
```

## Files

- **Renderer**: `lib/ga_renderer.js`
- **Color mapping**: `lib/gf3_colors.js`
- **Examples**: `examples/visualization_gallery.html`

## References

- [ganja.js coffeeshop](https://enkimute.github.io/ganja.js/examples/coffeeshop.html)
- [ganja.js graph() source](https://github.com/enkimute/ganja.js/blob/master/ganja.js#L781)
- [bivector.net tutorials](https://bivector.net/)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
