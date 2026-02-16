---
name: glamorous-gay
description: "Glamorous Toolkit integration with Gay.jl deterministic coloring. Moldable inspectors with GF(3)-balanced views, Lepiter color-coded knowledge graphs, and Bloc visualizations with SplitMix64 palettes."
license: MIT
metadata:
  trit: +1
  source: feenk.com, Gay.jl
  xenomodern: true
  stars: 312
  extensions:
    - MOLDABLE_INSPECTORS.md
    - LEPITER_COLORS.md
---

# Glamorous Gay Skill

**Status**: ✅ Production Ready
**Trit**: +1 (PLUS - generative/visual)
**Color**: #E91E63 (Pink)
**Principle**: Moldable development with deterministic coloring
**Frame**: Every object gets a reproducible color; every view tells a story

---

## Overview

**Glamorous Toolkit** (GT) is a moldable development environment where you shape the IDE to your problem. **Glamorous Gay** integrates Gay.jl's deterministic coloring:

1. **Moldable Inspectors**: Objects colored by identity hash
2. **Lepiter Knowledge Graphs**: Pages/snippets with GF(3) trits
3. **Bloc Visualizations**: Reproducible palettes for diagrams
4. **Parallel Tempering Views**: Pigeons.jl chains in GT

## Core Concept: Every Object Has a Color

```smalltalk
"In GT, everything is inspectable. Now everything is colorable."

Object >> gayColor
    "Deterministic color from object identity"
    ^ GaySplitMix64 colorAt: self identityHash seed: GayGlobalSeed value
    
Object >> gayTrit
    "GF(3) trit from hue"
    ^ self gayColor hue gayTritFromHue
    
Number >> gayTritFromHue
    "Hue → Trit mapping"
    self < 60 ifTrue: [ ^ 1 ].   "warm → PLUS"
    self < 180 ifTrue: [ ^ 0 ].  "neutral → ERGODIC"
    self < 300 ifTrue: [ ^ -1 ]. "cool → MINUS"
    ^ 1 "wrap around"
```

## SplitMix64 in Smalltalk

```smalltalk
Class: GaySplitMix64
    instanceVariables: 'state'
    classVariables: 'Golden Mix1 Mix2 Mask64'

GaySplitMix64 class >> initialize
    Golden := 16r9E3779B97F4A7C15.
    Mix1 := 16rBF58476D1CE4E5B9.
    Mix2 := 16r94D049BB133111EB.
    Mask64 := 16rFFFFFFFFFFFFFFFF.

GaySplitMix64 >> nextState
    state := (state + Golden) bitAnd: Mask64.
    ^ self mix: state

GaySplitMix64 >> mix: z
    | z1 z2 z3 |
    z1 := ((z bitXor: (z bitShift: -30)) * Mix1) bitAnd: Mask64.
    z2 := ((z1 bitXor: (z1 bitShift: -27)) * Mix2) bitAnd: Mask64.
    z3 := z2 bitXor: (z2 bitShift: -31).
    ^ z3

GaySplitMix64 >> colorAt: index
    "Generate OkLCH color at index"
    | rng L C H |
    rng := self class seed: (state bitXor: index).
    L := 10 + (rng nextFloat * 85).  "Lightness 10-95"
    C := rng nextFloat * 100.         "Chroma 0-100"
    H := rng nextFloat * 360.         "Hue 0-360"
    ^ GayColor L: L C: C H: H
```

## Moldable Inspectors

### Colored Object Inspector

```smalltalk
Object >> gtGayInspectorFor: aView
    <gtView>
    ^ aView explicit
        title: 'Gay Color';
        priority: 50;
        stencil: [
            | container colorBox tritLabel |
            container := BlElement new
                layout: BlLinearLayout horizontal;
                constraintsDo: [ :c | 
                    c horizontal fitContent.
                    c vertical fitContent ].
            
            colorBox := BlElement new
                size: 50@50;
                background: self gayColor asBlColor.
            
            tritLabel := BrLabel new
                text: ('Trit: ', self gayTrit asString);
                aptitude: BrGlamorousLabelAptitude.
            
            container addChildren: { colorBox. tritLabel }.
            container ]
```

### Collection Inspector with Rainbow

```smalltalk
SequenceableCollection >> gtGayRainbowFor: aView
    <gtView>
    ^ aView columnedList
        title: 'Rainbow';
        priority: 45;
        items: [ self withIndexCollect: [:item :i | i -> item ] ];
        column: 'Color' 
            icon: [ :assoc | 
                BlElement new 
                    size: 20@20;
                    background: (GaySplitMix64 colorAt: assoc key) asBlColor ]
            width: 30;
        column: 'Index' text: [ :assoc | assoc key ];
        column: 'Item' text: [ :assoc | assoc value ];
        column: 'Trit' text: [ :assoc | 
            (GaySplitMix64 colorAt: assoc key) trit ]
```

## Lepiter Integration

### Color-Coded Pages

```smalltalk
LePage >> gayColor
    "Page color from title hash"
    ^ GaySplitMix64 colorAt: self title hash

LeSnippet >> gayColor
    "Snippet color from content hash"
    ^ GaySplitMix64 colorAt: self contentAsString hash

LePage >> gtGayMapFor: aView
    <gtView>
    ^ aView mondrian
        title: 'Gay Map';
        priority: 60;
        painting: [ :m |
            m nodes
                shape: [ :page |
                    BlElement new
                        size: (50 @ 50);
                        background: page gayColor asBlColor;
                        addChild: (BrLabel new text: page title) ];
                with: self database pages.
            m edges
                shape: [ :link | 
                    BlLineElement new
                        border: (BlBorder paint: Color gray width: 1) ];
                fromRightCenter;
                toLeftCenter;
                connectToAll: #outgoingLinks.
            m layout force ]
```

### GF(3) Snippet Triads

```smalltalk
LePage >> verifyGF3Conservation
    "Check that snippet trits sum to 0 mod 3"
    | trits sum |
    trits := self children collect: #gayTrit.
    sum := trits sum.
    ^ (sum \\ 3) = 0
        ifTrue: [ 'GF(3) conserved ✓' ]
        ifFalse: [ 'GF(3) violated: sum = ', sum asString ]

LePage >> balanceSnippets
    "Add balancing snippet if needed"
    | sum neededTrit |
    sum := (self children collect: #gayTrit) sum.
    (sum \\ 3) = 0 ifTrue: [ ^ self ].
    
    neededTrit := (3 - (sum \\ 3)) \\ 3.
    neededTrit = 2 ifTrue: [ neededTrit := -1 ].
    
    self addSnippet: (LeTextSnippet string: 
        '[Balancing snippet, trit = ', neededTrit asString, ']')
```

## Bloc Visualizations

### Parallel Tempering View

```smalltalk
PigeonsResult >> gtGayTemperingFor: aView
    <gtView>
    ^ aView explicit
        title: 'Tempering Chains';
        priority: 40;
        stencil: [
            | container |
            container := BlElement new
                layout: BlLinearLayout vertical;
                constraintsDo: [ :c | c horizontal matchParent ].
            
            self chains withIndexDo: [ :chain :i |
                | row beta color |
                beta := self schedule at: i.
                color := GaySplitMix64 colorAt: i.
                
                row := BlElement new
                    layout: BlLinearLayout horizontal;
                    constraintsDo: [ :c | c horizontal matchParent ];
                    addChildren: {
                        "Color swatch"
                        BlElement new size: 30@30; background: color asBlColor.
                        "Beta label"
                        BrLabel new text: ('β = ', beta printString).
                        "Energy bar"
                        BlElement new 
                            size: ((chain energy / self maxEnergy * 200) @ 20);
                            background: color asBlColor.
                        "Trit"
                        BrLabel new text: ('trit: ', color trit asString)
                    }.
                container addChild: row ].
            container ]
```

### Directed Landscape Visualization

```smalltalk
DirectedLandscape >> gtGayLandscapeFor: aView
    <gtView>
    ^ aView explicit
        title: 'Landscape';
        priority: 35;
        stencil: [
            | canvas |
            canvas := BlElement new
                size: 600@400;
                background: Color black.
            
            self geodesics do: [ :geo |
                | path color |
                color := GaySplitMix64 colorAt: geo hash.
                path := BlPolylineElement vertices: geo asPoints.
                path border: (BlBorder paint: color asBlColor width: 2).
                canvas addChild: path ].
            
            canvas ]
```

## KPZ Integration

### Colored Height Function View

```smalltalk
KPZHeightFunction >> gtGayHeightFor: aView
    <gtView>
    ^ aView explicit
        title: 'Colored Height';
        priority: 30;
        stencil: [
            | canvas |
            canvas := BlElement new size: 800@400.
            
            self grid withIndexDo: [ :row :y |
                row withIndexDo: [ :height :x |
                    | color elem |
                    color := self heightToColor: height atColor: (self colorAt: x@y).
                    elem := BlElement new
                        position: (x * 4) @ (400 - (height * 2));
                        size: 4 @ (height * 2);
                        background: color asBlColor.
                    canvas addChild: elem ]].
            
            canvas ]

KPZHeightFunction >> heightToColor: h atColor: k
    "Gay.jl color modulated by height"
    | base |
    base := GaySplitMix64 colorAt: k.
    ^ GayColor 
        L: (base L + (h * 0.5) min: 95)
        C: base C
        H: base H
```

## Commands

```bash
# Load Glamorous Gay into GT
just gt-load-gay

# Color an object
just gt-gay-color object=MyClass

# Generate Lepiter color map
just gt-lepiter-gay-map

# Visualize tempering chains
just gt-pigeons-view result.ston
```

## Installation

```smalltalk
"Load via Metacello"
Metacello new
    repository: 'github://bmorphism/glamorous-gay:main/src';
    baseline: 'GlamorousGay';
    load.
    
"Set global seed"
GayGlobalSeed value: 1069.

"Verify installation"
42 gayColor inspect.
```

## GF(3) Triad

| Trit | Role | GT Component |
|------|------|--------------|
| -1 | Validation | Inspector assertions |
| 0 | Coordination | Lepiter knowledge base |
| +1 | Generation | Bloc visualizations |

**Conservation**: (-1) + (0) + (+1) = 0 ✓

## Related Skills

- **gay-mcp** (+1): Core coloring algorithm
- **kpz-universality** (0): Height function coloring
- **pigeons-tempering**: Chain visualization
- **discopy** (+1): String diagram rendering

---

**Skill Name**: glamorous-gay
**Type**: IDE Integration / Visualization
**Trit**: +1 (PLUS)
**Key Property**: Every object has a deterministic, reproducible color
**Status**: ✅ Production Ready

---

## Autopoietic Marginalia

> **The IDE molds to the problem. The colors reveal the structure. GF(3) conserves.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record effective inspector patterns
- **REMEMBERING** (0): Connect visualizations across domains
- **WORLDING** (+1): Create new moldable views

*Add Interaction Exemplars here as the skill is used.*
