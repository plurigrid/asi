---
name: media
description: Media processing = ffmpeg + imagemagick + sox.
metadata:
  trit: 1
geodesic: true
moebius: "μ(n) ≠ 0"
---

# media

Media processing = ffmpeg + imagemagick + sox.

## Atomic Skills

| Skill | Domain |
|-------|--------|
| ffmpeg | Video/audio |
| imagemagick | Images |
| sox | Audio |

## Video

```bash
# Convert
ffmpeg -i in.mov -c:v libx264 out.mp4

# Resize
ffmpeg -i in.mp4 -vf scale=1280:-1 out.mp4

# GIF
ffmpeg -i in.mp4 -vf "fps=10,scale=320:-1" out.gif
```

## Audio

```bash
# Extract
ffmpeg -i video.mp4 -vn -c:a aac audio.m4a

# Convert
sox in.wav -r 44100 out.wav
```

## Image

```bash
# Resize
convert in.png -resize 800x600 out.png

# Format
convert in.png out.jpg
```

## Pipeline

```bash
ffmpeg -i in.mp4 -f image2pipe - | convert - -resize 50% out.gif
```

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
