---
name: ffmpeg
description: Media processing (10 man pages).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# ffmpeg

Media processing (10 man pages).

## Convert

```bash
ffmpeg -i input.mov -c:v libx264 output.mp4
ffmpeg -i input.mp4 -c:v libvpx-vp9 output.webm
```

## Audio

```bash
ffmpeg -i video.mp4 -vn -c:a aac audio.m4a
ffmpeg -i input.mp3 -ar 44100 output.wav
```

## Resize

```bash
ffmpeg -i input.mp4 -vf scale=1280:720 output.mp4
ffmpeg -i input.mp4 -vf scale=-1:480 output.mp4
```

## GIF

```bash
ffmpeg -i input.mp4 -vf "fps=10,scale=320:-1" output.gif
```

## Concat

```bash
ffmpeg -f concat -i list.txt -c copy output.mp4
```

## Capture

```bash
ffmpeg -f avfoundation -i "1" -t 10 capture.mp4
```

## Stream

```bash
ffmpeg -i input.mp4 -f mpegts - | mpv -
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
