---
name: media
description: Media processing = ffmpeg + imagemagick + sox.
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
