#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = [
#     "google-genai>=1.16.0",
#     "opencv-python",
#     "numpy",
#     "rich",
# ]
# ///
"""
Gemini Tripartite Video Analysis
================================

Process video frame-by-frame with 3 interleaved inner monologue streams:
  - MINUS (-1): Constraints, errors, problems (purple, hue=270°)
  - ERGODIC (0): Balance, flow, composition (cyan, hue=180°)
  - PLUS (+1): Opportunities, improvements, creativity (orange, hue=30°)

Uses Gay-MCP SplitMix64 for deterministic stream interleaving.
GF(3) conservation: sum of trits ≡ 0 (mod 3)

Usage:
  uv run gemini_tripartite_video.py <video.mp4>
  
  # Or with explicit dependencies:
  uv run --with google-genai --with opencv-python --with numpy --with rich \\
      -- python gemini_tripartite_video.py <video.mp4>

Environment:
  GOOGLE_API_KEY: Your Gemini API key
"""

import os
import sys
import time
import json
from dataclasses import dataclass, field
from typing import Iterator, List, Dict, Any, Optional
from pathlib import Path

# ═══════════════════════════════════════════════════════════════════════════════
# SPLITMIX64 DETERMINISTIC RNG (Gay-MCP Compatible)
# ═══════════════════════════════════════════════════════════════════════════════


class SplitMix64:
    """Deterministic PRNG for reproducible stream interleaving"""

    GOLDEN = 0x9E3779B97F4A7C15
    MIX1 = 0xBF58476D1CE4E5B9
    MIX2 = 0x94D049BB133111EB
    MASK = (1 << 64) - 1

    def __init__(self, seed: int = 0x42D):
        self.state = seed & self.MASK
        self.initial_seed = seed

    def next(self) -> int:
        self.state = (self.state + self.GOLDEN) & self.MASK
        z = self.state
        z = ((z ^ (z >> 30)) * self.MIX1) & self.MASK
        z = ((z ^ (z >> 27)) * self.MIX2) & self.MASK
        return z ^ (z >> 31)

    def next_float(self) -> float:
        return self.next() / self.MASK

    def next_trit(self) -> int:
        """Generate trit in {-1, 0, +1}"""
        return (self.next() % 3) - 1

    def color_at(self, index: int) -> dict:
        """Generate OkLCH color at index"""
        # Reset and advance to index
        temp = SplitMix64(self.initial_seed)
        for _ in range(index):
            temp.next()

        L = 0.4 + 0.4 * temp.next_float()
        C = 0.1 + 0.2 * temp.next_float()
        H = temp.next_float() * 360
        trit = temp.next_trit()

        return {"L": L, "C": C, "H": H, "trit": trit, "css": f"oklch({L:.2f} {C:.3f} {H:.1f})"}


# ═══════════════════════════════════════════════════════════════════════════════
# TRIPARTITE STREAM DEFINITIONS
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class TripartiteStream:
    """One of three interleaved analysis streams"""

    name: str
    trit: int  # -1, 0, +1
    prompt_template: str
    color_hue: float
    symbol: str

    def to_css(self, L: float = 0.65, C: float = 0.18) -> str:
        return f"oklch({L} {C} {self.color_hue})"

    def format_prompt(self, context: str = "") -> str:
        return self.prompt_template.format(context=context) if context else self.prompt_template


STREAMS = {
    -1: TripartiteStream(
        name="MINUS",
        trit=-1,
        prompt_template="""You are the MINUS (-1) stream analyzing this frame.
Focus ONLY on:
- Constraints and limitations visible
- Errors, problems, inconsistencies  
- Missing elements or gaps
- Risks or concerns
- What could go wrong

Be critical and thorough. Output as JSON with keys: constraints, errors, risks, missing.
{context}""",
        color_hue=270,  # Purple
        symbol="⊖",
    ),
    0: TripartiteStream(
        name="ERGODIC",
        trit=0,
        prompt_template="""You are the ERGODIC (0) stream analyzing this frame.
Focus ONLY on:
- Overall balance and composition
- Flow and movement patterns
- Neutral observations (what IS, not what should be)
- Temporal continuity with previous frames
- State description without judgment

Be balanced and objective. Output as JSON with keys: balance, flow, state, continuity.
{context}""",
        color_hue=180,  # Cyan
        symbol="○",
    ),
    1: TripartiteStream(
        name="PLUS",
        trit=1,
        prompt_template="""You are the PLUS (+1) stream analyzing this frame.
Focus ONLY on:
- Opportunities and possibilities
- Creative improvements
- Positive observations
- Potential enhancements
- What could be added or amplified

Be generative and optimistic. Output as JSON with keys: opportunities, improvements, positives, enhancements.
{context}""",
        color_hue=30,  # Orange
        symbol="⊕",
    ),
}

# ═══════════════════════════════════════════════════════════════════════════════
# FRAME EXTRACTION
# ═══════════════════════════════════════════════════════════════════════════════


def extract_frames(video_path: str, fps: float = 1.0, max_frames: int = 30) -> List[tuple]:
    """Extract frames from video at specified FPS"""
    import cv2
    import numpy as np

    cap = cv2.VideoCapture(video_path)
    if not cap.isOpened():
        raise ValueError(f"Cannot open video: {video_path}")

    video_fps = cap.get(cv2.CAP_PROP_FPS)
    total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
    duration = total_frames / video_fps

    print(f"Video: {video_fps:.1f} FPS, {total_frames} frames, {duration:.1f}s duration")

    # Calculate frame indices to extract
    frame_interval = int(video_fps / fps)
    frames = []
    frame_idx = 0

    while len(frames) < max_frames:
        cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)
        ret, frame = cap.read()
        if not ret:
            break

        timestamp = frame_idx / video_fps
        frames.append((frame_idx, timestamp, frame))
        frame_idx += frame_interval

    cap.release()
    print(f"Extracted {len(frames)} frames")
    return frames


def frame_to_base64(frame) -> str:
    """Convert OpenCV frame to base64 JPEG"""
    import cv2
    import base64

    _, buffer = cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, 85])
    return base64.b64encode(buffer).decode("utf-8")


# ═══════════════════════════════════════════════════════════════════════════════
# GEMINI ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════════


@dataclass
class FrameAnalysis:
    """Analysis result for a single frame"""

    frame_idx: int
    timestamp: float
    stream: TripartiteStream
    response: str
    parsed: Optional[dict] = None


@dataclass
class TripartiteAnalysis:
    """Complete tripartite analysis of video"""

    video_path: str
    seed: int
    analyses: List[FrameAnalysis] = field(default_factory=list)

    def gf3_sum(self) -> int:
        """Compute GF(3) sum of all trits"""
        return sum(a.stream.trit for a in self.analyses) % 3

    def is_conserved(self) -> bool:
        return self.gf3_sum() == 0

    def by_stream(self) -> Dict[int, List[FrameAnalysis]]:
        result = {-1: [], 0: [], 1: []}
        for a in self.analyses:
            result[a.stream.trit].append(a)
        return result


def analyze_frame_with_gemini(
    client,
    frame_b64: str,
    stream: TripartiteStream,
    context: str = "",
    model: str = "gemini-2.5-flash",
) -> str:
    """Analyze a single frame with Gemini using specified stream"""
    from google.genai import types

    prompt = stream.format_prompt(context)

    response = client.models.generate_content(
        model=model,
        contents=[
            types.Content(
                parts=[
                    types.Part(inline_data=types.Blob(mime_type="image/jpeg", data=frame_b64)),
                    types.Part(text=prompt),
                ]
            )
        ],
    )

    return response.text


def analyze_video_tripartite(
    video_path: str,
    api_key: str = None,
    fps: float = 0.5,
    max_frames: int = 20,
    seed: int = 0x42D,
    model: str = "gemini-2.5-flash",
) -> TripartiteAnalysis:
    """
    Analyze video with tripartite interleaved streams.

    Each frame is assigned to MINUS, ERGODIC, or PLUS stream
    based on deterministic SplitMix64 RNG.
    """
    from google import genai
    from rich.console import Console
    from rich.progress import Progress, SpinnerColumn, TextColumn
    from rich.panel import Panel

    console = Console()

    # Initialize
    api_key = (
        api_key
        or os.environ.get("GOOGLE_API_KEY")
        or os.environ.get("GOOGLE_GENERATIVE_AI_API_KEY")
    )
    if not api_key:
        console.print("[red]Error: Set GOOGLE_API_KEY or GOOGLE_GENERATIVE_AI_API_KEY[/red]")
        sys.exit(1)

    client = genai.Client(api_key=api_key)
    rng = SplitMix64(seed)
    result = TripartiteAnalysis(video_path=video_path, seed=seed)

    # Extract frames
    console.print(Panel(f"[bold]Tripartite Video Analysis[/bold]\nSeed: 0x{seed:X}", title="🎬"))
    frames = extract_frames(video_path, fps=fps, max_frames=max_frames)

    # Analyze each frame with interleaved streams
    with Progress(
        SpinnerColumn(), TextColumn("[progress.description]{task.description}"), console=console
    ) as progress:
        task = progress.add_task("Analyzing...", total=len(frames))

        for i, (frame_idx, timestamp, frame) in enumerate(frames):
            # Determine stream via RNG
            trit = rng.next_trit()
            stream = STREAMS[trit]

            progress.update(
                task, description=f"{stream.symbol} Frame {i + 1}/{len(frames)} [{stream.name}]"
            )

            # Convert frame and analyze
            frame_b64 = frame_to_base64(frame)

            try:
                response = analyze_frame_with_gemini(
                    client,
                    frame_b64,
                    stream,
                    context=f"Frame {i + 1}, timestamp {timestamp:.1f}s",
                    model=model,
                )

                analysis = FrameAnalysis(
                    frame_idx=frame_idx, timestamp=timestamp, stream=stream, response=response
                )

                # Try to parse JSON
                try:
                    analysis.parsed = json.loads(response)
                except:
                    pass

                result.analyses.append(analysis)

            except Exception as e:
                console.print(f"[yellow]Warning: Frame {i} failed: {e}[/yellow]")

            progress.advance(task)

    # Summary
    by_stream = result.by_stream()
    console.print()
    console.print(
        Panel(
            f"[bold]Analysis Complete[/bold]\n\n"
            f"⊖ MINUS:   {len(by_stream[-1]):3d} frames (purple, hue=270°)\n"
            f"○ ERGODIC: {len(by_stream[0]):3d} frames (cyan, hue=180°)\n"
            f"⊕ PLUS:    {len(by_stream[1]):3d} frames (orange, hue=30°)\n\n"
            f"GF(3) Sum: {result.gf3_sum()} {'✓ CONSERVED' if result.is_conserved() else '○ OPEN'}",
            title="Summary",
        )
    )

    return result


# ═══════════════════════════════════════════════════════════════════════════════
# SYNTHESIS: COMBINE STREAMS
# ═══════════════════════════════════════════════════════════════════════════════


def synthesize_streams(analysis: TripartiteAnalysis) -> dict:
    """Synthesize insights from all three streams"""
    by_stream = analysis.by_stream()

    synthesis = {
        "constraints": [],  # From MINUS
        "balance": [],  # From ERGODIC
        "opportunities": [],  # From PLUS
    }

    for a in by_stream[-1]:  # MINUS
        if a.parsed:
            synthesis["constraints"].extend(a.parsed.get("constraints", []))
            synthesis["constraints"].extend(a.parsed.get("errors", []))

    for a in by_stream[0]:  # ERGODIC
        if a.parsed:
            synthesis["balance"].extend(a.parsed.get("balance", []))
            synthesis["balance"].extend(a.parsed.get("flow", []))

    for a in by_stream[1]:  # PLUS
        if a.parsed:
            synthesis["opportunities"].extend(a.parsed.get("opportunities", []))
            synthesis["opportunities"].extend(a.parsed.get("improvements", []))

    return synthesis


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════


def main():
    from rich.console import Console

    console = Console()

    if len(sys.argv) < 2:
        console.print("""
[bold]Gemini Tripartite Video Analysis[/bold]

Usage:
  python gemini_tripartite_video.py <video.mp4> [options]
  
  uv run gemini_tripartite_video.py <video.mp4>

Options:
  --fps <float>      Frames per second to analyze (default: 0.5)
  --max <int>        Maximum frames to analyze (default: 20)
  --seed <int>       Random seed for stream interleaving (default: 0x42D)
  --model <str>      Gemini model (default: gemini-2.5-flash)
  --output <path>    Save JSON output to file

Environment:
  GOOGLE_API_KEY     Your Gemini API key

Streams:
  ⊖ MINUS (-1)    Constraints, errors, problems (purple)
  ○ ERGODIC (0)   Balance, flow, composition (cyan)  
  ⊕ PLUS (+1)     Opportunities, improvements (orange)
        """)
        return

    video_path = sys.argv[1]

    # Parse args
    fps = 0.5
    max_frames = 20
    seed = 0x42D
    model = "gemini-2.5-flash"
    output = None

    args = sys.argv[2:]
    i = 0
    while i < len(args):
        if args[i] == "--fps" and i + 1 < len(args):
            fps = float(args[i + 1])
            i += 2
        elif args[i] == "--max" and i + 1 < len(args):
            max_frames = int(args[i + 1])
            i += 2
        elif args[i] == "--seed" and i + 1 < len(args):
            seed = int(args[i + 1], 0)
            i += 2
        elif args[i] == "--model" and i + 1 < len(args):
            model = args[i + 1]
            i += 2
        elif args[i] == "--output" and i + 1 < len(args):
            output = args[i + 1]
            i += 2
        else:
            i += 1

    # Run analysis
    result = analyze_video_tripartite(
        video_path, fps=fps, max_frames=max_frames, seed=seed, model=model
    )

    # Synthesize
    synthesis = synthesize_streams(result)

    # Output
    if output:
        export = {
            "video": video_path,
            "seed": seed,
            "model": model,
            "gf3_conserved": result.is_conserved(),
            "streams": {
                "minus": [
                    {"frame": a.frame_idx, "response": a.response} for a in result.by_stream()[-1]
                ],
                "ergodic": [
                    {"frame": a.frame_idx, "response": a.response} for a in result.by_stream()[0]
                ],
                "plus": [
                    {"frame": a.frame_idx, "response": a.response} for a in result.by_stream()[1]
                ],
            },
            "synthesis": synthesis,
        }
        with open(output, "w") as f:
            json.dump(export, f, indent=2)
        console.print(f"\n[green]Saved to {output}[/green]")

    # Print synthesis
    console.print("\n[bold]Synthesis[/bold]")
    for key, items in synthesis.items():
        if items:
            console.print(f"\n[cyan]{key.upper()}[/cyan]")
            for item in items[:5]:
                console.print(f"  • {item}")


if __name__ == "__main__":
    main()
