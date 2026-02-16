#!/usr/bin/env python3
"""
Triadic Video Analyzer with GF(3) Conservation
Analyzes videos from chaotic_media_lake.duckdb using parallel trit streams
"""
import duckdb
import subprocess
import json
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
import sys

GOLDEN = 0x9e3779b97f4a7c15
MASK64 = 0xFFFFFFFFFFFFFFFF

@dataclass
class VideoEntry:
    chaotic_id: str
    original_path: str
    filename: str
    color_hex: str
    trit: int
    gay_seed: int

def splitmix64(seed: int) -> tuple[int, int]:
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64

def color_at(seed: int, index: int) -> str:
    """O(1) random access to color sequence - SPI guaranteed"""
    state = (seed + (index + 1) * GOLDEN) & MASK64
    _, mixed = splitmix64(state - GOLDEN)
    hue = mixed % 360
    return f"hsl({hue}, 70%, 50%)"

def get_video_duration(path: str) -> Optional[float]:
    """Get video duration using macOS mdls (no ffprobe needed)"""
    try:
        result = subprocess.run([
            'mdls', '-name', 'kMDItemDurationSeconds', '-raw', path
        ], capture_output=True, text=True)
        if result.stdout and result.stdout.strip() != '(null)':
            return float(result.stdout.strip())
    except:
        pass
    return None

def get_video_metadata(path: str) -> dict:
    """Get full video metadata using macOS mdls"""
    try:
        result = subprocess.run([
            'mdls', '-name', 'kMDItemDurationSeconds',
            '-name', 'kMDItemPixelWidth', '-name', 'kMDItemPixelHeight',
            '-name', 'kMDItemCodecs', path
        ], capture_output=True, text=True)
        
        meta = {}
        for line in result.stdout.split('\n'):
            if '=' in line:
                key, val = line.split('=', 1)
                key = key.strip()
                val = val.strip().strip('()"')
                if key == 'kMDItemDurationSeconds' and val != 'null':
                    meta['duration'] = float(val)
                elif key == 'kMDItemPixelWidth' and val != 'null':
                    meta['width'] = int(val)
                elif key == 'kMDItemPixelHeight' and val != 'null':
                    meta['height'] = int(val)
                elif key == 'kMDItemCodecs':
                    meta['codec'] = val.replace('\n', '').strip()
        return meta
    except:
        return {}

def extract_keyframes(path: str, seed: int, n_frames: int = 5) -> list[str]:
    """Extract keyframe timestamps using deterministic positions"""
    duration = get_video_duration(path)
    if not duration:
        return []
    
    timestamps = []
    for i in range(n_frames):
        _, rand = splitmix64(seed + i * GOLDEN)
        t = (rand % int(duration * 1000)) / 1000.0
        timestamps.append(f"{t:.2f}s")
    return timestamps

def analyze_motion(path: str) -> float:
    """Estimate motion score using ffmpeg scene detection"""
    try:
        result = subprocess.run([
            'ffprobe', '-v', 'quiet', '-select_streams', 'v',
            '-show_entries', 'stream=avg_frame_rate',
            '-of', 'json', path
        ], capture_output=True, text=True)
        data = json.loads(result.stdout)
        fps_str = data['streams'][0]['avg_frame_rate']
        num, den = map(int, fps_str.split('/'))
        fps = num / den if den else 30
        # Higher FPS screen recordings tend to have more motion
        return min(1.0, fps / 60.0)
    except:
        return 0.5

def load_videos(db_path: str, trit_filter: Optional[int] = None) -> list[VideoEntry]:
    """Load video entries from chaotic_media_lake"""
    con = duckdb.connect(db_path, read_only=True)
    
    query = """
        SELECT chaotic_id, original_path, filename, color_hex, trit, gay_seed
        FROM chaotic_files
        WHERE extension IN ('.mov', '.mp4', '.MOV')
    """
    if trit_filter is not None:
        query += f" AND trit = {trit_filter}"
    query += " ORDER BY shuffle_key"
    
    videos = []
    for row in con.execute(query).fetchall():
        videos.append(VideoEntry(*row))
    con.close()
    return videos

def verify_gf3(db_path: str) -> tuple[bool, int]:
    """Verify GF(3) conservation"""
    con = duckdb.connect(db_path, read_only=True)
    result = con.execute("SELECT SUM(trit) FROM chaotic_files WHERE extension IN ('.mov', '.mp4', '.MOV')").fetchone()
    con.close()
    gf3_sum = result[0] or 0
    return gf3_sum == 0, gf3_sum

def triadic_summary(db_path: str):
    """Print triadic distribution summary"""
    con = duckdb.connect(db_path, read_only=True)
    
    print("\n╔════════════════════════════════════════════════════╗")
    print("║     TRIADIC VIDEO ANALYSIS - GF(3) CONSERVED       ║")
    print("╠════════════════════════════════════════════════════╣")
    
    for trit in [-1, 0, 1]:
        role = {-1: "VALIDATOR", 0: "ERGODIC", 1: "GENERATOR"}[trit]
        result = con.execute(f"""
            SELECT COUNT(*), 
                   STRING_AGG(color_hex, ', ' ORDER BY shuffle_key) as colors
            FROM chaotic_files 
            WHERE extension IN ('.mov', '.mp4', '.MOV') AND trit = {trit}
        """).fetchone()
        count = result[0]
        colors = result[1][:50] + "..." if result[1] and len(result[1]) > 50 else result[1]
        
        trit_symbol = {-1: "⊖", 0: "⊙", 1: "⊕"}[trit]
        print(f"║ {trit_symbol} Trit {trit:+d} ({role:9s}): {count:2d} videos              ║")
    
    # GF(3) check
    conserved, gf3_sum = verify_gf3(db_path)
    status = "✓ CONSERVED" if conserved else f"✗ VIOLATION ({gf3_sum})"
    print("╠════════════════════════════════════════════════════╣")
    print(f"║ GF(3) Sum: {gf3_sum:+d}  {status:>30s}   ║")
    print("╚════════════════════════════════════════════════════╝")
    
    con.close()

def analyze_video(video: VideoEntry) -> dict:
    """Analyze a single video entry"""
    path = video.original_path
    exists = Path(path).exists()
    
    result = {
        'chaotic_id': video.chaotic_id,
        'filename': video.filename,
        'color_hex': video.color_hex,
        'trit': video.trit,
        'exists': exists,
    }
    
    if exists:
        meta = get_video_metadata(path)
        result.update(meta)
        result['keyframes'] = extract_keyframes(path, video.gay_seed, 3)
        # Compute file size
        result['size_mb'] = Path(path).stat().st_size / (1024 * 1024)
    
    return result

def main():
    db_path = "/Users/bob/ies/chaotic_media_lake.duckdb"
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "summary":
            triadic_summary(db_path)
            return
        elif sys.argv[1] == "analyze":
            trit_filter = int(sys.argv[2]) if len(sys.argv) > 2 else None
            videos = load_videos(db_path, trit_filter)
            for v in videos[:10]:
                result = analyze_video(v)
                status = "✓" if result['exists'] else "✗"
                print(f"{status} {result['color_hex']} t={result['trit']:+d} {result['filename'][:45]}")
                if result['exists']:
                    dur = result.get('duration', 0)
                    w, h = result.get('width', 0), result.get('height', 0)
                    codec = result.get('codec', '?')
                    size = result.get('size_mb', 0)
                    print(f"    {dur:.1f}s | {w}x{h} | {codec} | {size:.1f}MB")
                    if result.get('keyframes'):
                        print(f"    Keyframes: {', '.join(result['keyframes'][:3])}")
            return
    
    # Default: show summary
    triadic_summary(db_path)
    
    print("\nUsage:")
    print("  python triadic_video_analyzer.py summary")
    print("  python triadic_video_analyzer.py analyze [trit]")

if __name__ == "__main__":
    main()
