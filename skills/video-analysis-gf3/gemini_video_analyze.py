#!/usr/bin/env python3
"""
Gemini 2.0 Flash Video Analysis with GF(3) Conservation
Analyzes videos from chaotic_media_lake with triadic classification
"""
import duckdb
import json
import sys
import subprocess
from pathlib import Path
from datetime import datetime

GOLDEN = 0x9e3779b97f4a7c15
MASK64 = 0xFFFFFFFFFFFFFFFF

def splitmix64(seed: int) -> tuple[int, int]:
    seed = (seed + GOLDEN) & MASK64
    z = seed
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK64
    return seed, (z ^ (z >> 31)) & MASK64

def trit_role(trit: int) -> str:
    return {-1: "VALIDATOR", 0: "ERGODIC", 1: "GENERATOR"}[trit]

def trit_prompt(trit: int) -> str:
    """Get analysis prompt based on trit class"""
    prompts = {
        -1: """Analyze this screen recording as a VALIDATOR (-1 trit).
Focus on: verification patterns, testing behavior, error detection, debugging sessions.
Identify: what is being validated, any issues found, success/failure patterns.""",
        
        0: """Analyze this video as an ERGODIC coordinator (0 trit).
Focus on: workflow patterns, scene transitions, coordination between tasks.
Identify: key moments, topic changes, information flow.""",
        
        1: """Analyze this video as a GENERATOR (+1 trit).
Focus on: creative output, code generation, content creation, synthesis.
Identify: what is being produced, tools used, generation patterns."""
    }
    return prompts.get(trit, prompts[0])

def analyze_with_gemini(video_path: str, trit: int, color_hex: str) -> dict:
    """Analyze video using Gemini 2.0 Flash via Python SDK"""
    try:
        from google import genai
        from google.genai import types
        
        client = genai.Client()
        
        # Upload video file
        print(f"  Uploading {Path(video_path).name}...")
        video_file = client.files.upload(file=video_path)
        
        # Wait for processing
        import time
        while video_file.state.name == "PROCESSING":
            time.sleep(2)
            video_file = client.files.get(name=video_file.name)
        
        if video_file.state.name == "FAILED":
            return {"error": "Video processing failed"}
        
        prompt = f"""
{trit_prompt(trit)}

Video metadata:
- Assigned color: {color_hex}
- Trit class: {trit:+d} ({trit_role(trit)})

Provide a structured analysis with:
1. SUMMARY (2-3 sentences)
2. KEY_MOMENTS (list of timestamps and descriptions)
3. TRIT_ALIGNMENT (how well does content match the {trit_role(trit)} role?)
4. MOTION_ESTIMATE (low/medium/high activity level)
"""
        
        response = client.models.generate_content(
            model="gemini-2.0-flash",
            contents=[video_file, prompt]
        )
        
        return {
            "summary": response.text,
            "model": "gemini-2.0-flash",
            "trit": trit,
            "color_hex": color_hex,
            "analyzed_at": datetime.now().isoformat()
        }
        
    except ImportError:
        return {"error": "google-genai not installed. Run: pip install google-genai"}
    except Exception as e:
        return {"error": str(e)}

def get_videos_for_analysis(db_path: str, trit_filter: int = None, limit: int = 5) -> list:
    """Get videos from chaotic_media_lake"""
    con = duckdb.connect(db_path, read_only=True)
    
    query = """
        SELECT chaotic_id, original_path, filename, color_hex, trit, gay_seed
        FROM chaotic_files
        WHERE extension IN ('.mov', '.mp4', '.MOV')
    """
    if trit_filter is not None:
        query += f" AND trit = {trit_filter}"
    query += f" ORDER BY shuffle_key LIMIT {limit}"
    
    videos = []
    for row in con.execute(query).fetchall():
        videos.append({
            'chaotic_id': row[0],
            'path': row[1],
            'filename': row[2],
            'color_hex': row[3],
            'trit': row[4],
            'seed': row[5]
        })
    con.close()
    return videos

def store_analysis(db_path: str, chaotic_id: str, analysis: dict):
    """Store analysis results back to DuckDB"""
    con = duckdb.connect(db_path)
    
    # Ensure columns exist
    try:
        con.execute("ALTER TABLE chaotic_files ADD COLUMN IF NOT EXISTS analysis_json TEXT")
        con.execute("ALTER TABLE chaotic_files ADD COLUMN IF NOT EXISTS analyzed_at TIMESTAMP")
    except:
        pass
    
    con.execute("""
        UPDATE chaotic_files 
        SET analysis_json = ?, analyzed_at = ?
        WHERE chaotic_id = ?
    """, [json.dumps(analysis), datetime.now(), chaotic_id])
    
    con.close()

def main():
    db_path = "/Users/bob/ies/chaotic_media_lake.duckdb"
    
    if len(sys.argv) < 2:
        print("Usage:")
        print("  python gemini_video_analyze.py list [trit]")
        print("  python gemini_video_analyze.py analyze <chaotic_id>")
        print("  python gemini_video_analyze.py batch [trit] [limit]")
        return
    
    cmd = sys.argv[1]
    
    if cmd == "list":
        trit = int(sys.argv[2]) if len(sys.argv) > 2 else None
        videos = get_videos_for_analysis(db_path, trit, limit=20)
        
        print(f"\n{'Chaotic ID':<14} {'Trit':>5} {'Color':<8} {'Filename'}")
        print("-" * 70)
        for v in videos:
            exists = "✓" if Path(v['path']).exists() else "✗"
            print(f"{exists} {v['chaotic_id']:<12} {v['trit']:+5d} {v['color_hex']:<8} {v['filename'][:40]}")
    
    elif cmd == "analyze":
        if len(sys.argv) < 3:
            print("Error: provide chaotic_id")
            return
        
        chaotic_id = sys.argv[2]
        con = duckdb.connect(db_path, read_only=True)
        row = con.execute("""
            SELECT original_path, color_hex, trit 
            FROM chaotic_files WHERE chaotic_id = ?
        """, [chaotic_id]).fetchone()
        con.close()
        
        if not row:
            print(f"Not found: {chaotic_id}")
            return
        
        path, color_hex, trit = row
        if not Path(path).exists():
            print(f"File missing: {path}")
            return
        
        print(f"\n🎬 Analyzing: {Path(path).name}")
        print(f"   Color: {color_hex} | Trit: {trit:+d} ({trit_role(trit)})")
        
        result = analyze_with_gemini(path, trit, color_hex)
        
        if "error" in result:
            print(f"   ❌ Error: {result['error']}")
        else:
            print(f"\n{result['summary']}")
            store_analysis(db_path, chaotic_id, result)
            print(f"\n✓ Analysis stored to chaotic_media_lake.duckdb")
    
    elif cmd == "batch":
        trit = int(sys.argv[2]) if len(sys.argv) > 2 else None
        limit = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        
        videos = get_videos_for_analysis(db_path, trit, limit)
        
        for v in videos:
            if not Path(v['path']).exists():
                print(f"✗ Missing: {v['filename']}")
                continue
            
            print(f"\n{'='*60}")
            print(f"🎬 {v['color_hex']} t={v['trit']:+d} {v['filename'][:45]}")
            
            result = analyze_with_gemini(v['path'], v['trit'], v['color_hex'])
            
            if "error" in result:
                print(f"❌ {result['error']}")
            else:
                # Print first 500 chars of summary
                summary = result.get('summary', '')[:500]
                print(summary)
                store_analysis(db_path, v['chaotic_id'], result)

if __name__ == "__main__":
    main()
