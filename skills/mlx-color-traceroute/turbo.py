#!/usr/bin/env python3
"""
Turbo Color Traceroute - Maximum speed Gay.jl colors via JAX/MLX → ACSet
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
import sys, time, json
import numpy as np

# ═══════════════════════════════════════════════════════════════════════════
# Backend selection: JAX > MLX > NumPy
# ═══════════════════════════════════════════════════════════════════════════

BACKEND = "numpy"
try:
    import jax
    jax.config.update("jax_enable_x64", True)
    import jax.numpy as xp
    from jax import jit
    BACKEND = "jax"
    @jit
    def sm64(s, i):
        z = s ^ i
        z = (z ^ (z >> 30)) * xp.uint64(0xBF58476D1CE4E5B9)
        z = (z ^ (z >> 27)) * xp.uint64(0x94D049BB133111EB)
        return z ^ (z >> 31)
    def sync(x): x.block_until_ready(); return x
except:
    try:
        import mlx.core as xp
        BACKEND = "mlx"
        def sm64(s, i):
            z = (s ^ i).astype(xp.uint32)  # MLX uint32 only
            z = (z ^ (z >> 15)) * xp.array(0x85EBCA6B, dtype=xp.uint32)
            z = (z ^ (z >> 13)) * xp.array(0xC2B2AE35, dtype=xp.uint32)
            return z ^ (z >> 16)
        def sync(x): xp.eval(x); return x
    except:
        xp = np
        def sm64(s, i):
            z = np.uint64(s) ^ i.astype(np.uint64)
            z = (z ^ (z >> 30)) * np.uint64(0xBF58476D1CE4E5B9)
            z = (z ^ (z >> 27)) * np.uint64(0x94D049BB133111EB)
            return z ^ (z >> 31)
        def sync(x): return x

# ═══════════════════════════════════════════════════════════════════════════
# Batch color generation
# ═══════════════════════════════════════════════════════════════════════════

def batch_colors(seed: int, n: int):
    """Generate n colors from seed, returns (states, hues, trits)"""
    if BACKEND == "jax":
        i = xp.arange(n, dtype=xp.uint64)
        s = xp.uint64(seed)
    elif BACKEND == "mlx":
        i = xp.arange(n).astype(xp.uint32)
        s = xp.array(seed & 0xFFFFFFFF, dtype=xp.uint32)
    else:
        i = np.arange(n, dtype=np.uint64)
        s = np.uint64(seed)
    
    z = sync(sm64(s, i))
    hue = sync((z % 65536).astype(xp.float32 if BACKEND != "numpy" else np.float32) / 65536 * 360)
    trit = sync((z % 3).astype(xp.int32 if BACKEND != "numpy" else np.int32) - 1)
    return z, hue, trit

# ═══════════════════════════════════════════════════════════════════════════
# ACSet export (Catlab-compatible)
# ═══════════════════════════════════════════════════════════════════════════

def to_acset(seed: int, n: int, servers: list = None):
    """Create ACSet JSON from batch colors"""
    z, hue, trit = batch_colors(seed, n)
    
    # Convert to numpy for JSON serialization
    if BACKEND == "jax":
        z, hue, trit = np.array(z), np.array(hue), np.array(trit)
    elif BACKEND == "mlx":
        z, hue, trit = np.array(z.tolist()), np.array(hue.tolist()), np.array(trit.tolist())
    
    servers = servers or [f"hop_{i}" for i in range(n)]
    if len(servers) < n:
        servers = servers + [f"hop_{i}" for i in range(len(servers), n)]
    
    return {
        "schema": {"name": "ColorBatch", "obs": ["Hop"], 
                   "attrs": [{"name": "hue", "dom": "Hop", "codom": "Float"},
                            {"name": "trit", "dom": "Hop", "codom": "Int"},
                            {"name": "state", "dom": "Hop", "codom": "UInt64"}]},
        "tables": {
            "Hop": {
                "_id": list(range(n)),
                "hue": hue.tolist(),
                "trit": trit.tolist(),
                "state": [int(x) for x in z],
                "server": servers[:n],
            }
        },
        "fingerprint": int(np.bitwise_xor.reduce(z.astype(np.uint64))),
        "trit_sum": int(trit.sum()),
        "balanced": int(trit.sum()) % 3 == 0,
    }

# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════

def main():
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    export = "--json" in sys.argv
    
    # Warmup
    if n > 100:
        batch_colors(seed, min(1000, n // 10))
    
    t0 = time.perf_counter()
    z, hue, trit = batch_colors(seed, n)
    dt = time.perf_counter() - t0
    
    # Convert for display
    if BACKEND == "jax":
        hue, trit = np.array(hue), np.array(trit)
    elif BACKEND == "mlx":
        hue, trit = np.array(hue.tolist()), np.array(trit.tolist())
    
    if export:
        acset = to_acset(seed, n)
        print(json.dumps(acset, indent=2))
    else:
        print(f"TURBO [{BACKEND.upper()}] seed=0x{seed:X} n={n:,}")
        print(f"Time: {dt*1000:.2f}ms ({n/dt/1e6:.1f}M/sec)")
        print()
        
        # Show first 8 and last if large
        show_n = min(8, n)
        for i in range(show_n):
            h = float(hue[i])
            t = int(trit[i])
            r = int(128 + 127 * np.cos((h - 0) * np.pi / 180))
            g = int(128 + 127 * np.cos((h - 120) * np.pi / 180))
            b = int(128 + 127 * np.cos((h - 240) * np.pi / 180))
            print(f"\033[48;2;{r};{g};{b}m  \033[0m {i:3d} {h:6.1f}° {'−○+'[t+1]}")
        
        if n > 8:
            print(f"... ({n - 8:,} more)")
        
        tsum = int(trit.sum())
        print(f"\nΣtrit={tsum} mod3={tsum%3} {'✓' if tsum%3==0 else '○'}")

if __name__ == "__main__":
    main()
