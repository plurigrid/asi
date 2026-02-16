#!/usr/bin/env python3
"""GPU-accelerated color generation - JAX/Metal/CUDA"""
import sys, time
import numpy as np

# Select backend
BACKEND = None
try:
    import jax
    jax.config.update("jax_enable_x64", True)
    import jax.numpy as jnp
    from jax import jit, devices
    BACKEND = "jax"
    DEVICE = str(devices()[0])
    
    @jit
    def sm64(s, i):
        z = jnp.uint64(s) ^ i.astype(jnp.uint64)
        z = (z ^ (z >> 30)) * jnp.uint64(0xBF58476D1CE4E5B9)
        z = (z ^ (z >> 27)) * jnp.uint64(0x94D049BB133111EB)
        return z ^ (z >> 31)
    
    def run(seed, n):
        i = jnp.arange(n, dtype=jnp.uint64)
        z = sm64(seed, i)
        z.block_until_ready()
        h = (z % 65536).astype(jnp.float32) / 65536 * 360
        t = (z % 3).astype(jnp.int32) - 1
        return np.array(z), np.array(h), np.array(t)
        
except ImportError:
    try:
        import mlx.core as mx
        BACKEND = "mlx"
        DEVICE = "Metal"
        
        def sm32(s, i):
            z = mx.array(s, dtype=mx.uint32) ^ i.astype(mx.uint32)
            z = (z ^ (z >> 15)) * mx.array(0x85EBCA6B, dtype=mx.uint32)
            z = (z ^ (z >> 13)) * mx.array(0xC2B2AE35, dtype=mx.uint32)
            return z ^ (z >> 16)
        
        def run(seed, n):
            i = mx.arange(n)
            z = sm32(seed & 0xFFFFFFFF, i)
            mx.eval(z)
            h = (z % 65536).astype(mx.float32) / 65536 * 360
            t = (z % 3).astype(mx.int32) - 1
            mx.eval(h, t)
            return np.array(z.tolist()), np.array(h.tolist()), np.array(t.tolist())
            
    except ImportError:
        BACKEND = "numpy"
        DEVICE = "CPU"
        
        def run(seed, n):
            i = np.arange(n, dtype=np.uint64)
            z = np.uint64(seed) ^ i
            z = (z ^ (z >> 30)) * np.uint64(0xBF58476D1CE4E5B9)
            z = (z ^ (z >> 27)) * np.uint64(0x94D049BB133111EB)
            z = z ^ (z >> 31)
            h = (z % 65536).astype(np.float32) / 65536 * 360
            t = (z % 3).astype(np.int32) - 1
            return z, h, t

def main():
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    n = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10_000_000
    
    # Warmup
    if BACKEND == "jax":
        _ = run(seed, min(1000, n))
    
    t0 = time.perf_counter()
    z, h, t = run(seed, n)
    dt = time.perf_counter() - t0
    
    rate = n / dt / 1e6
    tsum = int(t.sum())
    fp = int(np.bitwise_xor.reduce(z.astype(np.uint64)))
    
    print(f"{BACKEND.upper()} [{DEVICE}]")
    print(f"{n:,} colors in {dt*1000:.1f}ms = {rate:.0f}M/sec")
    print(f"Σtrit={tsum} mod3={tsum%3} fp=0x{fp:016X}")

if __name__ == "__main__":
    main()
