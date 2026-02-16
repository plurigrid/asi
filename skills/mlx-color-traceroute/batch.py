#!/usr/bin/env python3
"""JAX batch - 10k colors parallel"""
import os;os.environ["JAX_ENABLE_X64"]="1"
import jax.numpy as jnp;from jax import jit
@jit
def batch(s,n):
    i=jnp.arange(n);z=jnp.uint64(s)^i.astype(jnp.uint64)
    z=(z^(z>>30))*jnp.uint64(0xBF58476D1CE4E5B9);z=(z^(z>>27))*jnp.uint64(0x94D049BB133111EB);z=z^(z>>31)
    return z%65536/65536*360,z%3-1
import sys,time;s=int(sys.argv[1],16)if len(sys.argv)>1 else 0x42D;n=int(sys.argv[2])if len(sys.argv)>2 else 10000
t0=time.perf_counter();h,tr=batch(s,n);h.block_until_ready()
print(f"{n} colors in {(time.perf_counter()-t0)*1000:.2f}ms | trit_sum={int(tr.sum())}mod3={int(tr.sum())%3}")
