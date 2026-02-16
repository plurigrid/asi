#!/usr/bin/env python3
"""
Indefinite Causal Order over GF(3) — Vectorized (NumPy)

Batch process matrices, quantum switch, causal witnesses.
Runs on DGX Spark (numpy 2.4.2) or any system with numpy.
PyTorch/CUDA version can be trivially derived by replacing np→torch.

GF(3) trit: 0 (ERGODIC — coordination)
"""

import numpy as np
import time

# ═══════════════════════════════════════════════════════════════
# §1  GF(3) Arithmetic (vectorized)
# ═══════════════════════════════════════════════════════════════

def gf3_add(a, b):
    """GF(3) addition: (a + b) mod 3 in balanced {-1, 0, +1}."""
    return ((np.asarray(a) + np.asarray(b) + 1) % 3) - 1

def gf3_mul(a, b):
    """GF(3) multiplication."""
    return ((np.asarray(a) * np.asarray(b) + 1) % 3) - 1

def gf3_neg(a):
    return -np.asarray(a)

def gf3_matmul(A, B):
    """GF(3) matrix multiply for batch of 3×3 matrices.
    A: (batch, 3, 3), B: (batch, 3, 3) → C: (batch, 3, 3)"""
    C = np.zeros_like(A)
    for i in range(3):
        for j in range(3):
            s = np.zeros(A.shape[0], dtype=A.dtype)
            for k in range(3):
                s = gf3_add(s, gf3_mul(A[:, i, k], B[:, k, j]))
            C[:, i, j] = s
    return C

def gf3_matadd(A, B):
    return gf3_add(A, B)

def gf3_det(M):
    """GF(3) 3×3 determinant via Sarrus (batched)."""
    pos1 = gf3_mul(gf3_mul(M[:,0,0], M[:,1,1]), M[:,2,2])
    pos2 = gf3_mul(gf3_mul(M[:,0,1], M[:,1,2]), M[:,2,0])
    pos3 = gf3_mul(gf3_mul(M[:,0,2], M[:,1,0]), M[:,2,1])
    neg1 = gf3_mul(gf3_mul(M[:,0,2], M[:,1,1]), M[:,2,0])
    neg2 = gf3_mul(gf3_mul(M[:,0,1], M[:,1,0]), M[:,2,2])
    neg3 = gf3_mul(gf3_mul(M[:,0,0], M[:,1,2]), M[:,2,1])
    d = gf3_add(gf3_add(pos1, pos2), pos3)
    d = gf3_add(d, gf3_neg(neg1))
    d = gf3_add(d, gf3_neg(neg2))
    d = gf3_add(d, gf3_neg(neg3))
    return d


# ═══════════════════════════════════════════════════════════════
# §2  Channels (batched)
# ═══════════════════════════════════════════════════════════════

def make_channel(M, batch):
    return np.tile(M, (batch, 1, 1)).astype(np.int64)

def make_cnot(batch):
    return make_channel([[1,0,0],[1,1,0],[0,0,1]], batch)

def make_permute(batch):
    return make_channel([[0,1,0],[0,0,1],[1,0,0]], batch)

def make_random_channels(batch):
    """Random invertible GF(3) channel matrices."""
    M = np.random.randint(-1, 2, (batch, 3, 3)).astype(np.int64)
    dets = gf3_det(M)
    # Retry non-invertible ones
    mask = dets == 0
    while mask.any():
        M[mask] = np.random.randint(-1, 2, (mask.sum(), 3, 3)).astype(np.int64)
        dets = gf3_det(M)
        mask = dets == 0
    return M


# ═══════════════════════════════════════════════════════════════
# §3  Quantum Switch (batched)
# ═══════════════════════════════════════════════════════════════

def quantum_switch(C1, C2, control):
    """Batch quantum switch."""
    if control == 0:
        return gf3_matmul(C1, C2)
    elif control == 1:
        return gf3_matmul(C2, C1)
    else:
        return gf3_matadd(gf3_matmul(C1, C2), gf3_matmul(C2, C1))


# ═══════════════════════════════════════════════════════════════
# §4  Analysis
# ═══════════════════════════════════════════════════════════════

def check_commutativity(C1, C2):
    fwd = gf3_matmul(C1, C2)
    rev = gf3_matmul(C2, C1)
    return np.all(fwd == rev, axis=(1, 2))

def det_invariant(C1, C2):
    S0 = quantum_switch(C1, C2, 0)
    S1 = quantum_switch(C1, C2, 1)
    Sm = quantum_switch(C1, C2, -1)
    return {
        "det_S0": gf3_det(S0),
        "det_S1": gf3_det(S1),
        "det_Sm": gf3_det(Sm),
        "ico_flips_det": gf3_det(Sm) != gf3_det(S0),
        "commuting": check_commutativity(C1, C2),
    }

def parity_distribution(M_single):
    """Output parity distribution for a channel on all 27 cells."""
    cells = np.array([[f,p,a] for f in [-1,0,1] for p in [-1,0,1] for a in [-1,0,1]], dtype=np.int64)
    out = np.zeros_like(cells)
    for i in range(3):
        s = np.zeros(27, dtype=np.int64)
        for j in range(3):
            s = gf3_add(s, gf3_mul(M_single[i, j], cells[:, j]))
        out[:, i] = s
    parities = gf3_add(gf3_add(out[:,0], out[:,1]), out[:,2])
    return {"minus": (parities == -1).sum(), "zero": (parities == 0).sum(), "plus": (parities == 1).sum()}


# ═══════════════════════════════════════════════════════════════
# §5  Benchmarks
# ═══════════════════════════════════════════════════════════════

def benchmark_quantum_switch(batch_sizes=[100, 1000, 10000, 100000]):
    print("\n" + "=" * 60)
    print("  Quantum Switch Benchmark (NumPy vectorized)")
    print("=" * 60)

    for bs in batch_sizes:
        C1 = make_cnot(bs)
        C2 = make_permute(bs)

        # Warmup
        _ = quantum_switch(C1, C2, -1)

        t0 = time.perf_counter()
        S0 = quantum_switch(C1, C2, 0)
        S1 = quantum_switch(C1, C2, 1)
        Sm = quantum_switch(C1, C2, -1)
        elapsed = time.perf_counter() - t0

        sps = (3 * bs) / elapsed
        print(f"  batch={bs:>7d}  time={elapsed*1000:7.1f}ms  switches/sec={sps:>12,.0f}")

def benchmark_random_pairs(n_pairs=10000):
    print("\n" + "=" * 60)
    print(f"  Random Channel Pair Analysis (n={n_pairs})")
    print("=" * 60)

    t0 = time.perf_counter()
    C1 = make_random_channels(n_pairs)
    C2 = make_random_channels(n_pairs)
    result = det_invariant(C1, C2)
    elapsed = time.perf_counter() - t0

    n_comm = result["commuting"].sum()
    n_flip = result["ico_flips_det"].sum()
    n_noncomm = n_pairs - n_comm

    print(f"  Time: {elapsed*1000:.1f}ms")
    print(f"  Commuting pairs: {n_comm}/{n_pairs} ({100*n_comm/n_pairs:.1f}%)")
    print(f"  Non-commuting: {n_noncomm}/{n_pairs} ({100*n_noncomm/n_pairs:.1f}%)")
    print(f"  ICO flips det: {n_flip}/{n_pairs} ({100*n_flip/n_pairs:.1f}%)")
    if n_noncomm > 0:
        print(f"  Det flip rate (non-commuting): {n_flip}/{n_noncomm} ({100*n_flip/n_noncomm:.1f}%)")

    # Determinant distribution for ICO case
    dm = result["det_Sm"]
    print(f"\n  det(S(-1)) distribution:")
    print(f"    -1: {(dm == -1).sum():>5d}  ({100*(dm == -1).mean():.1f}%)")
    print(f"     0: {(dm == 0).sum():>5d}  ({100*(dm == 0).mean():.1f}%)")
    print(f"    +1: {(dm == 1).sum():>5d}  ({100*(dm == 1).mean():.1f}%)")


# ═══════════════════════════════════════════════════════════════
# §6  Demo
# ═══════════════════════════════════════════════════════════════

def demo():
    print("\n╔" + "═" * 58 + "╗")
    print("║  INDEFINITE CAUSAL ORDER — Vectorized NumPy             ║")
    print("╚" + "═" * 58 + "╝\n")

    # Verification (matches Julia/Zig/Boxxy)
    C1 = make_cnot(1)
    C2 = make_permute(1)

    print("Channels:")
    print(f"  C1 = CNOT(freq→phase)  det = {gf3_det(C1)[0]}")
    print(f"  C2 = Cyclic permutation det = {gf3_det(C2)[0]}")
    print(f"  Commuting: {check_commutativity(C1, C2)[0]}")

    S0 = quantum_switch(C1, C2, 0)
    S1 = quantum_switch(C1, C2, 1)
    Sm = quantum_switch(C1, C2, -1)

    print("\nQuantum Switch:")
    print(f"  S(0)  det = {gf3_det(S0)[0]}")
    print(f"  S(+1) det = {gf3_det(S1)[0]}")
    print(f"  S(-1) det = {gf3_det(Sm)[0]}")
    print(f"  S(0) == S(+1): {np.array_equal(S0, S1)}")

    dist = parity_distribution(Sm[0])
    print(f"\nParity (ICO, 27 cells): MINUS={dist['minus']} ERGODIC={dist['zero']} PLUS={dist['plus']}")

    ctrl_sum = gf3_add(gf3_add(0, 1), -1)
    print(f"\nGF(3) control conservation: Σ(0,+1,-1) = {ctrl_sum}  Conserved: {ctrl_sum == 0}")

    # Benchmarks
    benchmark_quantum_switch()
    benchmark_random_pairs()

    print("\n" + "=" * 60)
    print("  Complete. GF(3) trit: 0 (ERGODIC)")
    print("=" * 60)


if __name__ == "__main__":
    demo()
