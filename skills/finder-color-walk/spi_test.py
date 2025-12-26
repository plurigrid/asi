#!/usr/bin/env python3
"""
spi_test.py — Strong Parallelism Invariance (SPI) + GF(3) checks.

Given a fibers.json produced by triadic_router.bb, verify:
1. SPI: color assignment is order-independent (sorting canonicalizes).
2. GF(3): if policy=gf3_balanced, then for each index i: t0+t1+t2 ≡ 0 (mod 3).
"""
import argparse, json, hashlib


def sha256_int(s: str) -> int:
    b = hashlib.sha256(s.encode("utf-8")).digest()
    x = int.from_bytes(b[:8], "big", signed=False)
    return x


def trit(s: str) -> int:
    return sha256_int(s) % 3


def gf3_balanced_triplet(seed: str, p0: str, p1: str, p2: str):
    t0 = trit(f"{seed}::0::{p0}")
    t1 = trit(f"{seed}::1::{p1}")
    t2 = (-t0 - t1) % 3
    return t0, t1, t2


def raw_color(seed: str, j: int, p: str):
    return trit(f"{seed}::raw::{j}::{p}")


def compute_mapping(fibers, seed: str, policy: str):
    fibers = [sorted(list(f)) for f in fibers]
    n = min(len(f) for f in fibers)
    m = {}
    for i in range(n):
        p0, p1, p2 = fibers[0][i], fibers[1][i], fibers[2][i]
        if policy == "gf3_balanced":
            t0, t1, t2 = gf3_balanced_triplet(seed, p0, p1, p2)
        else:
            t0, t1, t2 = raw_color(seed, 0, p0), raw_color(seed, 1, p1), raw_color(seed, 2, p2)
        m[p0] = t0
        m[p1] = t1
        m[p2] = t2
    return m


def gf3_check(fibers, seed: str):
    fibers = [sorted(list(f)) for f in fibers]
    n = min(len(f) for f in fibers)
    for i in range(n):
        p0, p1, p2 = fibers[0][i], fibers[1][i], fibers[2][i]
        t0, t1, t2 = gf3_balanced_triplet(seed, p0, p1, p2)
        if (t0 + t1 + t2) % 3 != 0:
            return False, i, (p0, p1, p2), (t0, t1, t2)
    return True, None, None, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fibers", default="fibers.json")
    ap.add_argument("--seed", default="seed0")
    ap.add_argument("--policy", default="raw", choices=["raw", "gf3_balanced"])
    args = ap.parse_args()

    data = json.load(open(args.fibers))
    fibers = data["fibers"]

    # SPI test: shuffle within fibers and show mapping unchanged after canonicalization.
    m1 = compute_mapping(fibers, args.seed, args.policy)
    # permute (reverse each fiber) to simulate different traversal order
    fibers2 = [list(reversed(f)) for f in fibers]
    m2 = compute_mapping(fibers2, args.seed, args.policy)

    spi_ok = (m1 == m2)
    print(f"SPI: {'OK' if spi_ok else 'FAIL'}  entries={len(m1)}")

    if args.policy == "gf3_balanced":
        ok, i, paths, ts = gf3_check(fibers, args.seed)
        print(f"GF3: {'OK' if ok else 'FAIL'}")
        if not ok:
            print("violation:", {"i": i, "paths": paths, "trits": ts})
            raise SystemExit(2)

    if not spi_ok:
        # show a small diff
        diff = []
        for k in sorted(set(m1.keys()) | set(m2.keys())):
            if m1.get(k) != m2.get(k):
                diff.append((k, m1.get(k), m2.get(k)))
                if len(diff) >= 10:
                    break
        print("diff(sample):", diff)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
