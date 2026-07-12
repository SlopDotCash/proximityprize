#!/usr/bin/env python3
# G220 exact witness generator for the Lean certificate.
# Emits exact integers for a set of witnesses proving:
#  (a) A_signed = p*C - sumW*sumR  (the physical signed correlation, = p*Sum_{chi!=1} What conj(Rhat))
#      realizes BOTH signs at fixed rank across cells (physical-space sign no-go);
#  (b) the on-W-support "diagonal" partial sum D_on (dominant term) also realizes
#      BOTH signs => no diagonal-dominance sign certificate.
# Every number here is an exact integer and is recomputed float-free.
import json
import os
import tempfile
from itertools import combinations


def order_of(a, p):
    o, cur = 1, a % p
    while cur != 1:
        cur = (cur * a) % p
        o += 1
    return o


def prim_root(p):
    for a in range(2, p):
        if order_of(a, p) == p - 1:
            return a
    raise RuntimeError


def subgroup(p, n):
    m = (p - 1) // n
    h = pow(prim_root(p), m, p)
    G, cur = [], 1
    for _ in range(n):
        G.append(cur)
        cur = (cur * h) % p
    return sorted(set(G))


def W_profile(p, G):
    W = [0] * p
    for y in G:
        ty = (2 * y) % p
        for z in G:
            W[(ty - z) % p] += 1
    return W


def R_profile(p, G, r):
    R = [0] * p
    for A in combinations(G, r):
        R[sum(A) % p] += 1
    return R


def cell(p, n, r):
    G = subgroup(p, n)
    W = W_profile(p, G)
    R = R_profile(p, G, r)
    sumW, sumR = sum(W), sum(R)
    C = sum(W[x] * R[x] for x in range(p))
    A_signed = p * C - sumW * sumR
    Wsupp = set(x for x in range(p) if W[x] > 0)
    # p * A_signed decomposed on/off W-support (integer):
    def tval(x):
        return p * p * W[x] * R[x] - p * W[x] * sumR - p * R[x] * sumW + sumW * sumR
    D_on = sum(tval(x) for x in Wsupp)         # = p * (on-support part of A_signed)
    D_off = sum(tval(x) for x in range(p) if x not in Wsupp)
    assert D_on + D_off == p * A_signed, "decomposition identity failed"
    return dict(p=p, n=n, r=r, sumW=sumW, sumR=sumR, C=C,
                A_signed=A_signed, D_on=D_on, D_off=D_off,
                sign_A=(1 if A_signed > 0 else -1),
                sign_Don=(1 if D_on > 0 else -1))


# Chosen witnesses: opposite A-signs at fixed rank, and opposite D_on signs.
WITS = [
    # (label, p, n, r)
    ("posA_n8p257r5",   257, 8, 5),    # A_signed > 0
    ("negA_n8p97r5",     97, 8, 5),    # A_signed < 0  (r=5 sign flip)
    ("posDon_n16p97r6",  97, 16, 6),   # D_on > 0
    ("negDon_n16p97r5",  97, 16, 5),   # D_on < 0  (diagonal sign flip at same p,n)
    ("posA_n32p257r5",  257, 32, 5),   # A_signed > 0
    ("negA_n32p1153r5",1153, 32, 5),   # A_signed < 0  (r=5 sign flip, large m)
]


def main():
    out = []
    for label, p, n, r in WITS:
        d = cell(p, n, r)
        d["label"] = label
        out.append(d)
        print(f"{label:>20}: p={p} n={n} r={r}  A_signed={d['A_signed']:>16} "
              f"sign_A={d['sign_A']:+d}  D_on={d['D_on']:>20} sign_Don={d['sign_Don']:+d}")
    # Assertions the Lean file will encode:
    a5 = [d for d in out if d['r'] == 5 and d['n'] in (8, 32)]
    signs_a5 = set(d['sign_A'] for d in a5)
    assert signs_a5 == {1, -1}, "r=5 A_signed does not realize both signs"
    don = [d for d in out if d['n'] == 16]
    signs_don = set(d['sign_Don'] for d in don)
    assert signs_don == {1, -1}, "D_on does not realize both signs at n=16"
    print("\nPASS: r=5 A_signed realizes BOTH signs; on-support diagonal D_on realizes BOTH signs.")
    print("=> physical-space signed correlation sign NOT forced; no diagonal-dominance certificate.")
    # Reproducible from a clean checkout: prefer the report dir if present,
    # else fall back to a portable temp directory (create it if needed).
    out_dir = "/tmp/arklib-reports"
    if not os.path.isdir(out_dir):
        out_dir = os.path.join(tempfile.gettempdir(), "arklib-reports")
        os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, "oc_g220_witnesses.json")
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"wrote {out_path}")


if __name__ == '__main__':
    main()
