#!/usr/bin/env python3
"""SYZ35 probe: the punctured-pair interior law localised to union-generation.

Model = probe_syz34 (RS[n,k] dual shortenings on cores).  Verifies, for post-merge band triples:

  (1) exact reduction:  obj = dA + dB + dC - dim(A+B+C)   [obj = dim((A+B) cap C)]
  (2) lower bracket:    obj >= (dA+dB+dC) - dim(D_union)   (= target closed form)
  (3) generation equiv: obj == max(0,target)  iff  dim(A+B+C) == dim(D_union)   (target>=0)

target = |CA cap CB| + |CA cap CC| + |CB cap CC| - |triple| - 2k.
Confirms SYZ35's claims: (1),(2),(3) hold; the sharp upper bound obj<=max(0,target) is EQUIVALENT
to union-generation (the residual), not a separable fact.
"""
import random, importlib.util, os
spec = importlib.util.spec_from_file_location(
    "p34", os.path.join(os.path.dirname(__file__), "probe_syz34.py"))
p34 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p34)
dbs, rd = p34.dual_basis_on_support, p34.rref_dim

def run(n, p, trials, seed):
    random.seed(seed); k = n // 2; pts = random.sample(range(p), n)
    v1 = v2 = v3 = ok = 0
    for _ in range(trials):
        s = random.randint(k + 1, n - 1)
        allc = list(range(n))
        CA = set(random.sample(allc, s)); CB = set(random.sample(allc, s)); CC = set(random.sample(allc, s))
        ov = lambda X, Y: len(X & Y)
        if max(ov(CA, CB), ov(CA, CC), ov(CB, CC)) > k - 1:
            continue
        A = dbs(pts, k, CA, p); B = dbs(pts, k, CB, p); C = dbs(pts, k, CC, p)
        dA = rd(A, n, p); dB = rd(B, n, p); dC = rd(C, n, p)
        dABC = rd(A + B + C, n, p)
        obj = rd(A + B, n, p) + dC - dABC
        pair = ov(CA, CB) + ov(CA, CC) + ov(CB, CC); trip = len(CA & CB & CC)
        target = pair - trip - 2 * k
        dUnion = len(CA | CB | CC) - k
        if obj != dA + dB + dC - dABC: v1 += 1
        if obj < dA + dB + dC - dUnion: v2 += 1
        if target >= 0 and ((obj == max(0, target)) != (dABC == dUnion)): v3 += 1
        ok += 1
    print(f"n={n} k={k} p={p}: tested={ok}  (1)reduction_viol={v1}  (2)lower_viol={v2}  (3)gen_equiv_viol={v3}")

if __name__ == '__main__':
    for p in [61, 101, 257]:
        for n in [16, 20, 24, 30]:
            run(n, p, 4000, seed=n * 100 + p)
