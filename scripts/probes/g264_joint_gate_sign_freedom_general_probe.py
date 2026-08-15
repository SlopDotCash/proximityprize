#!/usr/bin/env python3
"""
G264 self-contained probe: general joint-gate sign-freedom is r-uniform, not a fixed-depth island.

Claim (formalized in _G264JointGateSignFreedomGeneral.lean):
  For ANY cyclic length m, ANY two ZERO-SUM integer functionals f,g : Z/m -> Z with a nonzero
  2x2 minor D = f_i*g_j - f_j*g_i at some coordinate pair i != j, the NONNEGATIVE-INTEGER kernel
  cone realizes ALL FOUR open sign quadrants of (<W,f>, <W,g>).

Closed-form Cramer witness (exactly the Lean construction):
  target sign pair (s,t) in {+-1}^2:
    a = s*g_j - t*f_j ,  b = t*f_i - s*g_i ,  c = max(0, -min(a,b,0))  (nonneg offset)
    W = c*1 + a*e_i + b*e_j
  Because f,g are zero-sum, the constant offset c*1 contributes 0 to both pairings, and
    <W,f> = a*f_i + b*f_j = s*D ,   <W,g> = a*g_i + b*g_j = t*D   (exact algebra)
  so sign(<W,f>) = s*sign(D), sign(<W,g>) = t*sign(D); ranging (s,t) hits all four quadrants
  regardless of sign(D), and W >= 0 entrywise.

This probe:
  1. reproduces the exact G263 minimal cell (m=5, minor 15) from the general construction;
  2. stresses the construction on thousands of random cells / rank pairs (varying m), asserting
     the exact identities <W,f>=s*D, <W,g>=t*D, W>=0, and all four sign quadrants realized;
  3. also directly instantiates the two live prize ranks r=5,6 as integer rank-weight surrogates
     to confirm the mechanism is not special to any fixed depth.

Exit non-zero (hard failure) if ANY asserted identity or sign is violated.
"""
import random
import sys

def dot(W, v):
    return sum(W[x] * v[x] for x in range(len(v)))

def centered(R):
    m = len(R)
    s = sum(R)
    return [m * R[x] - s for x in range(m)]

def find_minor_pair(f, g):
    m = len(f)
    for i in range(m):
        for j in range(i + 1, m):
            if f[i] * g[j] - f[j] * g[i] != 0:
                return i, j
    return None

def witness(f, g, i, j, s, t):
    """Closed-form Cramer witness kernel for target sign pair (s,t)."""
    a = s * g[j] - t * f[j]
    b = t * f[i] - s * g[i]
    m = len(f)
    base = [0] * m
    base[i] += a
    base[j] += b
    c = max(0, -min(base))
    W = [base[x] + c for x in range(m)]
    return W, a, b

def check_all_quadrants(f, g, i, j, label=""):
    D = f[i] * g[j] - f[j] * g[i]
    assert D != 0, f"{label}: zero minor"
    assert sum(f) == 0 and sum(g) == 0, f"{label}: functionals not zero-sum"
    seen = set()
    for s in (1, -1):
        for t in (1, -1):
            W, a, b = witness(f, g, i, j, s, t)
            assert all(w >= 0 for w in W), f"{label}: W has a negative entry: {W}"
            cf = dot(W, f)
            cg = dot(W, g)
            # exact Cramer identities
            assert cf == s * D, f"{label}: <W,f>={cf} != s*D={s*D} (s={s},t={t})"
            assert cg == t * D, f"{label}: <W,g>={cg} != t*D={t*D} (s={s},t={t})"
            # sign quadrant realized
            sf = 1 if cf > 0 else (-1 if cf < 0 else 0)
            sg = 1 if cg > 0 else (-1 if cg < 0 else 0)
            assert sf != 0 and sg != 0, f"{label}: degenerate sign (s={s},t={t})"
            seen.add((sf, sg))
    assert seen == {(1, 1), (1, -1), (-1, 1), (-1, -1)}, \
        f"{label}: did not realize all four quadrants, got {seen}"
    return D

def main():
    # 1. exact G263 minimal cell
    R5 = [0, 1, 0, 1, 2]
    R6 = [1, 0, 2, 0, 1]
    f = centered(R5)
    g = centered(R6)
    assert f == [-4, 1, -4, 1, 6], f
    assert g == [1, -4, 6, -4, 1], g
    pair = find_minor_pair(f, g)
    assert pair == (0, 1), pair
    D = check_all_quadrants(f, g, 0, 1, "G263 cell")
    assert D == 15, D
    print(f"[1] G263 minimal cell reproduced from general construction: minor D={D}, all four quadrants OK")

    # 2. random stress across many cells / rank pairs
    random.seed(20260713)
    total = 0
    passed = 0
    for _ in range(5000):
        m = random.randint(3, 14)
        Ra = [random.randint(0, 7) for _ in range(m)]
        Rb = [random.randint(0, 7) for _ in range(m)]
        f = centered(Ra)
        g = centered(Rb)
        pair = find_minor_pair(f, g)
        if pair is None:
            continue
        total += 1
        i, j = pair
        check_all_quadrants(f, g, i, j, f"rand m={m}")
        passed += 1
    assert total == passed, (total, passed)
    print(f"[2] random stress: {passed}/{total} independent (m, rank-pair) cells realize all four quadrants exactly")

    # 3. explicit r=5 and r=6 rank-weight surrogates on several primes-of-life m to show
    #    the mechanism is depth-uniform (not a fixed-depth island)
    depth_uniform = 0
    for m in (11, 13, 16, 17, 23, 31):
        R5 = [pow(x, 5, m) for x in range(m)]
        R6 = [pow(x, 6, m) for x in range(m)]
        f = centered(R5)
        g = centered(R6)
        pair = find_minor_pair(f, g)
        if pair is None:
            continue
        i, j = pair
        check_all_quadrants(f, g, i, j, f"r=5,6 surrogate m={m}")
        depth_uniform += 1
    assert depth_uniform >= 4, depth_uniform
    print(f"[3] r=5/r=6 rank-weight surrogates: {depth_uniform} cyclic lengths all sign-free -> depth-uniform")

    print("G264 PROBE PASS: joint two-rank centered gate is sign-free at every cell/rank pair with independent centered functionals.")

if __name__ == "__main__":
    try:
        main()
    except AssertionError as e:
        print(f"G264 PROBE FAIL: {e}", file=sys.stderr)
        sys.exit(1)
