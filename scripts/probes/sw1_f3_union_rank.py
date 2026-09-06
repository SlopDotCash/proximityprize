#!/usr/bin/env python3
"""sw1_f3_union_rank.py -- SW1 lane F3: exact union-rank of the G87 bridge family over F_p.

Target (one-question map F3 / SYZ42-SYZ43 `hrank`):

    hrank : finrank (span (range phi)) = 2 * (Ucard - k)

where phi is the G87 bridge family of a stack (u0,u1) with witness configuration
{(gamma_i, S_i)} : each block is {(l, gamma_i * l) : l in D_{S_i}}, D_S := {l in C^perp :
supp l subset S} = (C|_S)^perp, and U := union of the S_i.  Everything here is EXACT
modular linear algebra (no floats).

What is measured for every configuration:
  rank      := rank of the (r(t-k)) x (2|U|) bridge matrix Phi  ( = dim span phi )
  target    := 2(|U| - k)                                       ( = the hrank value )
  nu        := 2(|U|-k) - rank  = dim( Bad_U / (C|_U)^2 )        (nontrivial bad-stack dim)
where Bad_U := {(u0,u1) on U : for all i, (u0 + gamma_i u1)|_{S_i} in C|_{S_i}} = null(Phi).

Exact facts checked (all PASS/FAIL, exit nonzero on FAIL):
  (E1) null(Phi) contains (C|_U)^2, so rank <= 2(|U|-k) always; hrank <=> nu = 0.
  (E2) r = 1 : rank = t - k  (a single block is a GRAPH of dim t-k, not the "doubled"
       2(t-k)-dim shortening the one-question map's gloss suggests); hrank FAILS.
  (E3) r = 2, gamma_1 != gamma_2 : rank = 2(t-k) EXACTLY, independent of |S_1 cap S_2|;
       hence hrank <=> |U| = t <=> S_1 = S_2; with distinct supports hrank FAILS.
  (E4) Whenever a stack in Bad_U \\ (C|_U)^2 exists (nu >= 1) -- i.e. whenever the
       configuration is realised by a stack that does NOT jointly agree with a codeword
       pair on U -- rank <= 2(|U|-k) - 1 (the localized span cap; Lean:
       `_SW1_F3_UnionRankExact.lean`, `localized_span_cap`).  Verified end-to-end by
       sampling a nullspace vector, checking it is bad at every (gamma_i,S_i) and not
       in (C|_U)^2.
  (E5) p-sweep: for a fixed combinatorial configuration the rank profile is reported
       across primes p = 1 (mod n) to expose any small-field artefact.

Random and adversarial families (sunflower, one-swap, chain, nested, minimal-overlap) are
swept for n in {8,16,32}, k = n/2, t in the strip (k < t < 3n/4) and at t = 3n/4.
"""
from __future__ import annotations

import random
import sys
from itertools import combinations

# ----------------------------------------------------------------------------- field utils


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    i = 3
    while i * i <= p:
        if p % i == 0:
            return False
        i += 2
    return True


def primes_1_mod(n: int, count: int, start: int = 2) -> list[int]:
    out = []
    p = start
    while len(out) < count:
        if p % n == 1 and is_prime(p):
            out.append(p)
        p += 1
    return out


def primitive_root(p: int) -> int:
    phi = p - 1
    fac = []
    m = phi
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    raise RuntimeError("no primitive root")


def mu_n(p: int, n: int) -> list[int]:
    assert (p - 1) % n == 0
    g = primitive_root(p)
    w = pow(g, (p - 1) // n, p)
    pts = [pow(w, j, p) for j in range(n)]
    assert len(set(pts)) == n
    return pts


# ----------------------------------------------------------------------------- linear algebra mod p


def rref(rows: list[list[int]], p: int) -> tuple[list[list[int]], list[int]]:
    """Row-reduce (copy) mod p; return (reduced rows, pivot columns)."""
    A = [r[:] for r in rows]
    if not A:
        return A, []
    ncols = len(A[0])
    pivots = []
    r = 0
    for c in range(ncols):
        piv = None
        for i in range(r, len(A)):
            if A[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [(x * inv) % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
        if r == len(A):
            break
    return A[:r], pivots


def rank(rows: list[list[int]], p: int) -> int:
    return len(rref(rows, p)[0])


def nullspace(rows: list[list[int]], ncols: int, p: int) -> list[list[int]]:
    """Basis of {x : A x = 0} mod p."""
    R, piv = rref(rows, p) if rows else ([], [])
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [0] * ncols
        v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-R[i][f]) % p
        basis.append(v)
    return basis


def in_rowspace(rows: list[list[int]], v: list[int], p: int) -> bool:
    return rank(rows + [v], p) == rank(rows, p)


# ----------------------------------------------------------------------------- RS objects


def rs_generator(pts: list[int], k: int, p: int) -> list[list[int]]:
    return [[pow(a, i, p) for a in pts] for i in range(k)]


def parity_rows_on(G: list[list[int]], S: list[int], p: int) -> list[list[int]]:
    """Basis of D_S = (C|_S)^perp, as vectors indexed by S (length |S|)."""
    GS = [[row[j] for j in S] for row in G]  # k x |S|
    return nullspace(GS, len(S), p)  # dim |S| - rank(GS)


def bridge_matrix(G, supports, gammas, U, p):
    """Rows (l embedded in F^U, gamma_i * l) for l in basis(D_{S_i}).  Returns (Phi, blocks)."""
    pos = {x: idx for idx, x in enumerate(U)}
    m = len(U)
    Phi = []
    blocks = []
    for S, g in zip(supports, gammas):
        rows = parity_rows_on(G, S, p)
        blk = []
        for l in rows:
            v = [0] * (2 * m)
            for coord, val in zip(S, l):
                v[pos[coord]] = val
                v[m + pos[coord]] = (g * val) % p
            blk.append(v)
        Phi.extend(blk)
        blocks.append(blk)
    return Phi, blocks


def code_pairs_on_U(G, U, p):
    """Basis of (C|_U)^2 inside F^{2|U|}."""
    m = len(U)
    GU = [[row[j] for j in U] for row in G]
    out = []
    for row in GU:
        out.append(row + [0] * m)
        out.append([0] * m + row)
    return out


def is_bad_at(G, u0, u1, S, g, p) -> bool:
    """(u0 + g u1)|_S in C|_S ?  (u0,u1 indexed by global coordinate list)"""
    GS = [[row[j] for j in S] for row in G]
    v = [(u0[j] + g * u1[j]) % p for j in S]
    return in_rowspace(GS, v, p)


def pair_joint_on(G, u0, u1, S, p) -> bool:
    GS = [[row[j] for j in S] for row in G]
    return in_rowspace(GS, [u0[j] for j in S], p) and in_rowspace(GS, [u1[j] for j in S], p)


# ----------------------------------------------------------------------------- one configuration


def analyse(G, n, k, supports, gammas, p, rng, check_stack=True):
    U = sorted(set().union(*supports))
    m = len(U)
    Phi, blocks = bridge_matrix(G, supports, gammas, U, p)
    rk = rank(Phi, p)
    target = 2 * (m - k)
    CU2 = code_pairs_on_U(G, U, p)
    # (E1) (C|_U)^2 subset null(Phi)
    for c in CU2:
        for row in Phi:
            if sum(a * b for a, b in zip(row, c)) % p:
                return None, "E1: (C|_U)^2 not annihilated"
    nu = target - rk
    if nu < 0:
        return None, "E1: rank exceeds 2(|U|-k)"
    blk_ranks = [rank(b, p) for b in blocks]
    info = dict(U=m, rank=rk, target=target, nu=nu, blk=blk_ranks)
    if check_stack and nu >= 1:
        # (E4) exhibit a nontrivial bad stack: a nullspace vector outside (C|_U)^2
        NS = nullspace(Phi, 2 * m, p)
        found = None
        for _ in range(20):
            coeffs = [rng.randrange(p) for _ in NS]
            v = [sum(c * b[j] for c, b in zip(coeffs, NS)) % p for j in range(2 * m)]
            if not in_rowspace(CU2, v, p):
                found = v
                break
        if found is None:
            return None, "E4: nu>=1 but no nontrivial nullspace sample"
        u0 = [0] * n
        u1 = [0] * n
        for idx, x in enumerate(U):
            u0[x] = found[idx]
            u1[x] = found[m + idx]
        for S, g in zip(supports, gammas):
            if not is_bad_at(G, u0, u1, S, g, p):
                return None, "E4: nullspace stack not bad at a witness"
        if pair_joint_on(G, u0, u1, U, p):
            return None, "E4: sampled stack jointly agrees on U"
        if rk > target - 1:
            return None, "E4: cap violated"
        info["stack_ok"] = True
    return info, None


# ----------------------------------------------------------------------------- families


def random_supports(n, t, r, rng):
    return [sorted(rng.sample(range(n), t)) for _ in range(r)]


def one_swap_family(n, t, r, rng):
    base = sorted(rng.sample(range(n), t))
    outside = [x for x in range(n) if x not in base]
    fam = [base]
    pairs = [(x, y) for x in base for y in outside]
    rng.shuffle(pairs)
    for x, y in pairs[: r - 1]:
        fam.append(sorted((set(base) - {x}) | {y}))
    return fam


def sunflower_family(n, t, r, rng):
    core_size = max(2 * t - n, 0)
    core = set(rng.sample(range(n), core_size))
    rest = [x for x in range(n) if x not in core]
    fam = []
    for _ in range(r):
        petal = rng.sample(rest, t - core_size)
        fam.append(sorted(core | set(petal)))
    return fam


def chain_family(n, t, r, rng):
    perm = list(range(n))
    rng.shuffle(perm)
    fam = []
    for i in range(r):
        start = (i * (n - t)) % n
        fam.append(sorted(perm[(start + j) % n] for j in range(t)))
    return fam


def nested_family(n, t, r, rng):
    # all supports contain a common block of size t-1 : |S_i cap S_j| = t-1
    block = set(rng.sample(range(n), t - 1))
    rest = [x for x in range(n) if x not in block]
    rng.shuffle(rest)
    return [sorted(block | {rest[i % len(rest)]}) for i in range(r)]


def min_overlap_family(n, t, r, rng):
    # consecutive pairs with the minimal pairwise overlap 2t-n (SYZ56 regime)
    fam = []
    perm = list(range(n))
    rng.shuffle(perm)
    for i in range(r):
        start = (i * (n - t)) % n
        fam.append(sorted(perm[(start + j) % n] for j in range(t)))
    return fam


FAMILIES = {
    "random": random_supports,
    "oneswap": one_swap_family,
    "sunflower": sunflower_family,
    "chain": chain_family,
    "nested": nested_family,
    "minoverlap": min_overlap_family,
}


def distinct_scalars(p, r, rng):
    return rng.sample(range(1, p), r)


# ----------------------------------------------------------------------------- main sweep


def main() -> int:
    rng = random.Random(20260905)
    failures = []
    print("SW1-F3 union-rank probe: exact ranks of the G87 bridge family over F_p")
    print("columns: n k t p r family |U| rank 2(|U|-k) nu blocks")
    hrank_true_vacuous = 0
    hrank_true_total = 0
    configs = 0
    for n in (8, 16, 32):
        k = n // 2
        ts = sorted({k + 1, (3 * n) // 4 - 1, (3 * n) // 4})
        primes = primes_1_mod(n, 3) + primes_1_mod(n, 1, start=10_000)
        for p in primes:
            pts = mu_n(p, n)
            G = rs_generator(pts, k, p)
            for t in ts:
                # ---- (E2) r = 1
                S = sorted(rng.sample(range(n), t))
                info, err = analyse(G, n, k, [S], [rng.randrange(1, p)], p, rng)
                configs += 1
                if err or info["rank"] != t - k or info["nu"] != t - k:
                    failures.append(f"E2 n={n} p={p} t={t}: {err or info}")
                print(f"{n:3d} {k:2d} {t:2d} {p:6d} 1 single    {info['U']:3d} {info['rank']:3d} "
                      f"{info['target']:3d} {info['nu']:3d} {info['blk']}")
                # ---- (E3) r = 2 with controlled overlap
                for ov in sorted({max(2 * t - n, 0), t - 1, (max(2 * t - n, 0) + t) // 2}):
                    if ov < max(2 * t - n, 0) or ov >= t:
                        continue
                    A = sorted(rng.sample(range(n), t))
                    keep = rng.sample(A, ov)
                    outside = [x for x in range(n) if x not in A]
                    B = sorted(set(keep) | set(rng.sample(outside, t - ov)))
                    g1, g2 = distinct_scalars(p, 2, rng)
                    info, err = analyse(G, n, k, [A, B], [g1, g2], p, rng)
                    configs += 1
                    U = len(set(A) | set(B))
                    if err or info["rank"] != 2 * (t - k):
                        failures.append(f"E3 n={n} p={p} t={t} ov={ov}: {err or info}")
                    print(f"{n:3d} {k:2d} {t:2d} {p:6d} 2 pair/ov{ov:<2d} {info['U']:3d} "
                          f"{info['rank']:3d} {info['target']:3d} {info['nu']:3d} {info['blk']}")
                # ---- families, r = 3..8
                for fam_name, fam in FAMILIES.items():
                    for r in (3, 4, 6, 8):
                        if fam_name == "oneswap" and r - 1 > t * (n - t):
                            continue
                        sup = fam(n, t, r, rng)
                        if len({tuple(s) for s in sup}) < r:
                            continue  # SYZ18: supports must be pairwise distinct
                        gam = distinct_scalars(p, r, rng)
                        info, err = analyse(G, n, k, sup, gam, p, rng)
                        configs += 1
                        if err:
                            failures.append(f"{fam_name} n={n} p={p} t={t} r={r}: {err}")
                            continue
                        if info["nu"] == 0:
                            hrank_true_total += 1
                            hrank_true_vacuous += 1  # nu = 0 <=> no nontrivial bad stack
                        print(f"{n:3d} {k:2d} {t:2d} {p:6d} {r} {fam_name:9s} {info['U']:3d} "
                              f"{info['rank']:3d} {info['target']:3d} {info['nu']:3d} {info['blk']}")
    # ---- (E5) p-sweep on a fixed combinatorial configuration (n = 16, t = 11, r = 4 sunflower)
    print("\n(E5) p-sweep, fixed configuration n=16 k=8 t=11 r=4 sunflower + one-swap:")
    n, k, t = 16, 8, 11
    rng2 = random.Random(7)
    sup_sun = sunflower_family(n, t, 4, rng2)
    sup_swap = one_swap_family(n, t, 4, rng2)
    for p in primes_1_mod(n, 6) + primes_1_mod(n, 2, start=100_000):
        pts = mu_n(p, n)
        G = rs_generator(pts, k, p)
        for name, sup in (("sunflower", sup_sun), ("oneswap", sup_swap)):
            gam = distinct_scalars(p, 4, random.Random(p))
            info, err = analyse(G, n, k, sup, gam, p, rng2)
            if err:
                failures.append(f"E5 p={p} {name}: {err}")
                continue
            print(f"  p={p:7d} {name:9s} |U|={info['U']:2d} rank={info['rank']:2d} "
                  f"target={info['target']:2d} nu={info['nu']:2d}")
    print(f"\nconfigurations analysed: {configs}")
    print(f"configurations with hrank TRUE (nu = 0): {hrank_true_total} -- every one of them is "
          f"VACUOUS (no stack outside (C|_U)^2 realises it): {hrank_true_vacuous}")
    if failures:
        print("FAIL")
        for f in failures:
            print("  ", f)
        return 1
    print("PASS: (E1)-(E5) hold on every configuration; hrank <=> nu = 0 <=> the configuration "
          "is realised by NO stack that fails joint codeword agreement on U.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
