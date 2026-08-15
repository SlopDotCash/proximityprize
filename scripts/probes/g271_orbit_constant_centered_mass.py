#!/usr/bin/env python3
# G271: the centered coordinate mass P(x) is constant on multiplicative quotient orbits.
#
# Companion probe for
#   ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G271OrbitConstantCenteredMass.lean
#
# Self-contained, exact integer arithmetic only (no numpy, no floats, no FFT).
#
# Mathematical claim being certified (Fable G270 H_const, upgraded from discarded G269 split):
#   Let G <= F_p^* be the n-element 2-power subgroup, W (the weighted-relation profile) and R
#   (a field-derived adjacent-rank row) both G-invariant: f(g*x) = f(x) for g in G.  Set
#       SW = sum_x W(x),  SR = sum_x R(x),
#       P(x) = (p*W(x) - SW)*(p*R(x) - SR).
#   Then:
#     (a) P is constant on every G-coset of F_p^* (orbit constancy);
#     (b) sum_x P(x) = p*(p*sum_x W(x)R(x) - SW*SR) = p*A_r  (the G269 identity, factor p);
#     (c) hence sum_{x in F_p} P(x) = P(0) + sum over m=(p-1)/n orbit masses, each = n*P(rep).
#
# This probe builds genuine G-invariant profiles on F_p (indexed 0..p-1, with x=0 the additive
# zero coordinate) and asserts (a),(b),(c) exactly.  It hard-exits(1) on any drift so it cannot
# silently pass vacuously.
#
# NOTE: this certifies the STRUCTURE lemma (orbit constancy + sum identity), which is what the
# Lean file proves axiom-clean.  It is NOT a sponsor covariance bound and NOT prize closure.

import sys

def subgroup_2power(p, n):
    """Return the n-element 2-power multiplicative subgroup of F_p^* if it exists, else None."""
    if (p - 1) % n != 0:
        return None
    # a generator g of F_p^*; then G = <g^((p-1)/n)> has order n.
    g = primitive_root(p)
    if g is None:
        return None
    h = pow(g, (p - 1) // n, p)  # element of order n
    G = set()
    v = 1
    for _ in range(n):
        G.add(v)
        v = (v * h) % p
    if len(G) != n:
        return None
    # n must be a power of two for the "2-power subgroup" reading; assert it.
    if n & (n - 1) != 0:
        return None
    return G, g

def primitive_root(p):
    if p == 2:
        return 1
    # factor p-1
    phi = p - 1
    fac = set()
    m = phi
    d = 2
    while d * d <= m:
        while m % d == 0:
            fac.add(d); m //= d
        d += 1
    if m > 1:
        fac.add(m)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in fac):
            return g
    return None

def make_invariant_profile(p, G, seed):
    """Deterministic G-invariant integer profile on F_p (0..p-1).

    Value is constant on each multiplicative G-coset of F_p^*, plus an independent value at 0.
    """
    val = [0] * p
    # assign x=0 its own value
    val[0] = (seed * 7 + 3) % 11
    seen = [False] * p
    seen[0] = True
    label = 1
    for x in range(1, p):
        if seen[x]:
            continue
        coset_val = (seed * label * 13 + label * label + 5) % 17
        # fill the whole coset x*G
        for gg in G:
            y = (x * gg) % p
            val[y] = coset_val
            seen[y] = True
        label += 1
    return val

def check_cell(p, n, seed_w, seed_r):
    res = subgroup_2power(p, n)
    if res is None:
        return None
    G, g = res
    W = make_invariant_profile(p, G, seed_w)
    R = make_invariant_profile(p, G, seed_r)

    # sanity: profiles are genuinely G-invariant
    for x in range(p):
        for gg in G:
            if W[(gg * x) % p] != W[x] or R[(gg * x) % p] != R[x]:
                print(f"FAIL: profile not G-invariant at p={p}, x={x}")
                sys.exit(1)

    SW = sum(W)
    SR = sum(R)
    P = [(p * W[x] - SW) * (p * R[x] - SR) for x in range(p)]

    # (a) orbit constancy: P constant on each G-coset
    for x in range(1, p):
        for gg in G:
            if P[(gg * x) % p] != P[x]:
                print(f"FAIL (a): P not orbit-constant at p={p}, x={x}")
                sys.exit(1)

    # (b) sum identity: sum P = p*(p*sum W*R - SW*SR)
    sumP = sum(P)
    sumWR = sum(W[x] * R[x] for x in range(p))
    A = p * sumWR - SW * SR          # centered covariance A_r
    if sumP != p * A:
        print(f"FAIL (b): sum P = {sumP} != p*A = {p*A} at p={p}")
        sys.exit(1)

    # (c) orbit decomposition: P0 + sum over orbits of n*P(rep) = sum P
    m = (p - 1) // n
    # orbit representatives: g^j, j=0..m-1 give distinct cosets of G in F_p^*
    # (g^j and g^k are in the same G-coset iff j==k mod m, since G = <g^m>).
    reps = []
    covered = {0}
    orbit_sum = P[0]
    r = 1
    for _j in range(m):
        reps.append(r)
        orbit_sum += n * P[r]
        for gg in G:
            covered.add((r * gg) % p)
        r = (r * g) % p
    if len(covered) != p:
        print(f"FAIL (c): orbit reps do not cover F_p at p={p} ({len(covered)}/{p})")
        sys.exit(1)
    if orbit_sum != sumP:
        print(f"FAIL (c): orbit-summed {orbit_sum} != sum P {sumP} at p={p}")
        sys.exit(1)

    return (p, n, m, A, sumP)

def main():
    n = 16  # a 2-power subgroup order
    # real characteristic-p cells with (p-1) divisible by n=16
    cells = [(97, 16), (113, 16), (193, 16), (257, 16), (433, 16), (577, 16),
             (641, 16), (769, 16), (929, 16), (1153, 16)]
    tested = 0
    for (p, nn) in cells:
        for (sw, sr) in [(1, 2), (3, 5), (7, 4)]:
            out = check_cell(p, nn, sw, sr)
            if out is None:
                print(f"FAIL: n={nn} is not a valid 2-power subgroup order mod p={p}")
                sys.exit(1)
            tested += 1
    if tested == 0:
        print("FAIL: no cells tested (vacuous)")
        sys.exit(1)
    # explicit non-trivial witness: confirm P is genuinely non-constant across orbits
    # (so orbit-constancy is not the trivial constant-profile case)
    p, nn = 257, 16
    G, g = subgroup_2power(p, nn)
    W = make_invariant_profile(p, G, 3)
    R = make_invariant_profile(p, G, 5)
    SW, SR = sum(W), sum(R)
    P = [(p * W[x] - SW) * (p * R[x] - SR) for x in range(p)]
    reps, r = [], 1
    for _ in range((p - 1) // nn):
        reps.append(r); r = (r * g) % p
    orbit_vals = sorted(set(P[rep] for rep in reps))
    if len(orbit_vals) < 3:
        print(f"FAIL: witness profile too degenerate ({len(orbit_vals)} distinct orbit masses)")
        sys.exit(1)
    print(f"G271 orbit-constancy probe PASS: {tested} exact cells, "
          f"orbit constancy (a), sum identity (b) sum P = p*A, orbit decomposition (c) all hold.")
    print(f"  witness p=257,n=16: m={(p-1)//nn} orbits, {len(orbit_vals)} distinct non-constant "
          f"orbit masses (structure is genuinely inter-orbit, not a constant profile).")

if __name__ == "__main__":
    main()
