#!/usr/bin/env python3
"""probe_w15_window_rational_linear_refute.py — thread res:window-rational-linear (#334/#466)

FABRICATE-THEN-REFUTE probe for the named residual `WindowRationalLinear`
(ArkLib/Data/CodingTheory/ProximityGap/WBPencilLinearBudget.lean):

  WindowRationalLinear dom k w δ :=
    ∀ u₀ u₁, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
      #{γ : F | mcaEvent (rsCode dom k) δ u₀ u₁ γ} ≤ n

The Prop carries NO below-UDR guard (2w + k ≤ n), while its consumers
(`epsMCA_le_below_udr_linear`, `le_mcaDeltaStar_below_udr_linear`) only require
  1 ≤ k, w + k ≤ n, w + 3 ≤ n, δ ≤ 1, δ·n ≤ w.
This probe certifies an explicit countermodel INSIDE that consumer range but ABOVE
the unique-decoding radius:

  F = F₃₁, n = 10, k = 1, w = 7, δ = 7/10  (2w+k = 15 > 10 = n),
  #bad ≥ 12 > 10 = n.

Geometry (k = 1, codewords = constants): a scalar γ is mca-bad iff some value class
of the line u₀ + γ·u₁ has ≥ (1-δ)·n = 3 indices on which u₁ is non-constant, i.e.
iff the point multiset P_i = (u₁ᵢ, u₀ᵢ) ∈ F² has a ≥3-rich line of slope −γ with ≥ 2
distinct abscissae.  Two double points ("fat points") P0, P1 plus steered singles
produce 12 distinct such directions on 10 indices.

WBSolvable is certified explicitly: each row takes one value on ≥ 3 indices, hence
agrees with a constant polynomial (deg < k = 1) off an error set of size 7 = w
(`wbSolvable_of_close`).

The script verifies EVERYTHING faithfully against the Lean semantics:
  * exact mcaEvent (all witness sets S via the value-class characterization,
    joint clause ⟺ u₁ constant on S given S inside one class),
  * the NNReal threshold (1 - 7/10)*10 = 3,
  * WB certificates for both rows,
  * distinctness of the 12 γ's,
and prints the Lean-ready data.  Exits nonzero on any failure.
"""

from itertools import combinations

P = 31
N = 10
K = 1
W = 7
T = N - W  # = 3 = ceil((1-delta)*n) with delta = w/n = 7/10

# point config: index -> (x, y) = (u1_i, u0_i)
pts = [
    (0, 0), (0, 0),      # i0,i1 : fat point P0 (double)
    (1, 5), (1, 5),      # i2,i3 : fat point P1 (double)
    (2, 0),              # i4 : s1, horizontal with P0 (y = 0)  -> u0 value 0 thrice
    (1, 9),              # i5 : s2, vertical with P1 (x = 1)    -> u1 value 1 thrice
    (3, 1),              # i6 : s3
    (4, 7),              # i7 : s4
    (5, 3),              # i8 : s5
    (6, 12),             # i9 : s6
]
u1 = [x for (x, y) in pts]
u0 = [y for (x, y) in pts]

dom = list(range(N))  # dom i = i in F31 (irrelevant for k = 1, needed for WB checks)


def is_bad(gamma):
    """Faithful mcaEvent check for k = 1 (rsCode dom 1 = constant words).

    mcaEvent C delta u0 u1 gamma iff exists S, |S| >= T, exists codeword (constant c)
    with u0 + gamma*u1 = c on S, and NOT (exists constants v0,v1 agreeing with u0,u1
    on S).  Since any witness S sits inside one value class of the line, and joint
    agreement on S <=> u0 const on S AND u1 const on S <=> u1 const on S (u0 = c -
    gamma*u1 there), gamma is bad iff some value class has >= T indices and >= 2
    distinct u1-values.  Returns (bool, witness) with witness = (S, c, i, j)."""
    classes = {}
    for i in range(N):
        c = (u0[i] + gamma * u1[i]) % P
        classes.setdefault(c, []).append(i)
    for c, idxs in classes.items():
        if len(idxs) >= T:
            xs = sorted(set(u1[i] for i in idxs))
            if len(xs) >= 2:
                # pick a size-T witness containing two distinct abscissae
                i = next(i for i in idxs if u1[i] == xs[0])
                j = next(jj for jj in idxs if u1[jj] == xs[1])
                rest = [r for r in idxs if r not in (i, j)]
                S = sorted([i, j] + rest[: T - 2])
                return True, (S, c, i, j)
    return False, None


def brute_mcaEvent(gamma):
    """Second, fully brute-force implementation: enumerate ALL subsets S of size >= T,
    all constants c (line codeword), and the joint clause over all constant pairs."""
    for size in range(T, N + 1):
        for S in combinations(range(N), size):
            # line = codeword on S?
            vals = {(u0[i] + gamma * u1[i]) % P for i in S}
            if len(vals) != 1:
                continue
            # joint pair on S?  v0,v1 constants agreeing with u0,u1 on S
            joint = len({u0[i] for i in S}) == 1 and len({u1[i] for i in S}) == 1
            if not joint:
                return True
    return False


def wb_certificate(u, name):
    """Find a value taken >= T times: constant agreement certificate for
    WBSolvable dom 1 7 u via wbSolvable_of_close (error set size n - T = w)."""
    from collections import Counter
    cnt = Counter(u)
    val, m = cnt.most_common(1)[0]
    assert m >= T, f"{name}: no value repeated {T} times (max {m})"
    agree = [i for i in range(N) if u[i] == val]
    E = [i for i in range(N) if u[i] != val]
    assert len(E) <= W
    print(f"  WBSolvable {name}: constant {val}, agree indices {agree}, error set E = {E} (|E| = {len(E)} <= w = {W})")
    return val, E


def main():
    ok = True
    print(f"p = {P}, n = {N}, k = {K}, w = {W}, delta = {W}/{N}, witness threshold T = {T}")
    print(f"consumer range check: 1 <= k: {1 <= K}; w+k <= n: {W+K <= N}; w+3 <= n: {W+3 <= N}; delta <= 1: True; delta*n <= w: {W <= W}")
    print(f"UDR check: 2w+k = {2*W+K} vs n = {N}  -> {'ABOVE UDR' if 2*W+K > N else 'below UDR'}")
    # NNReal threshold: (1 - 7/10) * 10 = 3 exactly (exact rational arithmetic)
    from fractions import Fraction
    assert (1 - Fraction(W, N)) * N == T

    print("\nWB certificates (explicit, for wbSolvable_of_close):")
    wb_certificate(u0, "u0")
    wb_certificate(u1, "u1")

    print("\nbad-scalar census (faithful class characterization + independent brute force):")
    bad = []
    for gamma in range(P):
        b1, wit = is_bad(gamma)
        b2 = brute_mcaEvent(gamma)
        if b1 != b2:
            print(f"  MISMATCH at gamma = {gamma}: class-method {b1}, brute {b2}")
            ok = False
        if b1:
            S, c, i, j = wit
            bad.append((gamma, S, c, i, j))
    print(f"  #bad = {len(bad)}  (need > n = {N}: {'YES — COUNTERMODEL' if len(bad) > N else 'no'})")
    for gamma, S, c, i, j in bad:
        print(f"    gamma = {gamma:2d}: S = {S}, line value c = {c}, u1-nonconst witnesses (i,j) = ({i},{j}) with u1 = ({u1[i]},{u1[j]})")

    assert len(bad) > N, "not a countermodel"
    assert len({g for g, *_ in bad}) == len(bad)

    print("\nLean-ready data:")
    print(f"  u0 := ![{', '.join(str(v) for v in u0)}]")
    print(f"  u1 := ![{', '.join(str(v) for v in u1)}]")
    print(f"  bad gammas ({len(bad)}): {sorted(g for g, *_ in bad)}")
    print("\nRESULT:", "COUNTERMODEL VERIFIED" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
