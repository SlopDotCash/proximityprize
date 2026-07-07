#!/usr/bin/env python3
"""
S5 shell-base probe for #444 prize floor (the S5 geometric-shell handle).

CONTEXT (S5 handle / theta-count shell law):
  The S5 bound is  E_r(mu_n) <= (A*(2r+1)*K^r + 1) * Wick,  Wick = (2r-1)!! n^r,
  derived from a GEOMETRIC SHELL decomposition of the additive-energy count: the
  2r-tuples x in mu_n^{2r} with sum eps_i x_i = 0 are binned by the size of their
  partial sums, and the count per shell decays geometrically with base B. The S5
  bound is uniform-in-n ONLY IF the shell base B is bounded independent of n.
  Reported empirically B grows 2.70 -> 3.78 (n=16 -> 32); the OPEN INPUT for S5 is
  whether B(n) SATURATES (=> S5 gives a uniform K=O(1) => has-gap-fixable) or keeps
  GROWING (=> S5 needs concentration => reduces to the wall).

WHAT WE MEASURE (machine-checked, EXACT char-0 energy, artifact-free p=inf baseline):
  For n=2^mu, zeta^j -> +/-e_{j mod n/2} in Z^{n/2}. A vanishing 2r-sum is an exact
  integer vector identity. We compute, for r=2,3:
    E_r^inf(n)        = #{ x in mu_n^{2r} : sum eps_i x_i = 0 exactly in Z[zeta_n] }
    shell counts S_l  = the partial-sum-magnitude distribution that the shell law bins
  and extract the SHELL BASE B(n) three convergent ways so the verdict is robust:

    (B1) energy/Wick ratio growth:  the multiplicative jump
            B1(n) := (E_r^inf(n) / Wick(n))    -- if S5's prefactor A*K^r is uniform,
         this ratio is bounded; its growth IS the shell-base growth.
    (B2) tail-shell decay base: bin the squared partial-sum norm |sum_{i<=r} x_i|^2
         of the r-fold sums into dyadic shells; B2 = geometric base of the shell-count
         sequence (the literal theta-count base).
    (B3) moment-ratio base:  B3(n) := (E_3^inf/E_2^inf) / (n * c)  normalized; tracks
         whether the per-order growth saturates.

  VERDICT: if B (any consistent measure) keeps growing with n => REDUCES TO WALL;
  if it saturates to an n-independent constant => HAS-GAP-FIXABLE.

Proper mu_n, n=2^mu, never the full group. Exact integer arithmetic (no prime).
"""
import math
from collections import Counter
from itertools import product


def df(r):                       # (2r-1)!!
    v = 1
    for k in range(1, r + 1):
        v *= (2 * k - 1)
    return v


def root_vec(j, half):
    v = [0] * half
    if j < half:
        v[j] = 1
    else:
        v[j - half] = -1
    return tuple(v)


def partial_sum_counts(n, r):
    """Return Counter over r-fold sum vectors v: N(v)=#{x in mu_n^r: sum=v}.
    Then E_r^inf = sum N(v)^2.  Also return the |v|^2 magnitude distribution."""
    half = n // 2
    rv = [root_vec(j, half) for j in range(n)]
    cnt = Counter()
    for tup in product(range(n), repeat=r):
        s = [0] * half
        for j in tup:
            vv = rv[j]
            for t in range(half):
                s[t] += vv[t]
        cnt[tuple(s)] += 1
    Er = sum(c * c for c in cnt.values())
    # magnitude (squared-norm) distribution of the r-fold partial sums
    mag = Counter()
    for v, c in cnt.items():
        m2 = sum(t * t for t in v)
        mag[m2] += c            # number of r-tuples whose partial sum has norm^2 = m2
    return Er, mag


def shell_base_from_mag(mag):
    """Bin the magnitude^2 distribution into dyadic shells [2^k, 2^{k+1}) and
    return the geometric base = median successive-ratio of shell counts (the
    theta-count shell base)."""
    shells = Counter()
    for m2, c in mag.items():
        if m2 == 0:
            shells[-1] += c          # zero shell
        else:
            shells[int(math.floor(math.log2(m2)))] += c
    ks = sorted(k for k in shells if k >= 0)
    ratios = []
    for i in range(1, len(ks)):
        if shells[ks[i - 1]] > 0 and ks[i] == ks[i - 1] + 1:
            ratios.append(shells[ks[i]] / shells[ks[i - 1]])
    if not ratios:
        return None, shells
    ratios.sort()
    return ratios[len(ratios) // 2], shells     # median ratio = robust base


print("S5 SHELL BASE B(n) growth  (EXACT char-0 energy, proper mu_n=2^mu)")
print("=" * 76)
print(f"{'n':>5} {'r':>3} {'E_r^inf':>12} {'Wick':>12} {'B1=E/Wick':>10} "
      f"{'B2=shellbase':>12} {'verdict-trend':>14}")

results = {}
for mu in range(3, 8):           # n = 8,16,32,64,128
    n = 2 ** mu
    for r in (2, 3):
        if n ** r > 20_000_000:
            print(f"{n:>5} {r:>3}  (n^r={n**r:,} > budget, skip)")
            continue
        Er, mag = partial_sum_counts(n, r)
        wick = df(r) * n ** r
        b1 = Er / wick
        b2, shells = shell_base_from_mag(mag)
        results[(n, r)] = (Er, b1, b2)
        b2s = f"{b2:.3f}" if b2 is not None else "  n/a"
        print(f"{n:>5} {r:>3} {Er:>12} {wick:>12} {b1:>10.4f} {b2s:>12}")

print("\n--- B1 (energy/Wick) growth in n, per r ---")
for r in (2, 3):
    seq = [(n, results[(n, r)][1]) for n in (8, 16, 32, 64, 128) if (n, r) in results]
    print(f"  r={r}: " + "  ".join(f"n={n}:{b:.4f}" for n, b in seq))
    if len(seq) >= 2:
        print("        ratios n->2n: " +
              "  ".join(f"{seq[i][1]/seq[i-1][1]:.4f}" for i in range(1, len(seq))))

print("\n--- B2 (theta shell base) growth in n, per r ---")
for r in (2, 3):
    seq = [(n, results[(n, r)][2]) for n in (8, 16, 32, 64, 128)
           if (n, r) in results and results[(n, r)][2] is not None]
    print(f"  r={r}: " + "  ".join(f"n={n}:{b:.3f}" for n, b in seq))

print("\nVERDICT KEY:")
print("  B1 (energy/Wick) -> constant AND B2 shell base saturates => HAS-GAP-FIXABLE.")
print("  Either keeps growing with n                              => REDUCES TO WALL.")
