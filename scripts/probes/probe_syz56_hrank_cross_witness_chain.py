#!/usr/bin/env python3
"""
SYZ56 probe — the `hrank` residual via cross-witness chaining.

Context (#466). SYZ43 pinned the strip's realizability obligation to one scalar equality:
    hrank : finrank (span (range φ)) = 2 (Ucard - k)          (G87 bridge functionals φ)
SYZ22 proved each per-witness block is a FULL basis of its S-anchored punctured dual, so
`hrank` = union-generation over the mcaEvent witness-support family {S_i}, |S_i| >= t.

Proposed discharge (verify here):
  (a) cross-witness algebra: on S_i ∩ S_j (distinct scalars) u1 agrees with ONE codeword.
  (b) chaining: a large (over-budget) witness family glues these regions into one of size
      >= k, forcing u1 near a codeword (merged/degenerate branch) => hrank discharges.

VERDICT (this probe): (a) TRUE, (b) NO-GO in the strip.
  The forced single-codeword agreement regions are the pairwise overlaps |S_i ∩ S_j| >= 2t-n.
  Fusing pairwise codewords c_ij, c_il into ONE (so u1 agrees with a single codeword on a
  bigger region) needs them equal => needs them to agree on >= k points => an m-fold
  intersection of size >= k. The minimal m-fold overlap is  m*t-(m-1)*n = n - m(n-t),
  which is DECREASING in m: the largest guaranteed region is the pairwise one (m=2).
  In the rate-1/2 strip (k=n/2, t<3n/4  <=>  2t<n+k) that pairwise region is already < k,
  and every deeper merge only shrinks. So no chain ever certifies a size->=k region:
  u1 is NEVER forced near a codeword by cross-witness chaining.  hrank does not discharge.
  The band obstruction blocking the strip at scale t reappears at the witness-overlap scale.

Random families DO exhibit large overlaps (average pairwise ~ t^2/n ~ k near t=3n/4), but the
hrank obligation is over an ADVERSARIAL/existential configuration, so the worst case governs.
"""
import itertools, random


def thresholds(n):
    k = n // 2
    print(f"n={n}, k={k}, strip t<{3*n//4} (=3n/4)")
    for m in range(2, 9):
        tmin = n * (1 - 1 / (2 * m))
        print(f"  {m}-fold overlap >= k needs t >= {tmin:.2f}  (in strip? {tmin < 3*n/4})")


def sim_average(n, t, r, trials=4000):
    """Empirical: largest pairwise overlap in random t-subset families (average-case only)."""
    k = n // 2
    best = 0
    for _ in range(trials):
        S = [set(random.sample(range(n), t)) for _ in range(r)]
        for i, j in itertools.combinations(range(r), 2):
            best = max(best, len(S[i] & S[j]))
    print(f"    n={n} t={t} r={r}: max pairwise overlap = {best} (k={k}); >=k? {best>=k}"
          f"  [average-case, NOT the adversarial bound]")


if __name__ == "__main__":
    for n in (32, 64, 128):
        thresholds(n)
    print("Worst-case forced region = pairwise 2t-n < k throughout the strip => chain NO-GO.")
    print("Average-case random overlaps (informational only):")
    sim_average(32, 23, 20)
    sim_average(64, 47, 60)
