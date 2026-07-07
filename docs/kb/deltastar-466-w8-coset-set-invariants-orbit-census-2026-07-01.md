# #466 lane W8 — coset-SET invariants LIVE (W1/quarter-arc predicts |η_b|) + width-4 orbit census: K = n/4 − 1, Θ(n), NOT the D* law (2026-07-01)

Two deliverables, both decided by probe. No Lean claims are made in this note.

## Task A — the coset-set invariant classification: **LIVE (language found)**

Probe: `scripts/probes/probe_466_coset_invariants.py` →
`scripts/probes/_out_466_coset_invariants.txt`.

Setup: round-1 P1 (`466-r1-antiresonance-bblind`) killed every RESIDUE statistic of the worst
frequency b\*: |η_b| depends only on the coset C_b = b·μ_n **as a set**, and dilation washes out
residue classes. The open follow-up was whether any **arc-concentration set-functional** of C_b/p
on the circle predicts |η_b| / localizes the argmax. Battery: dyadic best-arc discrepancy,
Wasserstein-1 to uniform, pair-correlation Σ1/‖d‖, L2 triangular-kernel arc energy, Dirichlet
correlations (raw = contaminated, deflated = multiplicative-neighbor only), min-gap, gap-variance.
Regime: n ∈ {16, 32}, 2 generic primes each at β = 4 (p = 65617, 65633, 1048609, 1048897), all m
cosets per run (4101…32778); GF prime 65537 run separately and flagged; Parseval check exact.

**Verdict: LIVE.** Four functionals pass the pre-registered gate (|Spearman| ≥ 0.5 in ALL generic
runs AND argmax coset at percentile ≥ 0.99 in ≥ 3/4 of runs) — in fact pct(j\*) ≈ 1.000 in **all
4/4** runs for each:

| functional | Spearman range (4 generic runs) | pct(j\*) | worst localize |
|---|---|---|---|
| `w1_unif` (Wasserstein-1 to uniform) | 0.858 – 0.864 | 1.000 all runs | 0.0002 |
| `l2arc_2^-2` (quarter-arc L2 energy) | 0.767 – 0.774 | 1.000 all runs | 0.0005 |
| `disc_2^-2` (best quarter-arc excess) | 0.674 – 0.681 | 0.999 – 1.000 | 0.0012 |
| `l2arc_2^-3` (eighth-arc L2 energy) | 0.526 – 0.529 | 0.999 – 1.000 | 0.0015 |

Structural readings (stable across all runs, GF run included):

1. **The signal is COARSE.** Correlation is monotone decreasing in scale: quarter-circle arcs
   carry it (0.67–0.77), scale 2^-6…2^-7 is dead (≤ 0.17). The sup coset is the one that piles
   mass into a quarter-arc — |η_b| is a low-frequency imbalance phenomenon, matching M ≈ C·√(n log(p/n))
   with the extremal contribution concentrated at the coarsest harmonic.
2. **Multiplicative-neighbor information is useless.** The deflated Dirichlet functionals
   `dirdef_K` = 2Σ_{2≤k≤K} η_{kb} (pure information about η at multiplicative neighbors kb) have
   |Spearman| ≤ 0.14 and localization as bad as 1.0. |η_b| is invisible from the η-values of the
   coset's multiplicative translates — extends P1's b-blindness to the frequency side.
3. **Honesty caveat on `w1_unif`:** W1-to-uniform is soft-contaminated — H(t) = F(t) − t has
   Fourier coefficients η_{kb}/(2πik), so its k = 1 term is |η_b|/2π itself; its high rank
   correlation is partially tautological (it says the k = 1 term dominates the transport
   distance, itself a finding, but not an independent predictor). The **clean language finding
   is `disc_2^-2` / `l2arc_2^-2`**: transcendental-free (integer/rational arithmetic only,
   certificate-checkable) purely geometric functionals with 0.67–0.77 rank correlation and
   perfect argmax pinning.
4. **Localization is real but not a cost saving.** Searching cosets in decreasing `w1`/`l2arc_2^-2`
   order finds the true argmax within the first ≤ 0.05–0.12 % of the m cosets in every run
   (`localize` ≤ 0.0012). Per-coset cost is, however, ≥ O(n), same order as computing η_b
   directly — the value is the **alphabet** (any future dichotomy over coset-sets should be
   stated in coarse-arc-concentration terms, where the extremizer is provably extreme), not a
   sub-linear certificate search. `gap_var` (the doorIV statistic) also pins the argmax
   (pct = 1.000, 4/4) but with weaker correlation 0.28–0.41 — consistent with its known
   asymptotic Poisson decay.
5. GF prime 65537 (flagged, excluded from the verdict): same ordering, correlations mildly
   inflated at fine scales (e.g. `disc_2^-5` 0.32 vs 0.18–0.20 generic) — the generalized-Fermat
   structure adds fine-scale rigidity; pooling it would have overstated fine-scale functionals.

Status vs P1: P1's kill said "residues of b don't classify"; W8/A now says the coset-SET language
**does** — the correct invariant family is coarse arc concentration (quarter-arc discrepancy /
L2 arc energy), and the extremal coset is its near-extremizer. Any future dichotomy attempt
should target: "every coset with quarter-arc excess below τ has |η_b| ≤ …" (the contrapositive
direction is what the numbers support).

## Task B — e2BadScalarSet width-4 full G-orbit census: **K(n) = n/4 − 1 exactly (one exception), Θ(n), NOT the D\*-law analogue**

Probe: `scripts/probes/probe_466_e2w4_orbit_census.py` →
`scripts/probes/_out_466_e2w4_orbit_census.txt`. Object: the Lean
`E2DilationDirectCount.e2BadScalarSet` at width 4 — {−1/e₁(S) : S ∈ C(μ_n,4), e₂(S) = 0,
e₁(S) ≠ 0} — counted in full G-orbits (label = e₁^n since μ_n is the full n-torsion). n = 8…64
step 4, 2 generic primes each (p ≥ n⁴, p ≡ 1 mod n, GF/2-power-m flagged), char-0 ground truth by
exact integer reduction mod Φ_n; every row cross-prime AGREE + char-0 MATCH; free action
(#scalars = K·n, the `E2W4CyclotomicNonCollision` shape) verified at every row.

**Census law:** K(n) = n/4 − 1 **exactly** for all tested n except n = 60, where K = 16 =
(n/4 − 1) + 2. So:

- The census is **Θ(n)** (log-log slope 1.19 top-half; 1.27 all-n), matching the product-family
  model `Kmodel = n/4 − 1` of `E2W4CyclotomicNonCollision` Part 2 with ratio exactly 1.000 at 14
  of 15 rows — and **decisively NOT** the `_DstarGrowthLaw` moment-variety analogue (Θ(n^{r−1}) =
  Θ(n³) would need slope ≈ 3; even Θ(n²) is excluded). The width-4 e₂ = 0 locus in μ_n is
  1-parameter (product quads {x, −x, xt, x/t}), not a full-dimensional moment variety; the
  super-budget D\* growth at r = 3 does NOT come from this object. The `_OPSingleOrbit` model
  n/8 − 1 is refuted as the census count (off by ×2 + 1).
- **The n = 60 exception is Lam–Leung mixed {3,5}.** Both extra (non-product) orbits are stable
  across both primes, representatives (exponents mod 60): (0, 2, 14, 36) and (0, 2, 26, 48)
  (substantiated in the ADDENDUM section of the output artifact: printed per-prime with exact
  char-0 per-rep verification e2 ≡ 0 mod Φ₆₀, e1 ≠ 0; independently cross-checked via sympy;
  neither rep contains an antipodal pair, so neither is of product form).
  Hand-check for (0, 2, 14, 36): e₂/ζ² = 1 + ζ¹² + ζ¹⁴ + ζ³⁴ + ζ³⁶ + ζ⁴⁸ =
  (−ζ²⁴ from the σ₅ relation) + (−ζ⁵⁴ from the σ₃ relation) = −ζ²⁴(1 + ζ³⁰) = 0 — a weight-6
  vanishing sum genuinely using BOTH a 5-cycle and a 3-cycle, hence requiring 15 | n. n = 60 is
  the only 15 | n in range; predict extras again at n = 120, 180, … and K = n/4 − 1 exact
  whenever 15 ∤ n (conjecture, labeled as such).
- Side census: #bad SUBSETS = #bad scalars except when 3 | n, where e₁ collides across distinct
  bad subsets (3+3 Lam–Leung e₂-decompositions; e.g. n = 48: 1200 subsets → 528 scalars); the
  orbit count is unaffected (K still = n/4 − 1 at every 3 | n row except 60).

Consequence for the ledger: the width-4 bad-scalar orbit story is CLOSED as a growth question —
bounded? No. Polynomial matching D\*? No. It is the linear product law, plus a sparse 15 | n
Lam–Leung correction; the two-orbit refuters of `E2W4CyclotomicNonCollision` were already, up to
the 15 | n correction, the whole picture. A Lean-landable target this suggests (not attempted
here): `K(n) = n/4 − 1` for 15 ∤ n via the product-family non-collision theorems already in-tree
plus a "no non-product vanishing" cyclotomic lemma (Lam–Leung weight-6 classification).

## Artifacts

- `scripts/probes/probe_466_coset_invariants.py` + `_out_466_coset_invariants.txt` (Task A)
- `scripts/probes/probe_466_e2w4_orbit_census.py` + `_out_466_e2w4_orbit_census.txt` (Task B)
