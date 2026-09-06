# Dyadic phase-chaining candidate for delta-star, 2026-06-13

This note supersedes the finite factorial-moment gate as the *main* candidate
route under the stricter requirement that the answer not merely be equivalent to
explicit smooth-RS beyond-Johnson list decoding.

## Trigger

Latest issue evidence:

- #407 is now the active proximity-prize issue.  It explicitly marks #389 and
  #371 as archival and says the live frontier is the `L^infty` phase-alignment
  face for incomplete character sums over proper dyadic subgroups.
- New #407 comment `4700195129` refines the live target to a one-level
  square-descent inequality.  With
  `M(n) = max_b |sum_{x in mu_n} exp(2*pi*i*b*x/p)|`, the probe-supported local
  law is `M(2n)^2 <= 2 * M(n)^2 * (1 + drift_n)`.  The observed worst frequency
  has exactly aligned half-sums, but the two child magnitudes are submaximal; the
  proof target is therefore the submaximality/square-descent, not phase
  cancellation between halves.
- #389 reports worst-frequency probes for
  `S_b = sum_{x in mu_n} exp(2*pi*i*b*x/p)` up to `n=256`, with
  `|S_b| / sqrt(n log(p/n))` staying in the narrow range `1.14..1.36`.
- The same comments report a tower-recursive phase-alignment phenomenon: the
  worst frequency reinforces down the 2-adic tower.
- #400's `O(n)` `e_2=0` coset-rigidity conjecture is now refuted over both
  proper finite-field subgroups and complex roots of unity, so the surviving
  route should not use that value-set collapse.
- Local hazard: `Research/ProximityPrize/PROXIMITY_PRIZE_WORKBENCH.lean` still contains the older R4
  symmetric-function/coset-rigidity language.  Treat that section as stale until
  it is patched against #400/#407.

## Candidate closed conjecture

**Dyadic phase-chaining law.**  There is an absolute constant `C <= 2` such that
for every odd prime `p`, every dyadic subgroup `H = mu_n <= F_p^*` with
`n = 2^a`, `n | p-1`, and `n <= p^(1/4)`, and every nonzero frequency `b`,

```text
| sum_{x in H} exp(2*pi*i*b*x/p) | <= C * sqrt(n * log(p / n)).
```

The law is meant to be proved by the 2-adic tower decomposition

```text
mu_{2n} = mu_n disjoint_union zeta * mu_n
```

and a phase-increment/chaining estimate across levels, not by BGK, Weil, or
additive-energy Cauchy-Schwarz.  The target is the sup norm of the dyadic
Gaussian-period trigonometric polynomial, not a list-decoding statement.

### Current local form

The #407 refinement suggests attacking the following local form first:

```text
M(2n)^2 <= 2 * M(n)^2 * (1 + drift_n),
sum_{j < a} log(1 + drift_{2^j}) <= O(log log(p/n)).
```

This telescopes to the global `sqrt(n log(p/n))` law.  It is a closed
one-level statement once the drift sequence is made explicit; the current
mathematical gap is finding a drift bound that is not just a renamed deep-moment
or BGK lemma.

The sharpest local input is now:

```text
M(2n) = x + y                 -- exact phase alignment of the two half-cosets
x^2 + y^2 <= M(n)^2 * (1 + drift_n)
```

The elementary inequality `(x + y)^2 <= 2 * (x^2 + y^2)` then gives the
square-descent step.  Thus the open mathematical content is exactly
**submaximal aligned children**, not cancellation between the two children.

## Why this is not the forbidden restatement

- It is a direct spectral inequality for Gaussian periods of dyadic
  multiplicative subgroups.
- It makes no reference to RS codewords, received words, list sizes, or Johnson
  decoding.
- If proved, it feeds the in-tree Shaw operator route because the additive
  characters are Shaw eigenvectors, but the conjecture itself lives entirely in
  finite-field harmonic analysis.

## Why this may bypass known walls

- **Not Johnson:** the bound is spectral and applies in the small-subgroup
  regime `n << sqrt(p)` where Johnson-list arguments are irrelevant.
- **Not Weil:** Weil/Gauss completion gives `sqrt(p)`, vacuous when `n << sqrt(p)`;
  the conjecture gives `sqrt(n log(p/n))`.
- **Not additive energy:** energy gives only moment/average information and has a
  square-root loss for list bounds; this is a direct sup-norm bound.
- **Not BGK:** BGK gives `n p^{-nu}` with a tiny `nu`; the conjecture gives the
  random-trigonometric-polynomial scale.
- **Not #400:** it does not claim small symmetric-function value sets.  #400's
  `Theta(n^2)` refutation is compatible with a small spectral sup norm.

## Stress tests already passed

- The latest #389 probes through `n=256` show no power-law growth in the normalized
  constant.
- Multi-prime data at `n=64,128` showed the constant creep was not a single-prime
  artifact; the `n=256` probe then came back down.
- #400's refuted combinatorial route is orthogonal, not a counterexample.
- Local probe scripts already present for the phase face:
  `scripts/probes/probe_phase_alignment_tower.py`,
  `scripts/probes/probe_phase_alignment_prize_regime.py`, and
  `scripts/probes/probe_gauss_period_2power.py`.  I did not rerun them in this
  pass because `python3 -c 'print(1)'` hung, matching the broader local
  executable-launch issue.

## Fresh reading cluster downloaded

The following phase-route papers were downloaded to `/Users/shawwalters/papers/arklib`
on 2026-06-13:

- `arxiv-2310.15378-SpectralPropertiesGeneralizedPaleyGraphs.pdf`
- `arxiv-2406.16805-BeyondUniformCyclotomy.pdf`
- `arxiv-2604.06513-NatureSpectrumGeneralizedPaleyGraphs.pdf`
- `arxiv-2405.09319-PaleyLikeQuasirandomGraphsPolynomials.pdf`
- `arxiv-2507.09303-AsymptoticMahlerMeasureGaussianPeriods.pdf`

## New risk

The issue comments also say the worst child sums are phase-aligned, which is the
opposite of naive cancellation.  A proof therefore cannot be "independence of
halves."  It must show that the *increment locations* along the dyadic tower have
bounded metric entropy, giving Salem-Zygmund/generic-chaining growth rather than
linear growth.

## Scores

- Novelty: 9/10.  It treats dyadic Gaussian periods as a tower-indexed
  trigonometric process and asks for a chaining proof, not a classical subgroup
  sum estimate.
- Insightfulness: 9/10.  It connects the observed phase recursion, Salem-Zygmund
  sup norms, and the Shaw eigenvalue formulation.
- Proximity to prize regime: 9/10.  It is stated exactly for dyadic `mu_n` in the
  small-subgroup `n <= p^(1/4)` regime used by the prize.
- Feasibility: 8/10.  The numerical evidence is strong and the statement is closed,
  but the #407 comment shows the local square-descent is still the hard
  large-sieve/BGK content unless the drift is proved by a genuinely new
  submaximal-child mechanism.

## Current status

This is not a proof yet.  The next formal brick should be an abstract dyadic
phase-defect recursion: split a complex sum into two child sums, define the
alignment defect, and prove a deterministic chaining bound from levelwise defect
budgets.  That brick is independent of RS list decoding and can then be
instantiated against dyadic Gaussian periods.

Initial formal brick:

- `Research/ProximityPrize/Frontier/_DyadicPhaseChaining.lean`
  defines `PhaseChainingBudget`, `PhaseIncrementLaw`, and the deterministic
  consumer `level_le_of_phaseIncrementLaw`, plus a falsification form.  It now
  also defines `MultiplicativeChainingBudget`, `SquareDescentLaw`, and the
  telescope `level_le_of_squareDescentLaw` for the exact #407 local recursion.
  The newest addition is the child bridge
  `aligned_sum_sq_le_two_mul_of_sq_add_sq_le` and the local input
  `LocalAlignedChildSubmaximality`, which turns aligned child square-mass control
  into the dyadic factor-2 descent.
  The latest refinement adds `DyadicSquareDriftLaw`, the named #407 shape
  `Q(i+1) <= 2 * (1 + drift_i) * Q(i)`, together with
  `level_le_of_dyadicSquareDriftLaw` and
  `not_dyadicSquareDriftLaw_of_budget_lt`.  This gives the route a concrete
  proof/refutation hook: propose a drift product, then either certify the local
  square descent or kill it with a measured terminal excess.
  A further local bridge now records the literal affine form
  `Q(i+1) <= 2 * Q(i) + drift_i` via `AffineSquareDescentLaw` and
  `TwoAdicAffineSquareDescentLaw`, plus the elementary aligned-child theorem
  `aligned_sum_sq_le_two_mul_of_sq_add_sq_le`.  The new
  `LocalAlignedChildSubmaximality` hypothesis isolates the exact hard one-step
  target: represent the next worst aligned value as `x + y` and prove
  `x^2 + y^2 <= M(i)^2`; the factor `2` then follows with no analytic loss.
- There is also an existing untracked
  `Research/ProximityPrize/Frontier/_PhaseAlignmentGate.lean`
  square-increment gate.  Its additive certificate is complementary: it consumes
  direct per-level square increments, while `_DyadicPhaseChaining.lean` consumes
  multiplicative one-level losses `Q(i+1) <= step(i) * Q(i)`.
- Validation status: not yet certified.  Both `scripts/pg-iterate.sh` and direct
  `lake env lean` attempts stalled in the local Lean/lake launcher with no visible
  Lean child while the machine was saturated by unrelated Lean jobs; even raw
  `lean --version` hung through the resolved toolchain binary.  A later bounded
  `timeout 45 lake env lean .../_DyadicPhaseChaining.lean` attempt also failed
  to return until manually interrupted.  No proof claim should cite this file
  until it passes `scripts/pg-iterate.sh`.
