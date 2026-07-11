# #466 — the DQR renormalization arc: 13 theorems, one working equation (2026-07-11)

One-day research arc on the dyadic-quotient-renormalization angle (DQR) of the centered
attack matrix, opened after the DC correction. All results axiom-clean
(`propext, Classical.choice, Quot.sound`), verified via `lake env lean` + numeric probes.

## The frame (files `_DQR23TwoScaleCenteredRecursion.lean`)
1. `eta_two_scale` (DQR-2→THEOREM): `η'_b = η_b + η_{b·a}` for tower steps `G' = G ⊔ aG`.
2. `eta_im_zero`: periods are REAL for mult-closed `G ∋ −1`.
3. `offZero_fourteenth_two_scale` (DQR-3→THEOREM): the signed binomial ledger, no abs values.
4. `cross_correlation_exact`: `∑_{b≠0} η_b·η_{b·a} = −|G|²` — pair-and-sum flow is
   mean-anticoherent at every level.

## The stratum theory (`_DQR4*` files)
5. `crossMoment_eq_rep`: `(k,1)` strata = centered rep counts at the twist point.
6. `crossMoment_eq_mixedCount` + `mixedSolutionCount_eq_repCorrelation`: general strata =
   dilated rep-rep correlations `∑_c f_j(c)f_k(−ac)`.
7. `centeredStratum_identity`: centered-centered correlation = q·(centered count) exactly —
   no DC residue at any stratum. Falsify-first record: stratum-wise CS = the machine-refuted
   doubling wall (depth-increasing).
8. `oneSidedCenteredStratum`: every stratum = weighted sample of the depth-j deviation field
   on the sparse dilated support of `f_k`.
9. `oddPowerSum_eq_rep_zero` + `twistAverage_factorizes`: `∑_{a≠0} T_{k,j}(a) = P_k·P_j`,
   `P_r = q·f_r(0) − n^r` — the twist-averaged ledger in CLOSED FORM (zero-sum counts;
   Lam–Leung objects; odd-r counts = pure wraparound).
10. `shift_dvd_repCount_zero`: `r | f_r(0)` (prime r; fixed-point-free rotation + p-group
    congruence).
11. `dilation_dvd_repCount_zero` + `mul_dvd_repCount_zero`: `n·r | f_r(0)` (free dilation via
    first-coordinate normalization; MulClosed finite sets are groups).
12. `stratum_palindrome`: `T_k = T_{14−k}` for tower twists (`a² ∈ G`) — 13 strata → 7.
13. `symmetrized_recursion` (CAPSTONE): for tower steps,
    `S₁₄(G') = 2·S₁₄(G) + 2·∑_{k=1}^{6} C(14,k)·T_k + 3432·T₇`.

## Probes (verified, falsify-first)
- `probe_dqr4_zero_rep_divisibility.py`: `n·r | f_r(0)` everywhere; odd-r pure-wraparound
  (`f₃(0) = f₅(0) = 0` exactly at p=12289, n=32).
- `probe_dqr4_twist_discrepancy.py`: ledger verified to 1e-6 at all scales; ACTUAL dyadic
  twists deviate 10³–10⁵× from the twist mean at extreme strata — the wall is POINTWISE, not
  average-case; per-level growth factor 33–1517× (< 2¹³ trivial, > 2⁷ Gaussian shallow).
- swarm no-go `_DQRSecondMomentAnticorrelationNoGo`: quadratic anticoherence alone cannot
  force contraction — higher strata mandatory (which items 5–8 supply exactly).

## The open core in this frame
Iterating the working equation over the 29 production levels, the depth-seven gate
(`qE₇ − n¹⁴ ≤ q·2¹⁸·n⁷`, DC-corrected) is equivalent to controlling seven pointwise-atypical,
integrality-constrained, palindromically-paired strata `T₁…T₇` per level. Their twist AVERAGE
is closed-form; their pointwise values at the actual dyadic twists are the conjecture.
Next candidates: the 29-level iteration consumer (fold of the working equation); exact
small-scale stratum tables; welding `f_r(0)` to the in-tree char-0/Lam–Leung closed forms.
