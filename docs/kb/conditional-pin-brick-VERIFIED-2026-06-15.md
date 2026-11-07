# Conditional-pin brick: BUILT + VERIFIED axiom-clean (2026-06-15)

> **Status correction (2026-10-28 audit, T48; see PG-006, PG-144, R-079).** The Lean implications
> below are valid conditional statements. The hypothesis they consume, however, is **not** "TRUE" and
> is not the genuine open core. `CrossBoundedByWick` yields the raw bound
> `E_r ≤ (2r−1)‼·n^r` at every depth `r`. The principal (`b = 0`) Fourier mode alone forces
> `q·E_r ≥ n^(2r)`, i.e. `E_r ≥ n^(2r)/q`. That exceeds `(2r−1)‼·n^r` whenever
> `n^r > q·(2r−1)‼`, which holds at the intended growing-depth prize parameters (depth `r ≈ log m`
> with `n ≫ log m`). So the all-depth raw premise, and even its `r ≤ log m` truncation, fails there.
> The open analytic content is a DC-subtracted nonzero-frequency moment bound
> (`∑_{b≠0} ‖η_b‖^(2r) = q·E_r − n^(2r)`), which this brick does not state. Calling an even moment a
> "signed" energy does not remove the DC term, since `G = −G` makes every period real (PG-144).
> This is not a claim that every fixed finite `(n, q)` violates an all-orders Gaussian envelope
> (`n = 1` is an immediate exception). The `β = 4` "0 violations" data below are finite measurements,
> not a proof. The dated text is kept as history.

The prize sup-norm bound is now reduced, in verified Lean, to a SINGLE inequality *(superseded: see
the correction above; the inequality is false at production depth)*.

## The brick (in-tree, axiom-clean — confirmed by lake-locked build, 3324 jobs, only [propext,Classical.choice,Quot.sound])
`CharPWickConditionalPin.lean` (+ `CharPMomentRecursion.lean`, `Frontier/CrossStepRung{One,Two,Three}.lean`):
- HYPOTHESIS `CrossBoundedByWick G := ∀ r≥1, cross G r ≤ 2r·(n·wick G.card r)`  (the single inequality c_r≤1).
- `rEnergy_le_wick_of_crossBound` : CrossBoundedByWick ⟹ E_r ≤ Wick_r=(2r−1)‼·n^r ∀r  (induction: r=1 base
  rEnergy_one + exact recursion rEnergy_succ/cross_eq; E_{r+1}=n·E_r+cross_r ≤ (2r+1)·n·Wick_r=Wick_{r+1}).
- `eta_pow2r_le_wick_of_crossBound` : ⟹ ‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r  (via the exact moment identity).
- `eta_le_wick_rpow_of_crossBound` : ⟹ ‖η_b‖ ≤ (q·(2r−1)‼)^{1/2r}·√n = the prize-shape √n floor with the
  slowly-growing factor; at r≍log m this is √(2n log m) — the BGK/Paley prize floor.
- BASES PROVEN (axiom-clean): r=1 (rEnergy_one), r=2 (crossStepBound_two_of_exact_moments via Sidon
  E_2=3n²−3n), r=3 (crossStepBound_three_of_exact_moments, n≥8).
NET: the ENTIRE prize sup-norm bound M(μ_n)≤√(2n log m) is now ONE explicit inequality away — c_r≤1 for all
r≤log m — with the first three rungs proven and the recursion exact. Sharper + more concrete than the prior
OpenCoreConditionalPin (WorstCaseIncidenceBounded).

## Honest scope (my cumulant finding sharpens it): the hypothesis is the GENUINE open core, NOT sign-inducible
The bases r=1,2,3 do NOT extend to all r by a simple sign/monotonicity induction. Measured (real periods,
β=4, multi-prime): κ₄=−3n < 0 (sub-Gaussian, provable from the exact 4th moment) BUT κ₆>0 — the cumulants
ALTERNATE (see period-cumulant-signinduction-refuted-2026-06-15.md). So c_r is not monotone and CrossBoundedByWick
cannot be discharged by "κ₄<0 ⇒ κ₆<0"; it requires the deep analytic (effective-CLT-at-depth = BCHKS 1.12)
argument. The bound is TRUE (periods asymptotically Gaussian, max→√(2n log m); β=4 data 0 violations) — the
conditional pin faithfully isolates exactly the open analytic content into one inequality, no more, no less.
