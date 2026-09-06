/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The SECOND Stepanov stall on mu_n: the Stepanov-Weil sqrt(q) FIELD bound is VACUOUS in the
# prize regime, and Johnson sqrt(kn) sits strictly below BOTH Stepanov outputs (#444, lane bivstep)

`StepanovStructuredVacuous` formalized the FIRST Stepanov stall: classical Stepanov on the
SEPARABLE subgroup relation `X^n - 1` pins the multiplicity to `M = 1`
(`mu_n_roots_simple`), so the engine collapses to the trivial degree bound `s* <= deg P <= n - 1`
(`stepanov_collapses_to_degree`).  Its docstring records, AS PROSE ONLY, the SECOND stall: the
Stepanov-Weil / Kelley-Owen field-root bound is `~ sqrt(q)`, "exponentially vacuous because
`p ~ n * 2^128 >> n^2`".  This file makes that second stall an axiom-clean THEOREM, and pins the
exact three-way arithmetic separation in the prize regime.

## The object (issue #444/#407 prize regime)

`mu_n` is the THIN 2-power subgroup of `F_q^*`, `n = 2^a`, `n | q - 1`, prize regime `q ~ n^beta`,
`beta in [4, 5]` (the brief: `q >> n^3`, certainly `q >= n^2`).  Two Stepanov outputs on `mu_n`:

* (A) classical Stepanov on the separable `X^n - 1`: trivial degree bound `s* <= n - 1`
  (already in tree: `stepanov_collapses_to_degree`).
* (B) Stepanov-Weil / Kelley-Owen over `F_q`: a `t`-nomial has `~ sqrt(q)` roots in `F_q`; the
  bound is in `sqrt(q)`, NOT in the subgroup size.

## What is proven here (all axiom-clean, real-number arithmetic, NON-moment, NON-character)

* `weil_field_bound_vacuous` : `(n : R)^2 <= q  =>  (n : R) <= Real.sqrt q`.  In the prize regime
  `q >= n^2` (automatic, `beta >= 3 > 2`), the Weil FIELD bound `sqrt q` is `>= n`, i.e. it EXCEEDS
  the trivial degree bound `n` of (A).  So (B) is VACUOUS on `mu_n` -- it is worse than the trivial
  bound that needs no Weil input at all.
* `johnson_below_trivial` : `k < n  =>  Real.sqrt (k * n) < n`.  The Johnson radius is strictly
  below the trivial degree bound (A) for every interior rate `k < n`.
* `johnson_below_weil` : `k * n < q  =>  Real.sqrt (k * n) < Real.sqrt q`.  Johnson is strictly
  below the Weil bound (B) too.
* `stepanov_outputs_strictly_above_johnson` : the packaged three-way separation in the prize
  regime (`n^2 <= q`, `k < n`, `k * n < q`): Johnson `sqrt(kn)` `<` trivial `n` `<=` Weil `sqrt q`.
  Hence NEITHER Stepanov form reaches Johnson, AND the Weil form is additionally vacuous.

## Honest scope (rules 1, 3, 4, 6 + ASYMPTOTIC GUARD)

Pure real/Nat field-cardinality arithmetic; NO character sum, NO moment, NO energy.  This is a
refutation-with-mechanism (rule 4): it pins the SECOND Stepanov stall (the `sqrt q` field bound's
prize-regime vacuity) that `StepanovStructuredVacuous`'s verdict named only in prose.  Thinness
enters via the prize regime `q >> n` (`mu_n` THIN): for the THICK regime `q ~ n^{2.3..3.2}` the
inequality `sqrt q >= n` is exactly where the field bound starts to bite, so the vacuity is
thinness-localized to `beta >= 2`.  Makes NO capacity / beyond-Johnson / sub-linear claim; the
cliff-at-n/2 is untouched.  Does NOT prove CORE; it maps a wall.  CORE
`M(mu_n) <= C sqrt(n log(p/n))` stays OPEN.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.

## References
- Kelley-Owen 2015 (arXiv:1510.01758): trinomial `X^n + aX^s + b` has `<= delta * floor(1/2 +
  sqrt((q-1)/delta))` roots in `F_q`; the bound is in `sqrt q`, tight for square `q`.
- Bi-Cheng-Rojas / Kelley 2016 (arXiv:1602.00208): a `t`-nomial has
  `<= 2(q-1)^{1-1/(t-1)} C^{1/(t-1)}` nonzero `F_q`-roots.
-/

open scoped NNReal

namespace ArkLib.ProximityGap.StepanovWeilQVacuous

/-- **The Weil field bound is vacuous in the prize regime.**  If `q >= n^2` (automatic for the
prize, `q ~ n^beta`, `beta >= 3 > 2`), then `n <= sqrt q`.  The Stepanov-Weil / Kelley-Owen
field-root bound `~ sqrt q` therefore EXCEEDS the trivial degree bound `n` of the separable-relation
Stepanov collapse: it is worse than the bound that needs no Weil input, hence VACUOUS on `mu_n`. -/
theorem weil_field_bound_vacuous {n q : ℝ} (hn : 0 ≤ n) (hq : n ^ 2 ≤ q) :
    n ≤ Real.sqrt q := by
  calc n = Real.sqrt (n ^ 2) := by rw [Real.sqrt_sq hn]
    _ ≤ Real.sqrt q := Real.sqrt_le_sqrt hq

/-- **Johnson is strictly below the trivial degree bound.**  For an interior rate `k < n`
(`0 < n`), `sqrt (k * n) < n`.  So the Johnson radius `sqrt(kn)` is strictly smaller than the
trivial Stepanov output `n` (A); Johnson is NOT what classical Stepanov supplies. -/
theorem johnson_below_trivial {k n : ℝ} (hk : 0 ≤ k) (hn : 0 < n) (hkn : k < n) :
    Real.sqrt (k * n) < n := by
  have hlt : k * n < n ^ 2 := by nlinarith [hn]
  calc Real.sqrt (k * n) < Real.sqrt (n ^ 2) := by
        apply Real.sqrt_lt_sqrt (by positivity) hlt
    _ = n := Real.sqrt_sq hn.le

/-- **Johnson is strictly below the Weil bound.**  If `k * n < q`, then
`sqrt (k * n) < sqrt q`.  So the Johnson radius is strictly below the Stepanov-Weil field
output `sqrt q` (B) as well. -/
theorem johnson_below_weil {k n q : ℝ} (hk : 0 ≤ k) (hn : 0 ≤ n) (hlt : k * n < q) :
    Real.sqrt (k * n) < Real.sqrt q :=
  Real.sqrt_lt_sqrt (by positivity) hlt

/-- **The three-way separation in the prize regime (the packaged verdict).**  In the prize regime
(`n^2 <= q`, interior rate `k < n`, and `k * n < q` -- all automatic for `q ~ n^beta`, `beta >= 3`,
`k < n`):

  `Johnson sqrt(kn)  <  trivial n  <=  Weil sqrt q`.

Hence the Johnson radius lies strictly BELOW both Stepanov outputs (the trivial separable-relation
degree bound AND the Weil field bound), and the Weil field bound is itself `>= n`, i.e. VACUOUS
(worse than the trivial bound).  Neither Stepanov form reaches Johnson, let alone the prize floor
`sqrt(n log(q/n))`. -/
theorem stepanov_outputs_strictly_above_johnson {k n q : ℝ}
    (hk : 0 ≤ k) (hn : 0 < n) (hkn : k < n) (hq2 : n ^ 2 ≤ q) (hknq : k * n < q) :
    Real.sqrt (k * n) < n ∧ n ≤ Real.sqrt q ∧ Real.sqrt (k * n) < Real.sqrt q :=
  ⟨johnson_below_trivial hk hn hkn, weil_field_bound_vacuous hn.le hq2,
    johnson_below_weil hk hn.le hknq⟩

end ArkLib.ProximityGap.StepanovWeilQVacuous

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.StepanovWeilQVacuous.weil_field_bound_vacuous
#print axioms ArkLib.ProximityGap.StepanovWeilQVacuous.johnson_below_trivial
#print axioms ArkLib.ProximityGap.StepanovWeilQVacuous.johnson_below_weil
#print axioms ArkLib.ProximityGap.StepanovWeilQVacuous.stepanov_outputs_strictly_above_johnson
