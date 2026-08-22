/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import Mathlib.Tactic

/-!
# The trivial-cocycle baseline OVERSHOOTS the prize target in the thin regime (constraint lemma)

**Door (iv), Lane 2/3 — extends `_JacobiCocycleDispersion`, kernel-checks the named gap.**

`_JacobiCocycleDispersion` proves the trivial-cocycle Fourier transform is a literal delta of full mass
`n` (`trivial_cocycle_delta_fiber`), and names the open prize predicate
`JacobiCocycleDispersion M C n m := M ≤ C·√(n·log m)`. The docstrings assert "the prize requires the
cocycle to BREAK this concentration down to √n·polylog" but never kernel-check that the trivial
baseline `M = n` actually FAILS the dispersion predicate. This file supplies exactly that.

The arithmetic is clean: for the trivial baseline `M = n`,

  `JacobiCocycleDispersion n C n m  ↔  n ≤ C·√(n·log m)  ↔  √n ≤ C·√(log m)  ↔  n ≤ C²·log m`.

So in the THIN regime `n > C²·log m` (the prize regime: `m ≈ p/n ≈ n^{β−1}`, `log m ≈ (β−1)log n ≪ n`),
the trivial-cocycle concentration `n` STRICTLY EXCEEDS the prize ceiling `C·√(n·log m)` — the trivial
cocycle is NOT a dispersion witness. This is the precise, kernel-checked content of "the prize requires
the genuine cocycle to break the n-spike": the entire prize gap is the multiplicative factor
`√(n / (C²·log m)) > 1` by which the trivial baseline overshoots.

## HONEST SCOPE
This locks that the TRIVIAL cocycle fails the dispersion predicate in the thin regime — it does NOT
prove the GENUINE cocycle satisfies it (that is the open `JacobiCocycleDispersion`, untouched). It is a
baseline/constraint identity: it pins the size of the gap the genuine cocycle must close, nothing more.
NO CORE / cancellation / completion / anti-concentration / moment-saving / capacity claim. CORE OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot

open ProximityGap.Frontier.JacobiCocycleDispersion

/-- **Dispersion predicate at the trivial baseline reduces to `n ≤ C²·log m`.** For `0 ≤ n`,
`0 ≤ C`, `0 ≤ log m`, the trivial-baseline dispersion `JacobiCocycleDispersion n C n m` (i.e.
`n ≤ C·√(n·log m)`) holds iff `n ≤ C²·(log m)`. -/
theorem trivial_dispersion_iff_thin_le {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) :
    JacobiCocycleDispersion n C n (Real.exp logm) ↔ n ≤ C ^ 2 * logm := by
  unfold JacobiCocycleDispersion
  rw [Real.log_exp]
  constructor
  · intro h
    -- n ≤ C√(n logm) ⟹ n² ≤ C²·n·logm ⟹ (if n>0) n ≤ C² logm; if n=0 trivial
    have hsqrt : Real.sqrt (n * logm) ≥ 0 := Real.sqrt_nonneg _
    have hsq : n ^ 2 ≤ (C * Real.sqrt (n * logm)) ^ 2 := by
      apply sq_le_sq'
      · nlinarith [hsqrt, hC, hn]
      · exact h
    have hCsq : (C * Real.sqrt (n * logm)) ^ 2 = C ^ 2 * (n * logm) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hCsq] at hsq
    rcases eq_or_lt_of_le hn with hn0 | hn0
    · rw [← hn0]; positivity
    · nlinarith [hsq, hn0]
  · intro h
    -- n ≤ C² logm ⟹ n² ≤ C²·n·logm ⟹ n ≤ C√(n logm)
    have hkey : n ^ 2 ≤ C ^ 2 * (n * logm) := by nlinarith [h, hn]
    have hrhs : (C * Real.sqrt (n * logm)) ^ 2 = C ^ 2 * (n * logm) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hrhs_nonneg : 0 ≤ C * Real.sqrt (n * logm) := by positivity
    nlinarith [hkey, hrhs, hrhs_nonneg, sq_nonneg (n - C * Real.sqrt (n * logm)), hn]

/-- **Trivial-cocycle OVERSHOOT in the thin regime (the constraint).** When `n > C²·log m` (the prize
regime), the trivial-cocycle baseline concentration `n` STRICTLY exceeds the prize ceiling
`C·√(n·log m)` — i.e. `¬ JacobiCocycleDispersion n C n m`. The trivial cocycle is not a dispersion
witness; the genuine cocycle must close a strict gap. -/
theorem trivial_cocycle_overshoots_thin {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    ¬ JacobiCocycleDispersion n C n (Real.exp logm) := by
  rw [trivial_dispersion_iff_thin_le hn hC hlogm]
  push_neg
  exact hthin

/-- **Strict overshoot is exactly the thin-threshold failure.** This is the strict companion to
`trivial_dispersion_iff_thin_le`: the trivial baseline exceeds the prize ceiling precisely when
`C²·log m < n`. It packages the Door-IV baseline gap as a strict inequality, with no genuine-cocycle
claim. -/
theorem trivial_strict_overshoot_iff {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) :
    C * Real.sqrt (n * logm) < n ↔ C ^ 2 * logm < n := by
  constructor
  · intro hgap
    by_contra hnot
    have hle : n ≤ C ^ 2 * logm := le_of_not_gt hnot
    have hdisp : JacobiCocycleDispersion n C n (Real.exp logm) :=
      (trivial_dispersion_iff_thin_le hn hC hlogm).2 hle
    unfold JacobiCocycleDispersion at hdisp
    rw [Real.log_exp] at hdisp
    exact not_lt_of_ge hdisp hgap
  · intro hthin
    have hnot : ¬ JacobiCocycleDispersion n C n (Real.exp logm) :=
      trivial_cocycle_overshoots_thin hn hC hlogm hthin
    unfold JacobiCocycleDispersion at hnot
    rw [Real.log_exp] at hnot
    exact lt_of_not_ge hnot

/-- **Positive additive gap at the trivial baseline.** In the thin regime the amount by which the
trivial-cocycle spike exceeds the prize ceiling is strictly positive. This is only a baseline audit
identity: the open work is still to make the genuine Jacobi cocycle disperse. -/
theorem trivial_overshoot_gap_pos {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    0 < n - C * Real.sqrt (n * logm) := by
  have hgap : C * Real.sqrt (n * logm) < n :=
    (trivial_strict_overshoot_iff hn hC hlogm).2 hthin
  linarith

end ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_dispersion_iff_thin_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_cocycle_overshoots_thin
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_strict_overshoot_iff
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_overshoot_gap_pos
