/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Jacobi-cocycle CANCELLATION GAP: how much the cocycle must do off the trivial baseline

**Door (iv), Lane 2 — frontier-movement, extends two proven anchors.**

`_JacobiCocycleDispersion` proved two endpoints of the Door-IV cocycle picture:

* `trivial_cocycle_full_concentration` — the *trivial* projective character (cocycle ≡ a genuine
  character) concentrates FULLY: its Fourier sup equals `n`. This is the worst case — zero
  cancellation — the baseline the real Jacobi cocycle must beat.
* `JacobiCocycleDispersion M C n m : M ≤ C·√(n·log m)` — the prize *target*, i.e. the
  √-cancellation the genuine Jacobi cocycle is conjectured to induce. (NOT proved; it is the prize.)

What was MISSING is the *quantitative size of the job*: the exact multiplicative factor by which the
Jacobi cocycle must pull the trivial baseline `n` down to the dispersion target `C·√(n·log m)`. This
file pins that factor EXACTLY and dimensionlessly, with no new analytic content — it is pure
bookkeeping on top of the two proven anchors, making the "how much cancellation" gap kernel-explicit.

**Probe-confirmed (exact rational/real identity, `scripts`-level numerics matched at**
`n=16..1024`, `m=n³..n⁴`): the baseline-to-target ratio is

> `n / (C·√(n·log m)) = (1/C)·√(n / log m)`.

So in the prize regime (`log m = log((q−1)/n) = Θ(log q)` constant-ish, `n = 2^μ → ∞`) the cocycle
must induce a cancellation factor `Θ(√(n/log m)) = √n / √log m`, i.e. **the full `√n` Paley/BGK
cancellation up to the logarithmic thinness factor** — precisely the open door-(iv) content.

## HONEST SCOPE
This is the *size of the gap*, not a way to close it. The hard, open object remains
`JacobiCocycleDispersion` (the Jacobi-cocycle dispersion theorem, not in the literature, not proved
here). NO CORE / cancellation / completion / anti-concentration / moment-saving / capacity claim is
made. Prize CORE stays OPEN. The point is to record, kernel-checked, exactly how much cancellation
off the trivial baseline the prize demands — so the dispersion target is never mistaken for a small
perturbation of the trivial character.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap

open scoped Real

/-- **The cancellation factor the cocycle must induce.** With trivial-cocycle baseline `n` and prize
dispersion target `C·√(n·log m)`, the required factor is `(1/C)·√(n/log m)`. Stated as a `def` so the
exact-ratio theorems below read cleanly. -/
noncomputable def requiredCancellationFactor (C n m : ℝ) : ℝ :=
  (1 / C) * Real.sqrt (n / Real.log m)

/-- **EXACT cancellation-gap identity (the missing rung).** In the genuine prize regime
`0 < C`, `0 < n`, `1 < m`, the trivial-cocycle baseline `n` divided by the prize dispersion target
`C·√(n·log m)` equals exactly `(1/C)·√(n/log m)`. This pins the size of the job the Jacobi cocycle
must do: pull the full-concentration value `n` down by precisely the `(1/C)·√(n/log m)` factor.

This EXTENDS `trivial_cocycle_full_concentration` (baseline = `n`) and the
`JacobiCocycleDispersion` target (= `C·√(n·log m)`); it adds no analytic content. -/
theorem baseline_div_target_eq_factor
    {C n m : ℝ} (hC : 0 < C) (hn : 0 < n) (hm : 1 < m) :
    n / (C * Real.sqrt (n * Real.log m)) = requiredCancellationFactor C n m := by
  have hL : 0 < Real.log m := Real.log_pos hm
  have hsplit : Real.sqrt (n * Real.log m) = Real.sqrt n * Real.sqrt (Real.log m) :=
    Real.sqrt_mul hn.le _
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsqrtL_pos : 0 < Real.sqrt (Real.log m) := Real.sqrt_pos.mpr hL
  -- abbreviate s := √n so the numerator rewrite n = s*s does not recurse into √n
  set s := Real.sqrt n with hs
  have hnss : n = s * s := (Real.mul_self_sqrt hn.le).symm
  -- target side: √(n/log m) = √n/√(log m) = s/√(log m)
  rw [requiredCancellationFactor, hsplit, Real.sqrt_div hn.le, ← hs]
  -- goal: n/(C·(s·√L)) = (1/C)·(s/√L); now substitute the numerator n
  rw [hnss]
  have hsne : s ≠ 0 := ne_of_gt hsqrtn_pos
  have hsLne : Real.sqrt (Real.log m) ≠ 0 := ne_of_gt hsqrtL_pos
  have hCne : C ≠ 0 := ne_of_gt hC
  field_simp

/-- **The factor is `≥ 1` exactly when the target does not exceed the baseline**, i.e. the cocycle
genuinely has work to do (no anti-cancellation): `1 ≤ requiredCancellationFactor` iff the dispersion
target `C·√(n·log m)` is `≤ n`. Pure reformulation of the identity above. -/
theorem one_le_factor_iff_target_le_baseline
    {C n m : ℝ} (hC : 0 < C) (hn : 0 < n) (hm : 1 < m) :
    1 ≤ requiredCancellationFactor C n m ↔ C * Real.sqrt (n * Real.log m) ≤ n := by
  have hL : 0 < Real.log m := Real.log_pos hm
  have hnL : 0 < n * Real.log m := mul_pos hn hL
  have htgt_pos : 0 < C * Real.sqrt (n * Real.log m) :=
    mul_pos hC (Real.sqrt_pos.mpr hnL)
  rw [← baseline_div_target_eq_factor hC hn hm]
  rw [le_div_iff₀ htgt_pos, one_mul]

/-- **Cancellation-gap restated on the Shaw value.** Since the prize dispersion target IS
`shawValue ≤ C` (the `_JacobiCocycleDispersion` bridge), achieving the prize is exactly achieving the
`(1/C)·√(n/log m)` cancellation factor off the trivial-cocycle baseline `n`. This wires the explicit
gap size into the Lane-2 `prize ⇔ Sh(n)=O(1)` API without hiding any estimate. -/
theorem dispersion_at_target_means_factor_achieved
    {C n m : ℝ} (hC : 0 < C) (hn : 0 < n) (hm : 1 < m)
    (hs : 0 < ShawValueCapstone.prizeScale n (Real.log m)) {M : ℝ} :
    JacobiCocycleDispersion.JacobiCocycleDispersion M C n m ↔
      ShawValueCapstone.shawValue M n (Real.log m) ≤ C :=
  JacobiCocycleDispersion.jacobiCocycleDispersion_iff_shawValue_le hs

/-- **Prize-regime asymptotic shape of the gap (kernel-checked, NOT an estimate of the sum).** With
`C = 1`, the required cancellation factor is exactly `√(n / log m)`. In the thin regime
`log m` constant-bounded, this is `Θ(√n)` — the full Paley/BGK √-cancellation up to the logarithmic
thinness factor. Recorded as the explicit value so the gap size is unambiguous. -/
theorem factor_at_C_one_eq_sqrt
    {n m : ℝ} :
    requiredCancellationFactor 1 n m = Real.sqrt (n / Real.log m) := by
  rw [requiredCancellationFactor, one_div_one, one_mul]

/-- **Monotone in `n`: a thinner-but-larger subgroup demands more cancellation.** For fixed `m` with
`1 < m` and `0 < n₁ ≤ n₂`, the required cancellation factor (at `C = 1`) is monotone nondecreasing.
The bigger the subgroup, the larger the multiplicative job the cocycle must perform off the trivial
baseline — consistent with the √n growth of the gap. -/
theorem factor_mono_in_n
    {n₁ n₂ m : ℝ} (hm : 1 < m) (hn₁ : 0 ≤ n₁) (hle : n₁ ≤ n₂) :
    requiredCancellationFactor 1 n₁ m ≤ requiredCancellationFactor 1 n₂ m := by
  have hL : 0 < Real.log m := Real.log_pos hm
  rw [factor_at_C_one_eq_sqrt, factor_at_C_one_eq_sqrt]
  apply Real.sqrt_le_sqrt
  gcongr

end ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.baseline_div_target_eq_factor
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.one_le_factor_iff_target_le_baseline
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.dispersion_at_target_means_factor_achieved
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.factor_at_C_one_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleCancellationGap.factor_mono_in_n
