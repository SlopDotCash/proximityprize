/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# G73: the Shkredov–Vyugin multi-shift bound has an exponent floor strictly above `1/2`

This file closes, as a calibrated axiom-clean no-go, the last third-party escape the G72 referee
left open for the `δ*` core (issue #466): the Shkredov–Vyugin *multi-shift* intersection bound
(arXiv:1102.1172, Corollary 1.2).  For a multiplicative subgroup `R ⊆ ℤ_p^*`, `k` distinct nonzero
shifts, and `p` large enough, SV Cor 1.2 gives

`|R ∩ (R+μ₁) ∩ ⋯ ∩ (R+μ_k)| ≤ 4(k+1)·(|R|^{1/(2k+1)} + 1)^{k+1}`,

which the paper summarises informally as `≪_k |R|^{1/2 + α_k}` with `α_k → 0` as `k → ∞`.  The
campaign's transversality hope needs a genuinely sub-`|R|^{1/2}` cross-shift cancellation (the
Paley/BGK √-saving) at a *fixed* thin cell.

## The obstruction (this file, exact and `k`-uniform)

The SV bound, taken as a function of `|R|`, is **never below `|R|^{1/2}`**; its exponent has a
strict positive floor for every finite `k`:

`4(k+1)·(R^{1/(2k+1)} + 1)^{k+1} ≥ R^{(k+1)/(2k+1)} = R^{1/2 + 1/(2(2k+1))} > R^{1/2}`   (`R ≥ 1`).

The excess exponent `1/(2(2k+1))` is strictly positive for every `k`, so a *fixed* number of
Shkredov–Vyugin shifts can never reach the `1/2` target: it always leaves a residual exponent gap
`≥ 1/(2(2k+1))`.  Driving that gap below any `ε > 0` forces `k ≥ 1/(4ε) − 1/2`, i.e. **unboundedly
many distinct shifts** — the `α_k → 0` limit is genuinely asymptotic in the number of shifts and is
never realised at any single application to the fixed thin subgroup at the adversarial wall.

This is the exact quantification of the G72 referee's "thickness-essential in the wrong direction"
verdict, on the SV *exponent* rather than its (satisfiable) large-`p` hypothesis: even where the SV
hypothesis holds, its output exponent is `> 1/2` at every finite `k`, so multi-shift SV supplies no
sub-`√`-cancellation.  It does NOT bound the campaign cross-cell (that stays open); it certifies the
named third-party lever is exponent-floored above the required `1/2`.

Complements: `WF407_T02Shkredov` (the single-shift `E₂/E₃` density gate `|Γ| > p^{1/4}` is never met
at prize density), `_A3SumProductDepthConfinement` (the sum-product cluster is depth-2 confined).
Neither owns this multi-shift exponent-floor statement.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G73ShkredovMultiShiftExponentFloor

open Real

/-- The Shkredov–Vyugin Corollary 1.2 multi-shift upper bound as a function of the subgroup size
`R` and the number of shifts `k`:  `4(k+1)·(R^{1/(2k+1)} + 1)^{k+1}`. -/
noncomputable def svBound (R : ℝ) (k : ℕ) : ℝ :=
  4 * (k + 1) * (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1)

/-- The exponent SV can certify at `k` shifts, `(k+1)/(2k+1)`, equals `1/2` plus a strictly
positive excess `1/(2(2k+1))`. -/
theorem svExponent_eq_half_add (k : ℕ) :
    ((k : ℝ) + 1) / (2 * k + 1) = 1 / 2 + 1 / (2 * (2 * k + 1)) := by
  have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  field_simp
  ring

/-- The SV excess exponent is strictly positive for every `k`: the certified exponent is strictly
above `1/2`. -/
theorem svExcess_pos (k : ℕ) : (0 : ℝ) < 1 / (2 * (2 * k + 1)) := by positivity

/-- `(k+1)/(2k+1) ≥ 1/2` for every `k` (the exponent floor, weak form). -/
theorem svExponent_ge_half (k : ℕ) : (1 : ℝ) / 2 ≤ ((k : ℝ) + 1) / (2 * k + 1) := by
  rw [svExponent_eq_half_add]
  have := svExcess_pos k
  linarith

/-- Exponent arithmetic: `(1/(2k+1)) * (k+1) = (k+1)/(2k+1)`. -/
theorem exponent_mul_eq (k : ℕ) :
    (1 : ℝ) / (2 * k + 1) * ((k : ℝ) + 1) = ((k : ℝ) + 1) / (2 * k + 1) := by
  have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  field_simp

/-- **Core power inequality.**  For `R ≥ 1` and any `k`, the SV bound dominates `R^{(k+1)/(2k+1)}`:
drop the `+1` in the base (monotone `rpow`), collapse the double power, and use `4(k+1) ≥ 1`. -/
theorem svBound_ge_rpow (R : ℝ) (hR : (1 : ℝ) ≤ R) (k : ℕ) :
    R ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ svBound R k := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  have hbase0 : (0 : ℝ) ≤ R ^ ((1 : ℝ) / (2 * k + 1)) := Real.rpow_nonneg hR0 _
  have hbase : R ^ ((1 : ℝ) / (2 * k + 1)) ≤ R ^ ((1 : ℝ) / (2 * k + 1)) + 1 := by linarith
  -- `(R^{1/(2k+1)})^{k+1} ≤ (R^{1/(2k+1)}+1)^{k+1}`, both bases nonneg, exponent `k+1 ≥ 0`.
  have hpow : (R ^ ((1 : ℝ) / (2 * k + 1))) ^ ((k : ℝ) + 1)
      ≤ (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1) :=
    Real.rpow_le_rpow hbase0 hbase (by positivity)
  -- LHS collapses to `R^{(k+1)/(2k+1)}` via `(R^a)^b = R^(a*b)`.
  have hcollapse : (R ^ ((1 : ℝ) / (2 * k + 1))) ^ ((k : ℝ) + 1)
      = R ^ (((k : ℝ) + 1) / (2 * k + 1)) := by
    rw [← Real.rpow_mul hR0, exponent_mul_eq]
  -- combine: `R^{(k+1)/(2k+1)} = (R^{...})^{k+1} ≤ (R^{...}+1)^{k+1} ≤ 4(k+1)·(...)^{k+1}`.
  have hpospow : (0 : ℝ) ≤ (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1) :=
    Real.rpow_nonneg (by linarith) _
  have hcoef : (1 : ℝ) ≤ 4 * ((k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  calc R ^ (((k : ℝ) + 1) / (2 * k + 1))
      = (R ^ ((1 : ℝ) / (2 * k + 1))) ^ ((k : ℝ) + 1) := hcollapse.symm
    _ ≤ (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1) := hpow
    _ = 1 * (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1) := (one_mul _).symm
    _ ≤ 4 * ((k : ℝ) + 1) * (R ^ ((1 : ℝ) / (2 * k + 1)) + 1) ^ ((k : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right hcoef hpospow
    _ = svBound R k := by rw [svBound]

/-- **The exponent floor.**  For `R ≥ 1` the SV multi-shift bound is at least `R^{1/2}`: it can
never certify a sub-square-root cross-shift cancellation. -/
theorem svBound_ge_sqrt (R : ℝ) (hR : (1 : ℝ) ≤ R) (k : ℕ) :
    R ^ ((1 : ℝ) / 2) ≤ svBound R k := by
  refine le_trans ?_ (svBound_ge_rpow R hR k)
  exact Real.rpow_le_rpow_of_exponent_le hR (svExponent_ge_half k)

/-- **Strict exponent floor.**  For `R > 1` the SV bound strictly exceeds `R^{1/2}`, so multi-shift
SV never reaches the wall's required `1/2` exponent at any finite number of shifts. -/
theorem svBound_gt_sqrt (R : ℝ) (hR : (1 : ℝ) < R) (k : ℕ) :
    R ^ ((1 : ℝ) / 2) < svBound R k := by
  have hR1 : (1 : ℝ) ≤ R := le_of_lt hR
  have hstrict : R ^ ((1 : ℝ) / 2) < R ^ (((k : ℝ) + 1) / (2 * k + 1)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hR
    rw [svExponent_eq_half_add]
    have := svExcess_pos k
    linarith
  exact lt_of_lt_of_le hstrict (svBound_ge_rpow R hR1 k)

/-- **`k`-uniform residual-gap lower bound.**  The excess of the SV exponent over `1/2` is at least
`1/(2(2k+1))` at every finite `k`; there is no finite number of shifts at which the excess vanishes.
This quantifies that the `α_k → 0` limit is unattained at any single application. -/
theorem svExponent_excess_ge (k : ℕ) :
    ((k : ℝ) + 1) / (2 * k + 1) - 1 / 2 = 1 / (2 * (2 * k + 1)) := by
  rw [svExponent_eq_half_add]; ring

/-- To force the SV exponent excess below a target `ε > 0` one needs `k` shifts with
`2·(2k+1) ≥ 1/ε`, i.e. **unboundedly many distinct shifts as `ε → 0`.**  Contrapositive form:
if `k` is too small (`2(2k+1) < 1/ε`) then the residual exponent gap exceeds `ε`. -/
theorem residual_gap_forces_many_shifts (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : (2 : ℝ) * (2 * k + 1) < 1 / ε) :
    ε < ((k : ℝ) + 1) / (2 * k + 1) - 1 / 2 := by
  rw [svExponent_excess_ge]
  have hpos : (0 : ℝ) < 2 * (2 * (k : ℝ) + 1) := by positivity
  rw [lt_div_iff₀ hpos]
  -- from `2(2k+1) < 1/ε` and `ε>0`: `ε · 2(2k+1) < 1`.
  have := (lt_div_iff₀ hε).mp hsmall
  linarith [this]

/-! ## Axiom audit -/
#print axioms svExponent_eq_half_add
#print axioms svExcess_pos
#print axioms svExponent_ge_half
#print axioms exponent_mul_eq
#print axioms svBound_ge_rpow
#print axioms svBound_ge_sqrt
#print axioms svBound_gt_sqrt
#print axioms svExponent_excess_ge
#print axioms residual_gap_forces_many_shifts

end ArkLib.ProximityGap.Frontier.G73ShkredovMultiShiftExponentFloor
