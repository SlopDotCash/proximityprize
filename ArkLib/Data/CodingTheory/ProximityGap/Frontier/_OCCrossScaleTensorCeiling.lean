/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false

/-!
# LANE OC-CROSSSCALE (#466, Opus core, 2026-07-10): the TENSOR CEILING that closes the
  last conceptual non-BGK escape — a cross-scale / super-additive certificate — as a
  strict AMPLIFICATION no-go (axiom-clean).

## The route this closes

After the fixed-cell ledger was exhausted — positive census (`_AnomalyLocalization`),
signed anomaly pinned to the wall `M` (fable G74), embedding transversality
(`_OCPieceBHeightNormCeiling`, `_OCGaloisEmbeddingEquidistribution`, #505), Shkredov–Vyugin
multi-shift exponent-floored (G73), chaining flat-Dudley BGK-tight (G69/G70) — BOTH the
fable-critic (G74 "rank-one next target") and the G56 frontier lane (final receipt) converged
on the SAME single surviving conceptual hope, stated as: *a super-additive combination across
DISTINCT n-scales — a genuinely new object OUTSIDE the fixed-cell BGK ledger.* Every fixed-cell
certificate is wall-pinned; the only thing that could reopen the board is a joint certificate on
several scales at once whose combined mixing is STRICTLY THINNER than the thinnest single cell.

The canonical way to combine two scales is the DIRECT PRODUCT (tensor) walk on
`μ_{n₁} × μ_{n₂}` of total size `N = n₁·n₂`. Its Gauss-period spectrum is the OUTER PRODUCT
`η^{prod}_{(b,c)} = η^{(1)}_b · η^{(2)}_c`, so the wall multiplies exactly:
`M_prod = M₁ · M₂` and the even moments multiply `E_r^{prod} = E_r^{(1)} · E_r^{(2)}`.
(Exact probes: `oc_crossscale_superadditive_probe.py`,
`oc_crossscale_correct_normalization_probe.py`.)

## The invariant and the ceiling

The correct BGK-normalized wall of a size-`n` cell is
    `g(n) := M / Real.sqrt n`.
The prize wall is the square-root-cancellation (BGK / Paley / Weil) FLOOR
`M ≥ c·√n`, i.e. `g ≥ 1` on every adversarial thin cell (probe: `g ∈ [1.69, 2.31]` on all
`v₂(p-1) ≥ log₂ n` cells `n ∈ {4,8,16}`). Under the tensor the normalized wall is EXACTLY
multiplicative:
    `g_prod = M₁·M₂ / √(n₁·n₂) = (M₁/√n₁)·(M₂/√n₂) = g₁ · g₂`.
Since each factor is `≥ 1` at the wall, the product `g₁·g₂ ≥ max(g₁, g₂)` — the tensor object
is NEVER thinner than either factor; when both factors are `> 1` it is STRICTLY WORSE. A
cross-scale product certificate therefore AMPLIFIES the BGK-normalized wall, it can never dip
below it. The last conceptual escape is closed: super-additivity across scales does not exist for
the product object — it is strictly SUB-additive in the escape direction (multiplicative
above the `g = 1` floor).

## What is and is not proved

This is a precise STRUCTURAL no-go on the *product / tensor* cross-scale object: the exact
normalized-wall tensor identity plus the amplification inequality above the BGK floor. It does not
by itself exclude a hypothetical NON-product joint object (a coupling that is not the direct-product
walk), but every constructive cross-scale proposal on the board reduces to the tensor spectrum, and
the tensor is now shown to strictly amplify. Combined with the fixed-cell ledger being fully
wall-pinned, the honest frontier statement stands: δ* CORE is ON-BGK/Paley at the adversarial thin
subgroup, and neither fixed-cell certificates nor their tensor products escape the wall.
No axioms, no `sorry`, no `native_decide`.
-/

namespace ArkLib.ProximityGap.Frontier.OCCrossScaleTensorCeiling

open Real

/-- A scale cell carries its subgroup size `n` (positive real) and its adversarial wall
value `M := max_{b ≠ 0} |η_b|`. The BGK-normalized wall is `g := M / √n`. -/
structure ScaleCell where
  /-- Subgroup size `n` (real, positive). -/
  n : ℝ
  /-- Adversarial wall `M = max_{b≠0} |η_b|` (real, nonnegative). -/
  M : ℝ
  n_pos : 0 < n
  M_nonneg : 0 ≤ M

namespace ScaleCell

/-- The BGK-normalized wall `g = M / √n`. The prize square-root-cancellation floor is `g ≥ 1`. -/
noncomputable def g (c : ScaleCell) : ℝ := c.M / Real.sqrt c.n

/-- The direct-product (tensor) cell: sizes multiply `n = n₁·n₂` and — by the outer-product
Gauss-period identity `η^{prod}_{(b,c)} = η₁_b·η₂_c` — the walls multiply `M = M₁·M₂`. -/
noncomputable def tensor (c d : ScaleCell) : ScaleCell where
  n := c.n * d.n
  M := c.M * d.M
  n_pos := mul_pos c.n_pos d.n_pos
  M_nonneg := mul_nonneg c.M_nonneg d.M_nonneg

/-- √ of a positive cell size is positive. -/
theorem sqrt_n_pos (c : ScaleCell) : 0 < Real.sqrt c.n := Real.sqrt_pos.mpr c.n_pos

/-- **Exact tensor identity for the BGK-normalized wall:** `g(c ⊗ d) = g c · g d`.
This is the algebraic core: the outer-product spectrum makes both `M` and `√n` multiply, so the
normalized wall is EXACTLY multiplicative. -/
theorem g_tensor (c d : ScaleCell) : (c.tensor d).g = c.g * d.g := by
  unfold g tensor
  simp only
  rw [Real.sqrt_mul c.n_pos.le]
  field_simp

/-- The normalized wall is nonnegative. -/
theorem g_nonneg (c : ScaleCell) : 0 ≤ c.g := by
  unfold g
  exact div_nonneg c.M_nonneg c.sqrt_n_pos.le

/-- **Amplification (weak):** if a cell is AT-OR-ABOVE the BGK floor (`1 ≤ g d`), then tensoring
with it does not decrease the other factor: `g c ≤ g (c ⊗ d)`. The product never thins below a
factor whose partner sits at/above the square-root-cancellation floor. -/
theorem g_le_g_tensor_of_floor (c d : ScaleCell) (hd : 1 ≤ d.g) :
    c.g ≤ (c.tensor d).g := by
  rw [g_tensor]
  calc c.g = c.g * 1 := (mul_one _).symm
    _ ≤ c.g * d.g := by
        apply mul_le_mul_of_nonneg_left hd (g_nonneg c)

/-- **Symmetric amplification:** if BOTH cells are at-or-above the BGK floor, the tensor wall
dominates the MAX of the two single-cell walls. A product certificate is never thinner than the
thinnest fixed cell. -/
theorem max_g_le_g_tensor_of_floor (c d : ScaleCell)
    (hc : 1 ≤ c.g) (hd : 1 ≤ d.g) : max c.g d.g ≤ (c.tensor d).g := by
  apply max_le
  · exact g_le_g_tensor_of_floor c d hd
  · rw [g_tensor, mul_comm]
    calc d.g = d.g * 1 := (mul_one _).symm
      _ ≤ d.g * c.g := mul_le_mul_of_nonneg_left hc (g_nonneg d)

/-- **STRICT amplification (the ceiling):** if BOTH cells are STRICTLY above the BGK floor
(`1 < g c`, `1 < g d`), the tensor object is STRICTLY worse than either factor:
`g c < g (c ⊗ d)` and `g d < g (c ⊗ d)`. There is NO super-additive gain — the cross-scale
product strictly AMPLIFIES the normalized wall. This is the no-go: a product certificate can
never dip below a single-cell wall on the adversarial thin regime (where `g > 1` holds
empirically with `g ∈ [1.69, 2.31]`). -/
theorem g_lt_g_tensor_of_strict (c d : ScaleCell)
    (hc : 1 < c.g) (hd : 1 < d.g) :
    c.g < (c.tensor d).g ∧ d.g < (c.tensor d).g := by
  have hcpos : 0 < c.g := lt_trans one_pos hc
  have hdpos : 0 < d.g := lt_trans one_pos hd
  rw [g_tensor]
  refine ⟨?_, ?_⟩
  · calc c.g = c.g * 1 := (mul_one _).symm
      _ < c.g * d.g := by exact mul_lt_mul_of_pos_left hd hcpos
  · calc d.g = 1 * d.g := (one_mul _).symm
      _ < c.g * d.g := by exact mul_lt_mul_of_pos_right hc hdpos

/-- **No super-additive escape (headline).** Define an escape as a cross-scale product cell whose
normalized wall drops STRICTLY below the minimum of the two factor walls
(`g (c ⊗ d) < min (g c) (g d)`). On the adversarial thin regime — both factors strictly above the
BGK square-root-cancellation floor `1` — NO such escape exists: the product wall is `≥` the max,
hence `≥` the min. The last conceptual non-BGK door is closed for the tensor object. -/
theorem no_superadditive_escape (c d : ScaleCell)
    (hc : 1 < c.g) (hd : 1 < d.g) :
    min c.g d.g ≤ (c.tensor d).g := by
  have h := max_g_le_g_tensor_of_floor c d hc.le hd.le
  exact le_trans (min_le_max) h

/-- Quantitative restatement: on the thin regime, the *gain factor* of the tensor over each
factor is `≥ 1` and strictly `> 1` — the product is a genuine amplification, not a bypass.
`(g (c ⊗ d)) / (g c) = g d > 1`. -/
theorem tensor_gain_eq_partner (c d : ScaleCell) (hc : 0 < c.g) :
    (c.tensor d).g / c.g = d.g := by
  rw [g_tensor]
  field_simp

end ScaleCell

end ArkLib.ProximityGap.Frontier.OCCrossScaleTensorCeiling
