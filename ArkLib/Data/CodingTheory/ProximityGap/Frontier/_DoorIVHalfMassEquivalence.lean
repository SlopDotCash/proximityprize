/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Door-(iv): the prize is equivalent to a worst-`b` half-mass `L¹` bound (#444)

Continuing the half-mass thread (`_DoorIVHalfMassFactorization`): write `M(n) = max_b ‖η_b‖` for the
prize object and `H(n) = max_b (‖A_b‖ + ‖B_b‖)` for the worst-`b` half-mass `L¹` of the index-2
coset-half split.  Two facts pin `M` and `H` to the same scale:

* `M ≤ H` **always** (coherence ≤ 1, i.e. `‖A+B‖ ≤ ‖A‖+‖B‖` pointwise, so the max transfers) —
  proven in `_DoorIVHalfMassFactorization.norm_le_halfMass`.
* `H ≤ C·M` for an absolute constant `C ≈ 1` (probe `probe_dooriv_halfmass_equiv.py`: `H/M = 1.00`
  at `n=16,64` full/near-full scan, `1.11` at `n=32` sampled; `H` and `M` coincide).

This file records the abstract **reduction**: under those two bounds, a prize-shaped bound on `M`
is equivalent (up to the constant `C`) to the same-shaped bound on `H`.  So the open door-(iv) target
can be **restated entirely in terms of the half-mass** `H(n)` — the citable reduction
`prize ⟺ H(n) = O(√(n·log(p/n)))`.

Scope: order arithmetic over `ℝ`.  No CORE/cancellation/capacity claim — this is the reduction wrapper,
with the analytic content (the bound on `H` itself) left open exactly as before.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

/-- **Half-mass dominates the prize** (the always-true direction): if `M ≤ H` and the half-mass `H` is
bounded by `C · scale`, then the prize `M` is bounded by `C · scale`. -/
theorem prizeBound_of_halfMassBound {M H C scale : ℝ}
    (hMH : M ≤ H) (hH : H ≤ C * scale) :
    M ≤ C * scale :=
  le_trans hMH hH

/-- **The prize bounds the half-mass up to the comparison constant** (the probed reverse): if
`H ≤ K · M` and the prize `M` is bounded by `C · scale`, then the half-mass is bounded by `K·C·scale`. -/
theorem halfMassBound_of_prizeBound {M H K C scale : ℝ}
    (hK : 0 ≤ K) (hHM : H ≤ K * M) (hM : M ≤ C * scale) :
    H ≤ (K * C) * scale := by
  have h1 : K * M ≤ K * (C * scale) := by gcongr
  have h2 : K * (C * scale) = (K * C) * scale := by ring
  exact le_trans hHM (h2 ▸ h1)

/-- **Prize ⟺ half-mass bound (up to constants).**  Given the always-true `M ≤ H` and the probed
reverse `H ≤ K·M` (`K ≈ 1`), the existence of an absolute prize constant is equivalent to the existence
of an absolute half-mass constant: a prize-shaped bound on `M` and the same-shaped bound on `H` imply
each other up to the factor `K`.  (Pointwise rung: for a single positive scale a `C` can be picked
trivially, so the genuine Big-O statement is the uniform-family form
`exists_prizeFamilyBound_iff_exists_halfMassFamilyBound` below, which fixes one constant across all `n`.) -/
theorem prizeBound_iff_halfMassBound {M H K scale : ℝ}
    (hMH : M ≤ H) (hHM : H ≤ K * M) (hK : 0 ≤ K) (_hscale : 0 < scale) :
    (∃ C, M ≤ C * scale) ↔ (∃ C, H ≤ C * scale) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨K * C, halfMassBound_of_prizeBound hK hHM hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, prizeBound_of_halfMassBound hMH hC⟩

/-- Quantitative envelope form: `M` and `H` are sandwiched `M ≤ H ≤ K·M`, so they are within the
factor `K` of each other — the half-mass is an equivalent target, not merely an upper envelope. -/
theorem prize_halfMass_sandwich {M H K : ℝ} (hMH : M ≤ H) (hHM : H ≤ K * M) :
    M ≤ H ∧ H ≤ K * M :=
  ⟨hMH, hHM⟩


/-- **Normalized half-mass corridor.**  At any positive prize scale, the pointwise sandwich
`M ≤ H ≤ K·M` transfers unchanged to the normalized ratios: the half-mass Shaw-value ratio is between
the prize ratio and `K` times the prize ratio.  Thus normalization by `√(n log(p/n))` does not create a
new lever; it preserves exactly the same comparison constant. -/
theorem normalized_prize_halfMass_sandwich {M H K scale : ℝ}
    (hscale : 0 < scale) (hMH : M ≤ H) (hHM : H ≤ K * M) :
    M / scale ≤ H / scale ∧ H / scale ≤ K * (M / scale) := by
  constructor
  · exact div_le_div_of_nonneg_right hMH (le_of_lt hscale)
  · have h1 : H / scale ≤ (K * M) / scale :=
      div_le_div_of_nonneg_right hHM (le_of_lt hscale)
    have h2 : (K * M) / scale = K * (M / scale) := by ring
    exact h2 ▸ h1

/-! ## Uniform-family form: the genuine absolute-constant (Big-O) reduction

The pointwise `prizeBound_iff_halfMassBound` above is, for a single positive scale, satisfiable by a
pointwise `C` and so does NOT by itself capture an absolute Big-O constant.  The family forms below
require ONE constant across the whole admissible index family `ι` (the fields / subgroup sizes), which
IS the `prize ⟺ H(n)=O(scale)` statement. -/

/-- A uniform prize-family bound: one constant `C` for every index. -/
def prizeFamilyBound {ι : Type*} (M scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i ≤ C * scale i

/-- A uniform half-mass-family bound: one constant `C` for every index. -/
def halfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, H i ≤ C * scale i


/-- A uniform normalized prize-family bound: one constant `C` bounds `M / scale` for every index.
This is the Shaw-value form of `prizeFamilyBound` when `scale = √(n log(p/n))`. -/
def normalizedPrizeFamilyBound {ι : Type*} (M scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i / scale i ≤ C

/-- A uniform normalized half-mass-family bound: one constant `C` bounds `H / scale` for every index. -/
def normalizedHalfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, H i / scale i ≤ C

/-- Quantified wall-witness form for normalized prize ratios: every proposed absolute constant is
beaten somewhere in the family.  This is the constructive-facing negation of bounded Shaw value. -/
def normalizedPrizeFamilyUnbounded {ι : Type*} (M scale : ι → ℝ) : Prop :=
  ∀ C : ℝ, ∃ i, C < M i / scale i

/-- Quantified wall-witness form for normalized half-mass ratios: every proposed absolute constant is
beaten somewhere in the family. -/
def normalizedHalfMassFamilyUnbounded {ι : Type*} (H scale : ι → ℝ) : Prop :=
  ∀ C : ℝ, ∃ i, C < H i / scale i

/-- The negation of a bounded normalized prize-family constant is exactly the quantified
counterexample form `∀ C, ∃ i, C < M i / scale i`.  No asymptotics or arithmetic estimate is hidden;
this is only order logic over the normalized ratios. -/
theorem not_exists_normalizedPrizeFamilyBound_iff_normalizedPrizeFamilyUnbounded {ι : Type*}
    {M scale : ι → ℝ} :
    (¬ ∃ C, normalizedPrizeFamilyBound M scale C) ↔
      normalizedPrizeFamilyUnbounded M scale := by
  constructor
  · intro h C
    by_contra hnone
    have hbound : normalizedPrizeFamilyBound M scale C := by
      intro i
      exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    exact h ⟨C, hbound⟩
  · intro hun h
    rcases h with ⟨C, hC⟩
    rcases hun C with ⟨i, hi⟩
    exact (not_lt_of_ge (hC i)) hi

/-- The negation of a bounded normalized half-mass-family constant is exactly the quantified
counterexample form `∀ C, ∃ i, C < H i / scale i`. -/
theorem not_exists_normalizedHalfMassFamilyBound_iff_normalizedHalfMassFamilyUnbounded {ι : Type*}
    {H scale : ι → ℝ} :
    (¬ ∃ C, normalizedHalfMassFamilyBound H scale C) ↔
      normalizedHalfMassFamilyUnbounded H scale := by
  constructor
  · intro h C
    by_contra hnone
    have hbound : normalizedHalfMassFamilyBound H scale C := by
      intro i
      exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    exact h ⟨C, hbound⟩
  · intro hun h
    rcases h with ⟨C, hC⟩
    rcases hun C with ⟨i, hi⟩
    exact (not_lt_of_ge (hC i)) hi

/-- Direct normalized transfer from prize to half-mass: if the normalized prize ratios are bounded
by `C`, then the normalized half-mass ratios are bounded by `K*C` under the comparison `H ≤ K*M`.
This is the named constant-tracking rung behind the Shaw-value reduction. -/
theorem normalizedHalfMassFamilyBound_of_normalizedPrizeFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K C : ℝ} (hK : 0 ≤ K) (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i)
    (hC : normalizedPrizeFamilyBound M scale C) :
    normalizedHalfMassFamilyBound H scale (K * C) := by
  intro i
  have h1 : H i / scale i ≤ K * (M i / scale i) :=
    (normalized_prize_halfMass_sandwich (hscale i) (hMH i) (hHM i)).2
  have h2 : K * (M i / scale i) ≤ K * C :=
    mul_le_mul_of_nonneg_left (hC i) hK
  exact le_trans h1 h2

/-- Direct normalized transfer from half-mass to prize: the always-true comparison `M ≤ H` sends any
normalized half-mass bound with constant `C` to the same normalized prize bound.  This is the easy
half of the Door-IV half-mass equivalence. -/
theorem normalizedPrizeFamilyBound_of_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {C : ℝ} (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hC : normalizedHalfMassFamilyBound H scale C) :
    normalizedPrizeFamilyBound M scale C := by
  intro i
  have h1 : M i / scale i ≤ H i / scale i :=
    div_le_div_of_nonneg_right (hMH i) (le_of_lt (hscale i))
  exact le_trans h1 (hC i)

/-- **Normalized uniform-family half-mass reduction.**  Under one family-wide comparison constant
`K` and positive scales, bounded normalized prize ratios are equivalent to bounded normalized half-mass
ratios.  This is the Shaw-value version of
`exists_prizeFamilyBound_iff_exists_halfMassFamilyBound`: normalization by the prize scale preserves
the exact same door-(iv) reduction and adds no hidden analytic lever. -/
theorem exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, normalizedPrizeFamilyBound M scale C) ↔
      (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨K * C, normalizedHalfMassFamilyBound_of_normalizedPrizeFamilyBound
      hK hscale hMH hHM hC⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    have h1 : M i / scale i ≤ H i / scale i :=
      (normalized_prize_halfMass_sandwich (hscale i) (hMH i) (hHM i)).1
    exact le_trans h1 (hC i)

/-- Raw prize-family bounds are equivalent to normalized prize-ratio bounds under positive scales,
with the same constant.  This is the scale-generic analogue of the Shaw-value normalization. -/
theorem prizeFamilyBound_iff_normalizedPrizeFamilyBound {ι : Type*} {M scale : ι → ℝ} {C : ℝ}
    (hscale : ∀ i, 0 < scale i) :
    prizeFamilyBound M scale C ↔ normalizedPrizeFamilyBound M scale C := by
  constructor
  · intro h i
    have hdiv : M i / scale i ≤ (C * scale i) / scale i :=
      div_le_div_of_nonneg_right (h i) (le_of_lt (hscale i))
    have hrewrite : (C * scale i) / scale i = C := by
      rw [mul_div_cancel_right₀ C (ne_of_gt (hscale i))]
    exact hrewrite ▸ hdiv
  · intro h i
    calc
      M i = (M i / scale i) * scale i := by
        rw [div_mul_cancel₀ (M i) (ne_of_gt (hscale i))]
      _ ≤ C * scale i := mul_le_mul_of_nonneg_right (h i) (le_of_lt (hscale i))

/-- Raw half-mass-family bounds are equivalent to normalized half-mass-ratio bounds under positive
scales, with the same constant. -/
theorem halfMassFamilyBound_iff_normalizedHalfMassFamilyBound {ι : Type*} {H scale : ι → ℝ} {C : ℝ}
    (hscale : ∀ i, 0 < scale i) :
    halfMassFamilyBound H scale C ↔ normalizedHalfMassFamilyBound H scale C := by
  constructor
  · intro h i
    have hdiv : H i / scale i ≤ (C * scale i) / scale i :=
      div_le_div_of_nonneg_right (h i) (le_of_lt (hscale i))
    have hrewrite : (C * scale i) / scale i = C := by
      rw [mul_div_cancel_right₀ C (ne_of_gt (hscale i))]
    exact hrewrite ▸ hdiv
  · intro h i
    calc
      H i = (H i / scale i) * scale i := by
        rw [div_mul_cancel₀ (H i) (ne_of_gt (hscale i))]
      _ ≤ C * scale i := mul_le_mul_of_nonneg_right (h i) (le_of_lt (hscale i))

/-- **Uniform-family door-(iv) reduction (the Big-O statement).**  Given, over the whole index family,
the always-true `M i ≤ H i` and the probed reverse `H i ≤ K · M i` with a SINGLE constant `K ≥ 0`, the
existence of an absolute prize constant is equivalent to the existence of an absolute half-mass
constant.  This is the honest `prize ⇔ H(n)=O(scale)`: one constant for all `n`, not pointwise. -/
theorem exists_prizeFamilyBound_iff_exists_halfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, prizeFamilyBound M scale C) ↔ (∃ C, halfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K * C, fun i => ?_⟩
    exact halfMassBound_of_prizeBound hK (hHM i) (hC i)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact prizeBound_of_halfMassBound (hMH i) (hC i)

/-- **Prize Shaw-value normalization.**  With positive scales, the raw prize Big-O statement
`M ≤ C·scale` is equivalent to bounded normalized prize Shaw value `M/scale ≤ C`, with the same
constant.  This packages the existential `Sh_M(n)=O(1)` form used by the door-(iv) reductions. -/
theorem exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (∃ C, prizeFamilyBound M scale C) ↔
      (∃ C, normalizedPrizeFamilyBound M scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (prizeFamilyBound_iff_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (prizeFamilyBound_iff_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).2 hC⟩

/-- **Half-mass Shaw-value normalization.**  With positive scales, the raw half-mass Big-O statement
`H ≤ C·scale` is equivalent to bounded normalized half-mass Shaw value `H/scale ≤ C`, with the same
constant.  This is the pure half-mass `H(n)=O(scale) ⇔ Sh_H(n)=O(1)` conversion used by the mixed
capstone below. -/
theorem exists_halfMassFamilyBound_iff_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (∃ C, halfMassFamilyBound H scale C) ↔
      (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (halfMassFamilyBound_iff_normalizedHalfMassFamilyBound
      (H := H) (scale := scale) hscale).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (halfMassFamilyBound_iff_normalizedHalfMassFamilyBound
      (H := H) (scale := scale) hscale).2 hC⟩

/-- **Mixed Shaw-value capstone.**  Under the same family-wide half-mass comparison and positive prize
scale, a raw uniform prize Big-O bound is equivalent to a bounded normalized half-mass Shaw-value.
This is the directly citable form `prize bound ⇔ Sh_H(n)=O(1)`: the left side is the original
`M ≤ C·scale`, while the right side is the normalized door-(iv) half-mass ratio `H/scale ≤ C`. -/
theorem exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, prizeFamilyBound M scale C) ↔
      (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    have hNormM : normalizedPrizeFamilyBound M scale C :=
      (prizeFamilyBound_iff_normalizedPrizeFamilyBound (M := M) (scale := scale) hscale).1 hC
    exact (exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
      (M := M) (H := H) (scale := scale) hK hscale hMH hHM).1 ⟨C, hNormM⟩
  · intro hNormH
    rcases (exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
      (M := M) (H := H) (scale := scale) hK hscale hMH hHM).2 hNormH with ⟨C, hNormM⟩
    exact ⟨C, (prizeFamilyBound_iff_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).2 hNormM⟩

/-- **Reverse mixed Shaw-value capstone.**  Under the same family-wide half-mass comparison and
positive prize scale, a raw uniform half-mass Big-O bound is equivalent to a bounded normalized prize
Shaw-value.  Together with `exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound`, this
closes the four-way reduction surface between raw prize, raw half-mass, normalized prize, and
normalized half-mass bounds.  The statement is only a reduction/renormalization: the analytic
half-mass or prize cancellation estimate remains exactly the open door-(iv) problem. -/
theorem exists_halfMassFamilyBound_iff_exists_normalizedPrizeFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, halfMassFamilyBound H scale C) ↔
      (∃ C, normalizedPrizeFamilyBound M scale C) := by
  constructor
  · intro hHalf
    rcases (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
      (M := M) (H := H) (scale := scale) hK hMH hHM).2 hHalf with ⟨C, hPrize⟩
    exact ⟨C, (prizeFamilyBound_iff_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).1 hPrize⟩
  · intro hNormPrize
    rcases (exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).2 hNormPrize with ⟨C, hPrize⟩
    exact (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
      (M := M) (H := H) (scale := scale) hK hMH hHM).1 ⟨C, hPrize⟩

/-- **Four-way door-(iv) bound capstone.**  Under one family-wide half-mass comparison and positive
scales, the original raw prize Big-O statement is equivalent to the simultaneous availability of all
three normalized/half-mass reformulations: raw half-mass, normalized prize Shaw value, and normalized
half-mass Shaw value.  This is a packaging theorem only; the analytic input remains the comparison
`M≤H≤K·M` and the still-open door-(iv) cancellation bound. -/
theorem prizeFamilyBound_iff_all_halfMassShaw_forms {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, prizeFamilyBound M scale C) ↔
      (∃ C, halfMassFamilyBound H scale C) ∧
        (∃ C, normalizedPrizeFamilyBound M scale C) ∧
          (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · intro hPrize
    have hHalf : ∃ C, halfMassFamilyBound H scale C :=
      (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
        (M := M) (H := H) (scale := scale) hK hMH hHM).1 hPrize
    have hNormPrize : ∃ C, normalizedPrizeFamilyBound M scale C :=
      (exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
        (M := M) (scale := scale) hscale).1 hPrize
    have hNormHalf : ∃ C, normalizedHalfMassFamilyBound H scale C :=
      (exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
        (M := M) (H := H) (scale := scale) hK hscale hMH hHM).1 hPrize
    exact ⟨hHalf, hNormPrize, hNormHalf⟩
  · intro hAll
    exact (exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
      (M := M) (scale := scale) hscale).2 hAll.2.1


/-- **Symmetric four-way door-(iv) bound capstone.**  Under the same family-wide half-mass
comparison and positive scales, the raw half-mass Big-O statement is equivalent to the simultaneous
availability of the raw prize bound and both normalized Shaw-value formulations.  This is the
half-mass-oriented companion to `prizeFamilyBound_iff_all_halfMassShaw_forms`; it is still only a
packaging theorem, with the analytic cancellation estimate left exactly open. -/
theorem halfMassFamilyBound_iff_all_prizeShaw_forms {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, halfMassFamilyBound H scale C) ↔
      (∃ C, prizeFamilyBound M scale C) ∧
        (∃ C, normalizedPrizeFamilyBound M scale C) ∧
          (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · intro hHalf
    have hPrize : ∃ C, prizeFamilyBound M scale C :=
      (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
        (M := M) (H := H) (scale := scale) hK hMH hHM).2 hHalf
    have hNormPrize : ∃ C, normalizedPrizeFamilyBound M scale C :=
      (exists_halfMassFamilyBound_iff_exists_normalizedPrizeFamilyBound
        (M := M) (H := H) (scale := scale) hK hscale hMH hHM).1 hHalf
    have hNormHalf : ∃ C, normalizedHalfMassFamilyBound H scale C :=
      (exists_halfMassFamilyBound_iff_exists_normalizedHalfMassFamilyBound
        (H := H) (scale := scale) hscale).1 hHalf
    exact ⟨hPrize, hNormPrize, hNormHalf⟩
  · intro hAll
    exact (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
      (M := M) (H := H) (scale := scale) hK hMH hHM).1 hAll.1

/-! ## Wall-side family reductions

The positive capstones above state the prize side (`∃ C`) as an equivalence.  The wall side is the
failure of those existential bounds.  These lemmas expose that failure directly so downstream door-(iv)
statements can cite `no prize constant ⇔ no half-mass constant` without unfolding negations by hand.
-/

/-- **Raw wall-side door-(iv) reduction.**  Under one family-wide half-mass comparison, failure of a
raw uniform prize Big-O bound is equivalent to failure of a raw uniform half-mass Big-O bound. This is
only the negated form of the already-proven positive reduction; it makes no arithmetic estimate. -/
theorem not_exists_prizeFamilyBound_iff_not_exists_halfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, prizeFamilyBound M scale C) ↔
      ¬ ∃ C, halfMassFamilyBound H scale C := by
  exact not_congr (exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hMH hHM)

/-- **Normalized wall-side door-(iv) reduction.**  With positive scales, failure of bounded normalized
prize Shaw values is equivalent to failure of bounded normalized half-mass Shaw values. This is the
wall form of `exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound`. -/
theorem not_exists_normalizedPrizeFamilyBound_iff_not_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, normalizedPrizeFamilyBound M scale C) ↔
      ¬ ∃ C, normalizedHalfMassFamilyBound H scale C := by
  exact not_congr (exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM)

/-- **Mixed wall-side capstone.**  With positive scales and the family-wide half-mass comparison,
failure of a raw uniform prize Big-O bound is equivalent to failure of bounded normalized half-mass
Shaw value. This is the negative form of the citable `prize ⇔ Sh_H(n)=O(1)` reduction. -/
theorem not_exists_prizeFamilyBound_iff_not_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, prizeFamilyBound M scale C) ↔
      ¬ ∃ C, normalizedHalfMassFamilyBound H scale C := by
  exact not_congr (exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM)

/-- **Symmetric mixed wall-side capstone.**  With positive scales and the family-wide half-mass
comparison, failure of a raw uniform half-mass Big-O bound is equivalent to failure of bounded
normalized prize Shaw value.  This is the negative form of
`exists_halfMassFamilyBound_iff_exists_normalizedPrizeFamilyBound` and closes the mixed wall API in
the opposite direction. -/
theorem not_exists_halfMassFamilyBound_iff_not_exists_normalizedPrizeFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ ∃ C, halfMassFamilyBound H scale C) ↔
      ¬ ∃ C, normalizedPrizeFamilyBound M scale C := by
  exact not_congr (exists_halfMassFamilyBound_iff_exists_normalizedPrizeFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM)

/-- **Quantified wall-witness half-mass reduction.**  Under the family-wide comparison
`M≤H≤K·M`, unbounded normalized prize Shaw ratios are equivalent to unbounded normalized half-mass
Shaw ratios in the concrete `∀ C, ∃ i, C < ratio i` sense.  This is the witness-producing wall form of
`prize ⇔ Sh_H(n)=O(1)`: if no absolute constant bounds one normalized ratio, then every proposed
constant is beaten by the other as well.  It is a reduction only; it proves no cancellation estimate. -/
theorem normalizedPrizeFamilyUnbounded_iff_normalizedHalfMassFamilyUnbounded {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    normalizedPrizeFamilyUnbounded M scale ↔
      normalizedHalfMassFamilyUnbounded H scale := by
  rw [← not_exists_normalizedPrizeFamilyBound_iff_normalizedPrizeFamilyUnbounded,
    ← not_exists_normalizedHalfMassFamilyBound_iff_normalizedHalfMassFamilyUnbounded]
  exact not_exists_normalizedPrizeFamilyBound_iff_not_exists_normalizedHalfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM

end ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeBound_of_halfMassBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassBound_of_prizeBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeBound_iff_halfMassBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prize_halfMass_sandwich
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalized_prize_halfMass_sandwich
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound_iff_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_normalizedPrizeFamilyBound_iff_normalizedPrizeFamilyUnbounded
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_normalizedHalfMassFamilyBound_iff_normalizedHalfMassFamilyUnbounded
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound_of_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound_of_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_halfMassFamilyBound_iff_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_halfMassFamilyBound_iff_exists_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_all_halfMassShaw_forms
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound_iff_all_prizeShaw_forms
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_prizeFamilyBound_iff_not_exists_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_normalizedPrizeFamilyBound_iff_not_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_prizeFamilyBound_iff_not_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.not_exists_halfMassFamilyBound_iff_not_exists_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyUnbounded_iff_normalizedHalfMassFamilyUnbounded
