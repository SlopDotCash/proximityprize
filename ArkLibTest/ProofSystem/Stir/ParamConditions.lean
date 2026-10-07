/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import ArkLib.ProofSystem.Stir.MainThm

/-!
# STIR parameter consistency

The corrected conditions admit a concrete zero-transition instance over `ZMod 5`,
with degree two and a four-point smooth domain. The last repetition count remains
unconstrained. Negative controls reject a domain no larger than its degree and a
non-power-of-two initial degree. These are parameter checks, not STIR soundness proofs.

Adapted from upstream ArkLib PR #1291.
-/

open NNReal ReedSolomon LinearCode STIR StirIOP

namespace ArkLibTest.StirMainThm

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The four units of `ZMod 5`, as an embedding of `Fin 4`. -/
private def units : Fin 4 ↪ ZMod 5 := ⟨fun i => ((i : ℕ) + 1 : ZMod 5), by decide⟩

/-- The units of `ZMod 5` form a smooth domain: all of the group `(ZMod 5)ˣ`, of order `4 = 2²`. -/
private instance smoothUnits : Smooth units where
  H := ⊤
  a := 1
  h_coset := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Subgroup.coe_top, Units.val_one, one_mul]
    revert x
    decide
  h_card_pow2 := ⟨2, by simp⟩

/-- The domains of the `M = 0` instance. -/
private abbrev domains : Fin (0 + 1) → Type := fun _ => Fin 4

/-- Parameters with `M = 0`: initial degree `2`, folding parameter `2`, and a repetition parameter
`100`, larger than every degree (the last repetition parameter is not constrained). -/
private def params : Params domains (ZMod 5) where
  deg := 2
  foldingParam := fun _ => 2
  φ := fun _ => units
  repeatParam := fun _ => 100

/-- Before any fold the degree is the initial degree (`degree_zero`). -/
example : degree domains params 0 = 2 := degree_zero domains params

private lemma degree_zero_eq : degree domains params 0 = 2 := degree_zero domains params

/-- The parameters of the `M = 0` instance satisfy the conditions of Construction 5.2. -/
private def conditions : ParamConditions domains params where
  h_deg := ⟨1, rfl⟩
  h_foldingParams := fun _ => ⟨1, rfl⟩
  h_deg_ge := by simp [params]
  h_smooth := fun _ => smoothUnits
  h_smooth_lt := fun i => by
    have : i = 0 := Fin.fin_one_eq_zero i
    subst this
    rw [degree_zero_eq]
    simp
  h_repeatP_le := fun i => i.elim0

private noncomputable def dist : Distances 0 := ⟨fun _ => 1 / 4, fun _ => 1⟩

/-- The code `RS[F, ι₀, 2]` has no list-decodability requirement, since `M = 0`. -/
private noncomputable def codes : CodeParams domains params dist where
  C := fun i => code (params.φ i) (degree domains params i)
  h_code := fun _ => rfl
  h_listDecode := fun i hi => absurd (Fin.fin_one_eq_zero i) hi

private lemma rate_eq : rate (code (params.φ 0) (degree domains params 0)) = 1 / 2 := by
  rw [degree_zero_eq, rateOfLinearCode_eq_min_div]
  norm_num

/-- `δ₀ = 1/4 < 1 - B⋆(1/2) = 1 - √(1/2)`. -/
private lemma delta_zero_lt :
    dist.δ 0 < 1 - Bstar (rate (code (params.φ 0) (degree domains params 0))) := by
  rw [rate_eq]
  unfold Bstar dist
  have h : NNReal.sqrt ((1 / 2 : ℚ≥0) : ℝ≥0) < 3 / 4 := by
    have h34 : (3 / 4 : ℝ≥0) = NNReal.sqrt ((3 / 4) ^ 2) := (NNReal.sqrt_sq _).symm
    rw [h34, NNReal.sqrt_lt_sqrt]
    push_cast
    norm_num
  change (1 / 4 : ℝ≥0) < 1 - _
  rw [lt_tsub_iff_right]
  calc (1 / 4 : ℝ≥0) + NNReal.sqrt ((1 / 2 : ℚ≥0) : ℝ≥0) < 1 / 4 + 3 / 4 := by gcongr
    _ = 1 := by norm_num

/-- The hypotheses of `stir_rbr_soundness` are jointly satisfiable, for `M = 0`: the conditions on
the parameters, the list-decodable codes, `0 < δ₀ < 1 - B⋆(ρ₀)`, and the (empty) conditions on
`δᵢ` for `0 < i ≤ M`. -/
theorem rbr_soundness_hypotheses_satisfiable :
    ∃ (P : Params domains (ZMod 5)) (Dist : Distances 0),
      Nonempty (ParamConditions domains P) ∧ Nonempty (CodeParams domains P Dist) ∧
      0 < Dist.δ 0 ∧
      Dist.δ 0 < 1 - Bstar (rate (code (P.φ 0) (degree domains P 0))) ∧
      ∀ {j : Fin (0 + 1)}, j ≠ 0 →
        0 < Dist.δ j ∧
        Dist.δ j < (1 - rate (code (P.φ j) (degree domains P j))
          - 1 / Fintype.card (domains j) : ℝ) ∧
        Dist.δ j < 1 - Bstar (rate (code (P.φ j) (degree domains P j))) :=
  ⟨params, dist, ⟨conditions⟩, ⟨codes⟩, by simp [dist], delta_zero_lt,
    fun hj => absurd (Fin.fin_one_eq_zero _) hj⟩

/-- The old condition `h_repeatP_le : tᵢ + 1 ≤ dᵢ` for every `i : Fin (M + 1)` would have rejected
the repetition parameter `100` of the last round, which Construction 5.2 does not constrain. -/
example : ¬ (params.repeatParam 0 + 1 ≤ degree domains params 0) := by
  rw [degree_zero_eq]
  simp [params]

/-- The reversed condition: a domain no larger than the degree is rejected by `ParamConditions`. -/
theorem not_paramConditions_of_card_le_degree {F : Type} [Field F] [DecidableEq F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] {P : Params ι F}
    (h : Fintype.card (ι 0) ≤ degree ι P 0) : ¬ Nonempty (ParamConditions ι P) :=
  fun ⟨hP⟩ => absurd (hP.h_smooth_lt 0) (not_lt.2 h)

/-- Why the old condition made Lemma 5.4 vacuous: if `|ι₀| ≤ d₀` the code has rate `1`, so
`1 - B⋆(ρ₀) = 0` and no `δ₀ : ℝ≥0` satisfies `δ₀ < 1 - B⋆(ρ₀)`. -/
theorem delta_zero_lt_false_of_card_le_degree {F : Type} [Field F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)] {P : Params ι F}
    (h : Fintype.card (ι 0) ≤ degree ι P 0) (δ₀ : ℝ≥0)
    (hδ₀ : δ₀ < 1 - Bstar (rate (code (P.φ 0) (degree ι P 0)))) : False := by
  have hpos : (Fintype.card (ι 0) : ℚ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι 0)).ne'
  have hrate : rate (code (P.φ 0) (degree ι P 0)) = 1 := by
    rw [rateOfLinearCode_eq_min_div, min_eq_right h]
    exact div_self hpos
  rw [hrate] at hδ₀
  simp [Bstar] at hδ₀

/-- The initial degree must be a power of 2: `3` is rejected. -/
theorem not_paramConditions_of_deg_eq_three {F : Type} [Field F] [DecidableEq F]
    {M : ℕ} {ι : Fin (M + 1) → Type} [∀ i, Fintype (ι i)] {P : Params ι F}
    (h : P.deg = 3) : ¬ Nonempty (ParamConditions ι P) := by
  rintro ⟨hP⟩
  obtain ⟨k, hk⟩ := hP.h_deg
  rw [h] at hk
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end ArkLibTest.StirMainThm
