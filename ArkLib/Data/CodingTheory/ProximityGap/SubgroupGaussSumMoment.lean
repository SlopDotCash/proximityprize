/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The general `2r`-th moment of the subgroup Gauss sum = `q · (r-fold additive energy)` (#389)

Generalizes `SubgroupGaussSumFourthMoment` (`r=2`): with `η_b = ∑_{y∈G} ψ(b·y)`,

> `∑_b ‖η_b‖^{2r} = q · E_r(G)`, `E_r(G) = #{(v,w) ∈ (Fin r → G)² : ∑v = ∑w}`.

The full moment↔energy correspondence: the `r`-fold additive energy (controlling the `r`-band
supply for δ\*) equals the `2r`-th moment of the incomplete character sum. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `r`-fold additive energy `E_r(G) = #{(v,w) ∈ (Fin r → G)² : ∑v = ∑w}`, as a nested
indicator sum. -/
noncomputable def rEnergy (G : Finset F) (r : ℕ) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
    (if ∑ i, v i = ∑ i, w i then 1 else 0)

/-- `∏_{i∈s} ψ(f i) = ψ(∑_{i∈s} f i)`. -/
theorem prod_addChar_eq {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ∏ i ∈ s, ψ (f i) = ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← AddChar.map_add_eq_mul]

/-- `η_b^r = ∑_{v : Fin r → G} ψ(b · ∑_i v i)`. -/
theorem eta_pow (ψ : AddChar F ℂ) (G : Finset F) (b : F) (r : ℕ) :
    eta ψ G b ^ r = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, v i) := by
  classical
  have h1 : eta ψ G b ^ r = ∏ _i : Fin r, (∑ y ∈ G, ψ (b * y)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rfl
  rw [h1, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [prod_addChar_eq, Finset.mul_sum]

/-- **The general `2r`-th moment: `∑_b ‖η_b‖^{2r} = q · E_r(G)`.** -/
theorem subgroup_gaussSum_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) :
    ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- conjugate of `η_b^r`
  have hconjpow : ∀ b : F, (starRingEnd ℂ) (eta ψ G b ^ r)
      = ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (-(b * ∑ i, w i)) := by
    intro b
    rw [eta_pow, map_sum]
    exact Finset.sum_congr rfl (fun w _ => hconj _)
  -- the complex identity
  have hcomplex : (∑ b : F, eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r))
      = (Fintype.card F : ℂ) * rEnergy G r := by
    calc ∑ b : F, eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r)
        = ∑ b : F, ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
              ψ (b * (∑ i, v i - ∑ i, w i)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hconjpow, eta_pow, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [← AddChar.map_add_eq_mul]
          congr 1
          ring
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ b : F,
              ψ (b * (∑ i, v i - ∑ i, w i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ w ∈ Fintype.piFinset (fun _ : Fin r => G),
              (if ∑ i, v i = ∑ i, w i then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [AddChar.sum_mulShift (∑ i, v i - ∑ i, w i) hψ]
          by_cases h : ∑ i, v i = ∑ i, w i <;> simp [h, sub_eq_zero]
      _ = (Fintype.card F : ℂ) * rEnergy G r := by
          simp only [rEnergy]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun w _ => ?_)
          by_cases h : ∑ i, v i = ∑ i, w i <;> simp [h]
  -- cast `‖η_b‖^{2r}` to the complex modulus power
  have hcast : ∀ b : F,
      ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ)
        = eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r) := by
    intro b
    rw [map_pow, ← mul_pow, RCLike.mul_conj, pow_mul]
    norm_cast
  have hfinal : ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * rEnergy G r := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => hcast b)
  have : ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * rEnergy G r : ℝ) : ℂ) := by
    rw [hfinal]; push_cast; ring
  exact_mod_cast this

end ArkLib.ProximityGap.SubgroupGaussSumMoment

#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.subgroup_gaussSum_moment
