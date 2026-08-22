/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import Mathlib.Tactic

/-!
# The subgroup Gauss-sum SIXTH MOMENT = `q · E₃(G)` (next rung of the moment ladder, #357/#389)

The second moment of `η_b = ∑_{y∈G} ψ(b·y)` is `q·|G|` and the fourth is `q·E(G)` (the additive
energy). This file supplies the **sixth** moment — the next rung — which is `q` times the **3-fold
additive energy**

> `subgroup_gaussSum_sixthMoment`:  `∑_{b∈F} ‖η_b‖⁶ = q · E₃(G)`,

where `E₃(G) = #{(y₁,…,y₆) ∈ G⁶ : y₁+y₂+y₃ = y₄+y₅+y₆}`. Pure additive-character orthogonality
(Parseval), **no Weil**: writing `η_b³ = ∑_{y₁,y₂,y₃∈G} ψ(b(y₁+y₂+y₃))` and applying the same
second-moment collapse to the cube `‖η_b‖⁶ = ‖η_b³‖²` sends each sextuple to `q·[y₁+y₂+y₃ = y₄+y₅+y₆]`.

**Why it matters (the anti-concentration ladder).** The known count bound is
`#{b : ‖η_b‖² ≥ q} ≤ min(|G|, E(G)/q)` (second + fourth moment). Markov on the sixth moment adds
`#{b : ‖η_b‖² ≥ q} ≤ E₃(G)/q²`, and with the trivial `E₃(G) ≤ |G|⁵` this is `≤ |G|⁵/q²` — strictly
sharper than the fourth-moment `E(G)/q ≤ |G|³/q` exactly when `|G|² < q`. So the rung at which *no*
frequency reaches the Johnson scale moves from `|G| < q^{1/3}` (fourth moment) to `|G| < q^{2/5}`
(sixth moment); the full moment ladder pushes this threshold to `|G| < q^{1/2}`. This is an
average/count statement only — it does NOT touch the per-frequency worst case (the open core); it
sharpens the regime in which the moment method already gives sub-Johnson behaviour.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **3-fold additive energy** of a finite set `G`: the number of sextuples
`(y₁,…,y₆) ∈ G⁶` with `y₁ + y₂ + y₃ = y₄ + y₅ + y₆`. -/
def addEnergy3 (G : Finset F) : ℕ :=
  ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G,
    (if y₁ + y₂ + y₃ = y₄ + y₅ + y₆ then 1 else 0)

/-- The cube of the subgroup Gauss sum is the triple character sum over `G³`:
`η_b³ = ∑_{y₁,y₂,y₃∈G} ψ(b·(y₁+y₂+y₃))`. -/
theorem eta_cube_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    (eta ψ G b) ^ 3 = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ψ (b * (y₁ + y₂ + y₃)) := by
  simp only [eta]
  rw [show (∑ y ∈ G, ψ (b * y)) ^ 3
        = (∑ y ∈ G, ψ (b * y)) * ((∑ y ∈ G, ψ (b * y)) * (∑ y ∈ G, ψ (b * y))) from by ring]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y₃ _ => ?_)
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1; ring

/-- The complex conjugate of the cube: `conj(η_b³) = ∑_{z₁,z₂,z₃∈G} ψ(-(b·(z₁+z₂+z₃)))`. -/
theorem conj_eta_cube_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    (starRingEnd ℂ) ((eta ψ G b) ^ 3)
      = ∑ z₁ ∈ G, ∑ z₂ ∈ G, ∑ z₃ ∈ G, ψ (-(b * (z₁ + z₂ + z₃))) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [eta_cube_eq]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun z₁ _ => Finset.sum_congr rfl (fun z₂ _ =>
    Finset.sum_congr rfl (fun z₃ _ => ?_)))
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]

/-- **The subgroup Gauss-sum sixth moment equals `q · E₃(G)`.** Pure orthogonality (Parseval); no
Weil. The sixth moment of `η_b` is `q` times the 3-fold additive energy of `G`. -/
theorem subgroup_gaussSum_sixthMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6 = (Fintype.card F : ℝ) * addEnergy3 G := by
  -- `‖η_b‖⁶ = ‖η_b³‖²`, expand as `η_b³ · conj(η_b³)`, sum over `b`, collapse by orthogonality.
  have hnorm : ∀ b : F, (eta ψ G b) ^ 3 * (starRingEnd ℂ) ((eta ψ G b) ^ 3)
      = ((‖eta ψ G b‖ ^ 6 : ℝ) : ℂ) := by
    intro b
    have hww : (eta ψ G b) ^ 3 * (starRingEnd ℂ) ((eta ψ G b) ^ 3)
        = ((‖(eta ψ G b) ^ 3‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hww, norm_pow]
    push_cast
    ring
  have hcomplex : (∑ b : F, (eta ψ G b) ^ 3 * (starRingEnd ℂ) ((eta ψ G b) ^ 3))
      = (Fintype.card F : ℂ) * addEnergy3 G := by
    calc ∑ b : F, (eta ψ G b) ^ 3 * (starRingEnd ℂ) ((eta ψ G b) ^ 3)
        = ∑ b : F, (∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ψ (b * (y₁ + y₂ + y₃)))
            * (∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G, ψ (-(b * (y₄ + y₅ + y₆)))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [conj_eta_cube_eq, eta_cube_eq]
      _ = ∑ b : F, ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G,
            ψ (b * ((y₁ + y₂ + y₃) - (y₄ + y₅ + y₆))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          -- pull the left triple-sum out (sum_mul ×3), then push into the right (mul_sum ×3)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun y₁ _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun y₂ _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun y₃ _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y₄ _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y₅ _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y₆ _ => ?_)
          rw [← AddChar.map_add_eq_mul]
          congr 1; ring
      _ = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G, ∑ b : F,
            ψ (b * ((y₁ + y₂ + y₃) - (y₄ + y₅ + y₆))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₁ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₂ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₃ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₄ _ => ?_)
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y₅ _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G,
            (if y₁ + y₂ + y₃ = y₄ + y₅ + y₆ then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
            Finset.sum_congr rfl (fun y₃ _ => Finset.sum_congr rfl (fun y₄ _ =>
              Finset.sum_congr rfl (fun y₅ _ => Finset.sum_congr rfl (fun y₆ _ => ?_))))))
          rw [AddChar.sum_mulShift ((y₁ + y₂ + y₃) - (y₄ + y₅ + y₆)) hψ]
          have hcond : ((y₁ + y₂ + y₃) - (y₄ + y₅ + y₆) = 0)
              ↔ (y₁ + y₂ + y₃ = y₄ + y₅ + y₆) := sub_eq_zero
          simp only [hcond]
          split <;> simp
      _ = (Fintype.card F : ℂ) * addEnergy3 G := by
          rw [addEnergy3]
          push_cast
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
            Finset.sum_congr rfl (fun y₃ _ => Finset.sum_congr rfl (fun y₄ _ =>
              Finset.sum_congr rfl (fun y₅ _ => Finset.sum_congr rfl (fun y₆ _ => ?_))))))
          split <;> simp
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ 6 : ℝ) : ℂ) = (Fintype.card F : ℂ) * addEnergy3 G := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => (hnorm b).symm)
  have hfin : ((∑ b : F, ‖eta ψ G b‖ ^ 6 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * addEnergy3 G : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hfin

omit [Fintype F] in
/-- **The 3-fold additive energy is at most `|G|⁵`** (five free coordinates determine the sixth at
most once). The trivial upper bound that drives the sharpened anti-concentration threshold. -/
theorem addEnergy3_le_pow (G : Finset F) : addEnergy3 G ≤ G.card ^ 5 := by
  rw [addEnergy3]
  calc ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, ∑ y₆ ∈ G,
        (if y₁ + y₂ + y₃ = y₄ + y₅ + y₆ then 1 else 0)
      ≤ ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G, ∑ y₅ ∈ G, (1 : ℕ) := by
        refine Finset.sum_le_sum (fun y₁ _ => Finset.sum_le_sum (fun y₂ _ =>
          Finset.sum_le_sum (fun y₃ _ => Finset.sum_le_sum (fun y₄ _ =>
            Finset.sum_le_sum (fun y₅ _ => ?_)))))
        -- inner sum over `y₆` is the cardinality of a filter whose predicate pins `y₆`, hence ≤ 1
        rw [Finset.sum_boole]
        have hle1 : (G.filter (fun y₆ => y₁ + y₂ + y₃ = y₄ + y₅ + y₆)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha bb hbb
          simp only [Finset.mem_filter] at ha hbb
          have : y₄ + y₅ + a = y₄ + y₅ + bb := by rw [← ha.2, ← hbb.2]
          exact add_left_cancel this
        exact_mod_cast hle1
  _ = G.card ^ 5 := by
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        ring

end ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.subgroup_gaussSum_sixthMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSixthMoment.addEnergy3_le_pow
