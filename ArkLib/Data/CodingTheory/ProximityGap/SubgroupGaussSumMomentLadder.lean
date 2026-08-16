/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# The full subgroup Gauss-sum moment ladder: `∑_b ‖η_b‖^{2r} = q · E_r(G)`

Generalizes the second (`q|G|`), fourth (`q·E(G)`), and sixth (`q·E₃(G)`) moments to every rung:

> `subgroup_gaussSum_moment : ∑_{b∈F} ‖η_b‖^{2r} = q · E_r(G)`

where `E_r(G) = #{(x,z) ∈ (Fin r → G)² : ∑_i x_i = ∑_i z_i}` is the `r`-fold additive energy.
Pure additive-character orthogonality (Parseval), no Weil. The whole anti-concentration ladder
follows by Markov: `#{b : ‖η_b‖² ≥ q} ≤ E_r(G)/q^{r-1} ≤ |G|^{2r-1}/q^{r-1}`, whose `< 1` threshold
`|G|^{2r-1} < q^{r-1}` tends to `|G| < q^{1/2}` as `r → ∞` — the strongest count-side
anti-concentration the moment method yields. (Average/count side only; the per-frequency worst case
is the open core.)
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The **`r`-fold additive energy** of `G`: the number of pairs of `r`-tuples with equal sum. -/
def energyR (G : Finset F) (r : ℕ) : ℕ :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ z ∈ Fintype.piFinset (fun _ : Fin r => G),
    (if ∑ i, x i = ∑ i, z i then 1 else 0)

/-- A product of additive-character values is the character of the sum: `∏ᵢ ψ(cᵢ) = ψ(∑ᵢ cᵢ)`. -/
theorem prod_addChar {ι : Type*} (ψ : AddChar F ℂ) (s : Finset ι) (c : ι → F) :
    ∏ i ∈ s, ψ (c i) = ψ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s h ih =>
      rw [Finset.prod_insert h, ih, ← AddChar.map_add_eq_mul, ← Finset.sum_insert h]

/-- The `r`-th power of the subgroup Gauss sum is the character sum over `r`-tuples:
`η_b^r = ∑_{x : Fin r → G} ψ(b · ∑ᵢ xᵢ)`. -/
theorem eta_pow_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) (r : ℕ) :
    (eta ψ G b) ^ r
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, x i) := by
  have hpow : (eta ψ G b) ^ r = ∏ _i ∈ (Finset.univ : Finset (Fin r)), eta ψ G b := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow]
  simp only [eta]
  rw [Finset.prod_univ_sum (fun _ : Fin r => G) (fun (_ : Fin r) (y : F) => ψ (b * y))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [prod_addChar ψ Finset.univ (fun i => b * x i), Finset.mul_sum]

/-- The conjugate `r`-th power: `conj(η_b^r) = ∑_{z : Fin r → G} ψ(-(b · ∑ᵢ zᵢ))`. -/
theorem conj_eta_pow_eq (ψ : AddChar F ℂ) (G : Finset F) (b : F) (r : ℕ) :
    (starRingEnd ℂ) ((eta ψ G b) ^ r)
      = ∑ z ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (-(b * ∑ i, z i)) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [eta_pow_eq, map_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]

/-- **The full moment ladder: `∑_b ‖η_b‖^{2r} = q · E_r(G)`.** Pure orthogonality; no Weil. -/
theorem subgroup_gaussSum_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * energyR G r := by
  have hnorm : ∀ b : F, (eta ψ G b) ^ r * (starRingEnd ℂ) ((eta ψ G b) ^ r)
      = ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
    intro b
    have hww : (eta ψ G b) ^ r * (starRingEnd ℂ) ((eta ψ G b) ^ r)
        = ((‖(eta ψ G b) ^ r‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hww, norm_pow]
    push_cast
    rw [← pow_mul]
    ring_nf
  have hcomplex : (∑ b : F, (eta ψ G b) ^ r * (starRingEnd ℂ) ((eta ψ G b) ^ r))
      = (Fintype.card F : ℂ) * energyR G r := by
    calc ∑ b : F, (eta ψ G b) ^ r * (starRingEnd ℂ) ((eta ψ G b) ^ r)
        = ∑ b : F, (∑ x ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, x i))
            * (∑ z ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (-(b * ∑ i, z i))) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [conj_eta_pow_eq, eta_pow_eq]
      _ = ∑ b : F, ∑ x ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin r => G),
              ψ (b * ((∑ i, x i) - ∑ i, z i)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
          rw [← AddChar.map_add_eq_mul]; congr 1; ring
      _ = ∑ x ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ b : F,
              ψ (b * ((∑ i, x i) - ∑ i, z i)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ x ∈ Fintype.piFinset (fun _ : Fin r => G),
            ∑ z ∈ Fintype.piFinset (fun _ : Fin r => G),
              (if (∑ i, x i) = ∑ i, z i then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
          rw [AddChar.sum_mulShift ((∑ i, x i) - ∑ i, z i) hψ]
          have hcond : ((∑ i, x i) - ∑ i, z i = 0) ↔ ((∑ i, x i) = ∑ i, z i) := sub_eq_zero
          simp only [hcond]
          split <;> simp
      _ = (Fintype.card F : ℂ) * energyR G r := by
          rw [energyR]
          push_cast
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
          split <;> simp
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) = (Fintype.card F : ℂ) * energyR G r := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun b _ => (hnorm b).symm)
  have hfin : ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * energyR G r : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hfin

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.subgroup_gaussSum_moment
