/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The exact `r`-th *raw* moment of the subgroup Gauss sum = `q · N₀(G,r)` (#389, #407)

`SubgroupGaussSumMoment` proves the **even**, absolute-value moment
`∑_b ‖η_b‖^{2r} = q · E_r(G)` (the `2r`-fold additive energy). This file proves the
sharper, *all-`r`* **raw** power-sum identity (odd exponents included), with `η_b` taken
*without* the absolute value:

> `∑_{b∈F} η_b^r = q · N₀(G,r)`,  `N₀(G,r) = #{ v ∈ Gʳ : ∑ᵢ vᵢ = 0 }`.

Here `N₀(G,r)` is the number of `r`-tuples from `G` summing to zero — the *additive
relation count*. The proof is a one-shot application of additive-character orthogonality
(`AddChar.sum_mulShift`) to the `eta_pow` expansion: no conjugation, no `RCLike` machinery,
and it holds for **every** `r` (in particular the odd exponents, which the `‖·‖^{2r}` form
cannot see).

## Relation to the Gaussian-period moment law (#407)

For the **Gaussian periods** `η_i` (the `m = (q-1)/n` distinct nonzero-coset values of `η_b`
for `G = μ_n` an order-`n` multiplicative subgroup), `η_b` is `μ_n`-coset-invariant with
`η_0 = n`, so `∑_{b∈F} η_b^r = η_0^r + n·∑_i η_i^r = n^r + n·∑_i η_i^r`. Combined with the
identity below this yields the **period moment law**

> `∑_i η_i^r = (q/n)·N₀(G,r) − n^{r-1}`   (issue #407),

a closed form for *every* power-sum moment of the Gaussian-period distribution (the in-tree
energy moment gives only the even `r`). This file establishes the field-level engine
`∑_b η_b^r = q·N₀` of that law; the coset reindexing to `∑_i η_i^r` is the consumer step.

For a **negation-closed** `G` (`-1 ∈ μ_n`, true for every `n` even) the periods are real and,
via the negation bijection `(v,w) ↦ (v,-w)` on `Gʳ×Gʳ`, `N₀(G,2r) = E_r(G)` — so the even
case of `subgroup_gaussSum_moment` is recovered from `subgroup_gaussSum_rawMoment`.

Axiom-clean. Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumRawMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive relation count `N₀(G,r) = #{ v ∈ Gʳ : ∑ᵢ vᵢ = 0 }`, as an indicator sum. -/
noncomputable def N0 (G : Finset F) (r : ℕ) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), (if ∑ i, v i = 0 then 1 else 0)

/-- **The exact raw `r`-th moment: `∑_b η_b^r = q · N₀(G,r)`.**

Holds for *every* exponent `r` (odd included), unlike the `‖·‖^{2r}` energy moment. The proof
expands `η_b^r` over `r`-tuples (`eta_pow`), swaps the order of summation, and applies additive
orthogonality (`AddChar.sum_mulShift`): the inner sum over `b` is `q` when the tuple sums to `0`
and `0` otherwise. -/
theorem subgroup_gaussSum_rawMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) :
    ∑ b : F, eta ψ G b ^ r = (Fintype.card F : ℂ) * N0 G r := by
  classical
  calc ∑ b : F, eta ψ G b ^ r
      = ∑ b : F, ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, v i) :=
        Finset.sum_congr rfl (fun b _ => eta_pow ψ G b r)
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), ∑ b : F, ψ (b * ∑ i, v i) :=
        Finset.sum_comm
    _ = (Fintype.card F : ℂ) * N0 G r := by
        simp only [N0]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [AddChar.sum_mulShift (∑ i, v i) hψ]
        by_cases h : ∑ i, v i = 0 <;> simp [h]

/-- For a **negation-closed** `G` (`∀ x ∈ G, -x ∈ G`, e.g. an order-`n` subgroup `μ_n` with
`-1 ∈ μ_n`), each period `η_b` is **real**: `conj η_b = η_b`. Reindex the defining sum by the
negation involution `y ↦ -y` of `G`, using `conj(ψ a) = ψ(-a)`. -/
theorem eta_conj_eq {ψ : AddChar F ℂ} (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := fun a => by
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hGneg : G.image (fun y => -y) = G := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hG y hy
    · intro x hx; exact Finset.mem_image.mpr ⟨-x, hG x hx, neg_neg x⟩
  simp only [eta, map_sum]
  calc ∑ y ∈ G, (starRingEnd ℂ) (ψ (b * y))
      = ∑ y ∈ G, ψ (b * (-y)) := by
        refine Finset.sum_congr rfl (fun y _ => ?_); rw [hconj]; congr 1; ring
    _ = ∑ y ∈ G.image (fun y => -y), ψ (b * y) := by
        rw [Finset.sum_image (fun a _ a' _ h => neg_injective h)]
    _ = ∑ y ∈ G, ψ (b * y) := by rw [hGneg]

/-- For a negation-closed `G`, the `2r`-fold relation count equals the `r`-fold additive energy:
`N₀(G,2r) = E_r(G)`. Proof via reality of the periods: `subgroup_gaussSum_rawMoment` at exponent
`2r` gives `∑_b η_b^{2r} = q·N₀(G,2r)`, while `subgroup_gaussSum_moment` gives
`∑_b ‖η_b‖^{2r} = q·E_r(G)`; since each `η_b` is real (`eta_conj_eq`), `η_b^{2r} = ‖η_b‖^{2r}`,
so the two right-hand sides agree and `q ≠ 0` cancels.

This recovers the even case of `subgroup_gaussSum_moment` from `subgroup_gaussSum_rawMoment`. -/
theorem N0_eq_rEnergy_of_neg_closed {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) (r : ℕ) :
    N0 G (2 * r) = rEnergy G r := by
  classical
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  -- per-`b` reality: `η_b^{2r} = (‖η_b‖^{2r} : ℝ)` in `ℂ`
  have hreal : ∀ b : F, eta ψ G b ^ (2 * r) = ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
    intro b
    have him : (eta ψ G b).im = 0 := Complex.conj_eq_iff_im.mp (eta_conj_eq G hG b)
    have hre : eta ψ G b = ((eta ψ G b).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have heven : Even (2 * r) := even_two_mul r
    have hn : ‖eta ψ G b‖ = |(eta ψ G b).re| := by
      conv_lhs => rw [hre]
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc eta ψ G b ^ (2 * r)
        = ((eta ψ G b).re : ℂ) ^ (2 * r) := by rw [← hre]
      _ = (((eta ψ G b).re ^ (2 * r) : ℝ) : ℂ) := by push_cast; ring
      _ = ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
          rw [hn, heven.pow_abs]
  -- the two moment laws, cast to a common `ℂ` identity
  have hraw : ∑ b : F, eta ψ G b ^ (2 * r) = (Fintype.card F : ℂ) * N0 G (2 * r) :=
    subgroup_gaussSum_rawMoment hψ G (2 * r)
  have hen : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r :=
    subgroup_gaussSum_moment hψ G r
  have hsum : (Fintype.card F : ℂ) * N0 G (2 * r) = (Fintype.card F : ℂ) * rEnergy G r := by
    rw [← hraw]
    calc ∑ b : F, eta ψ G b ^ (2 * r)
        = ∑ b : F, ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := Finset.sum_congr rfl (fun b _ => hreal b)
      _ = (((∑ b : F, ‖eta ψ G b‖ ^ (2 * r)) : ℝ) : ℂ) := by rw [Complex.ofReal_sum]
      _ = (((Fintype.card F : ℝ) * rEnergy G r : ℝ) : ℂ) := by rw [hen]
      _ = (Fintype.card F : ℂ) * rEnergy G r := by push_cast; ring
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have : (N0 G (2 * r) : ℂ) = (rEnergy G r : ℂ) := mul_left_cancel₀ hcard hsum
  exact_mod_cast this

end ArkLib.ProximityGap.SubgroupGaussSumRawMoment

#print axioms ArkLib.ProximityGap.SubgroupGaussSumRawMoment.subgroup_gaussSum_rawMoment
#print axioms ArkLib.ProximityGap.SubgroupGaussSumRawMoment.N0_eq_rEnergy_of_neg_closed
