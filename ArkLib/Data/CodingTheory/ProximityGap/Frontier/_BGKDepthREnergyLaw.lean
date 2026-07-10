/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKSupBoundMomentTower

/-!
# The exact depth-`r` energy law + the BGK-conditional §8 independence form — #466

Companion to `_BGKSupBoundMomentTower.lean`. Two results:

* `moment_eq_card_energy` — **the exact depth-`r` Parseval/energy law** (unconditional, no Weil
  input): for a primitive `ψ` and any finite `G ⊆ F`, `r ≥ 0`,

    `∑_{b∈F} ‖η_b‖^(2r) = q · E_r(G)`,

  where `E_r(G) = #{(x, y) ∈ G^r × G^r : ∑ xᵢ = ∑ yᵢ}` is the ordered depth-`r` additive
  energy (`rEnergy` below). At `r = 2` this is the in-tree fourth-moment/`addEnergy` identity;
  the general-`r` form was previously only available depth-by-depth.

* `rEnergy_le_of_worstCase` — **the §8 independence form as a theorem modulo BGK**: under the
  single named open Prop `WorstCaseIncompleteSumBound ψ G M`,

    `q · E_r(G) ≤ |G|^(2r) + M^(r−1) · q · |G|`   (every `r ≥ 1`).

  At `M = C·n·log n` (round-30 scale) and `r ≈ log p` this is exactly the dossier §8 target
  `E_r − n^(2r)/q ≤ (C n log n)^(r−1) · n`. The open content stays 100% inside the hypothesis;
  nothing here discharges BGK. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower

namespace ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw

/-- An additive character maps finite sums to finite products. -/
theorem addChar_map_sum {A M : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    {ι : Type*} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, map_add_eq_mul, ih]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `r`-th power of the subgroup Gauss sum is the complete exponential sum of the
depth-`r` sum map over ordered `r`-tuples of `G`. -/
theorem eta_pow_eq_sum (ψ : AddChar F ℂ) (G : Finset F) (b : F) (r : ℕ) :
    eta ψ G b ^ r
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin r => G), ψ (b * ∑ i, p i) := by
  rw [eta, Finset.sum_pow']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, addChar_map_sum]

/-- **Ordered depth-`r` additive energy** of `G`:
`E_r(G) = #{(x, y) ∈ G^r × G^r : ∑ xᵢ = ∑ yᵢ}`. -/
noncomputable def rEnergy (G : Finset F) (r : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin r => G)) ×ˢ (Fintype.piFinset (fun _ : Fin r => G))
    |>.filter (fun p => ∑ i, p.1 i = ∑ i, p.2 i)).card

/-- **The exact depth-`r` Parseval/energy law**: `∑_b ‖η_b‖^(2r) = q · E_r(G)`. Pure
additive-character orthogonality at every depth; no Weil input. -/
theorem moment_eq_card_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * rEnergy G r := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  set P := Fintype.piFinset (fun _ : Fin r => G) with hP
  -- Step 1: `‖η_b‖^(2r)` as `η_b^r · conj (η_b^r)`.
  have hnorm : ∀ b : F,
      eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r) = ((‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ) := by
    intro b
    have hpow : ‖eta ψ G b ^ r‖ ^ 2 = ‖eta ψ G b‖ ^ (2 * r) := by
      rw [norm_pow, ← pow_mul, Nat.mul_comm r 2]
    rw [RCLike.mul_conj, ← hpow]
    norm_cast
  -- Step 2: the complex identity via orthogonality.
  have hcomplex : (∑ b : F, eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r))
      = (Fintype.card F : ℂ) * rEnergy G r := by
    have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
      intro a
      rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
    calc ∑ b : F, eta ψ G b ^ r * (starRingEnd ℂ) (eta ψ G b ^ r)
        = ∑ b : F, ∑ x ∈ P, ∑ y ∈ P, ψ (b * (∑ i, x i - ∑ i, y i)) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have hconjpow : (starRingEnd ℂ) (eta ψ G b ^ r)
              = ∑ y ∈ P, ψ (-(b * ∑ i, y i)) := by
            rw [eta_pow_eq_sum, map_sum]
            exact Finset.sum_congr rfl (fun y _ => hconj _)
          rw [hconjpow, eta_pow_eq_sum ψ G b r, ← hP, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
          have harg : b * (∑ i, x i) + -(b * ∑ i, y i) = b * (∑ i, x i - ∑ i, y i) := by ring
          rw [← AddChar.map_add_eq_mul, harg]
      _ = ∑ x ∈ P, ∑ y ∈ P, ∑ b : F, ψ (b * (∑ i, x i - ∑ i, y i)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ x ∈ P, ∑ y ∈ P,
            (if (∑ i, x i) = (∑ i, y i) then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [AddChar.sum_mulShift _ hψ]
          simp [sub_eq_zero]
      _ = (Fintype.card F : ℂ) * rEnergy G r := by
          rw [rEnergy]
          rw [Finset.card_filter]
          rw [Finset.sum_product]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          by_cases h : (∑ i, x i) = (∑ i, y i) <;> simp [h]
  -- Step 3: cast back to ℝ.
  have hcast : ((∑ b : F, ‖eta ψ G b‖ ^ (2 * r) : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * rEnergy G r : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_congr rfl (fun b _ => hnorm b), hcomplex]
    push_cast
    ring
  exact_mod_cast hcast

/-- The zero frequency contributes exactly `|G|^(2r)`. -/
theorem eta_zero_pow (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
  rw [eta_zero]
  simp

/-- **The §8 independence form as a theorem modulo BGK**: under the single named open Prop
`WorstCaseIncompleteSumBound ψ G M`, every depth `r ≥ 1` has

  `q · E_r(G) ≤ |G|^(2r) + M^(r−1) · q · |G|`.

At the round-30 scale `M = C·n·log n` and depth `r ≈ log p` this is the dossier §8 target
`E_r − n^(2r)/q ≤ (C·n·log n)^(r−1)·n`. Open content = the hypothesis, nothing else. -/
theorem rEnergy_le_of_worstCase {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M)
    {r : ℕ} (hr : 1 ≤ r) :
    (Fintype.card F : ℝ) * rEnergy G r
      ≤ (G.card : ℝ) ^ (2 * r) + M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card) := by
  have hlaw := (moment_eq_card_energy hψ G r).symm
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r)
      = ‖eta ψ G 0‖ ^ (2 * r) + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have htower := etaMomentTower_of_worstCase_relaxed hψ G hM0 hwc hr
  rw [hlaw, hsplit, eta_zero_pow]
  linarith

/-- **Depth-five headline**: BGK sup-bound `M` alone gives
`q · E_5(G) ≤ |G|^10 + M⁴ · q · |G|` — the moment-side production depth-five envelope input. -/
theorem rEnergy_five_le_of_worstCase {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M) :
    (Fintype.card F : ℝ) * rEnergy G 5
      ≤ (G.card : ℝ) ^ 10 + M ^ 4 * ((Fintype.card F : ℝ) * G.card) := by
  simpa using rEnergy_le_of_worstCase hψ G hM0 hwc (r := 5) (by norm_num)

end ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.moment_eq_card_energy
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.rEnergy_le_of_worstCase
#print axioms ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw.rEnergy_five_le_of_worstCase
