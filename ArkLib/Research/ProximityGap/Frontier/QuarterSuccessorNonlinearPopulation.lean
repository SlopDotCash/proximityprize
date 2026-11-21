/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.UnrestrictedSectionPopulation
import ArkLib.Research.ProximityGap.Frontier.HalfRateJetCapacity

/-! # Nonlinear populations at the first-prime quarter-rate successor

The line through the order-one and order-two jet costs bounds every order up to
three. The Hessian charge and convexity of the multiple space then leave an
auxiliary outside that space even without a second, value-quadratic interpolant.
-/

open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorNonlinearPopulation

open HalfRateUnrestrictedJetBudget (cap capacity_chord)
open SecondPrimeQuarticInterpolation (Monomials)
open UnrestrictedSectionPopulation SecondPrimeCoordinateWeight
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry

private def surplus (b w : ℤ) : ℤ :=
  7 * (cap 20000 268435455 3131746980 12 - cap (20000 - b) 268435455 (3131746980 - w) 12 -
    1073741824 * 15 * 20001) +
      19985 * (74 * 1073741824 - 4 * ((6 * b - 2) * w - 3 * b ^ 2 * 268435455))

private theorem positive (b w : ℤ) (hb : 2 ≤ b) (hb' : b ≤ 3)
    (hl : b * 268435455 ≤ w) (hu : w ≤ 1252698791) : 0 < surplus b w := by
  let lo := b * 268435455
  let hi : ℤ := 1252698791
  have hlt : lo < hi := by dsimp [lo, hi]; omega
  have ends : 0 < surplus b lo ∧ 0 < surplus b hi := by
    dsimp only [lo, hi]
    interval_cases b <;> decide
  have hL : 0 ≤ w - lo := sub_nonneg.mpr hl
  have hR : 0 ≤ hi - w := sub_nonneg.mpr hu
  have ch := capacity_chord (20000 - b) 268435455 3131746980 lo hi w 12 (by omega) hl hu
  have hs : (hi - w) * surplus b lo + (w - lo) * surplus b hi ≤ (hi - lo) * surplus b w := by
    unfold surplus
    linear_combination 7 * ch
  have h1 := mul_le_mul_of_nonneg_left (show 1 ≤ surplus b lo from ends.1) hR
  have h2 := mul_le_mul_of_nonneg_left (show 1 ≤ surplus b hi from ends.2) hL
  have hpos : 0 < (hi - lo) * surplus b w := by linarith only [h1,h2,hs,hlt]
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr hlt)).mp hpos

private theorem strict_count {I : Type} [Fintype I] (r : I → ℕ) (b W : ℕ)
    (hb : 2 ≤ b) (hb' : b ≤ 3) (hn : Fintype.card I = 1073741824) (hs : ∀ i, r i ≤ b)
    (hl : b * 268435455 ≤ W) (hu : W ≤ 1252698791)
    (hc : (∑ i, r i * (3 * r i - 2)) + 3 * b ^ 2 * 268435455 ≤ (6 * b - 2) * W) :
    1073741824 * (15 * 20001) + Fintype.card (Monomials (20000 - b) 11 268435455 (3131746980 - W)) <
      Fintype.card (Monomials 20000 11 268435455 3131746980) +
        ∑ i, ((5 - r i) * (5 - r i + 1) / 2) * 19985 := by
  have c₁ := _root_.ProximityGap.HalfRateJetCapacity.cast_monomials 20000 11 268435455 3131746980
    (by decide)
  have c₂ := _root_.ProximityGap.HalfRateJetCapacity.cast_monomials (20000 - b) 11 268435455
    (3131746980 - W) (by omega)
  rw [Nat.cast_sub (by omega : W ≤ 3131746980), Nat.cast_sub (by omega : b ≤ 20000)] at c₂
  have hp := positive (b : ℤ) (W : ℤ) (by exact_mod_cast hb) (by exact_mod_cast hb')
    (by exact_mod_cast hl) (by exact_mod_cast hu)
  unfold surplus at hp
  change (Fintype.card (Monomials 20000 11 268435455 3131746980) : ℤ) =
    cap 20000 268435455 3131746980 12 at c₁
  change (Fintype.card (Monomials (20000 - b) 11 268435455 (3131746980 - W)) : ℤ) =
    cap (20000 - (b:ℤ)) 268435455 (3131746980 - (W:ℤ)) 12 at c₂
  rw [←c₁, ←c₂] at hp
  have localCost (i : I) : 74 * 19985 ≤
      7 * (((5 - r i) * (5 - r i + 1) / 2) * 19985) + (4 * 19985) * (r i * (3 * r i - 2)) := by
    have hri : r i ≤ 3 := (hs i).trans hb'
    interval_cases h : r i <;> decide
  have total := sum_le_sum (s := (univ : Finset I)) (fun i _ => localCost i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul, hn] at total
  generalize hA : Fintype.card (Monomials 20000 11 268435455 3131746980) = A at hp ⊢
  generalize hM : Fintype.card (Monomials (20000 - b) 11 268435455 (3131746980 - W)) = M at hp ⊢
  generalize hC : (∑ i, r i * (3 * r i - 2)) = C at hc total
  generalize hK : (∑ i, ((5 - r i) * (5 - r i + 1) / 2) * 19985) = K at total ⊢
  clear hA hM hC hK localCost c₁ c₂
  interval_cases b <;> norm_num at hp hc total ⊢ <;> omega

variable {F I : Type} [Field F] [Fintype I] [DecidableEq F]

/-- Every irreducible quadratic or cubic component of the double-interpolation surface
carries at most 40154 or 60143 selected genuine scalars at 447392428 errors. -/
theorem actual_population {p : ℕ} [CharP F p] (hp : 132 < p)
    (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I)
    (hn : Fintype.card I = 1073741824)
    (ht : 626349396 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (f : F[X][X][X]) (hi : Irreducible f)
    (hb₂ : 2 ≤ f.natDegree) (hb₃ : f.natDegree ≤ 3)
    (htot : WeightedSylvesterDegree.TotalDegreeLe f 16)
    (hw : weight 268435455 f ≤ 1252698791)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C z)) (fam.q z) = 0) :
    G.card ≤ f.natDegree * 20000 + 11 * (16 - f.natDegree) := by
  classical
  rcases charge_or_singleton (d := 268435455) hp (RingHom.id F) dom (u 0) (u 1) f hi hb₂
    (by omega) htot G fam.q hroot with hcharge | hs
  · refine population_of_capacity (t := 626349396) (μ := 5) (d := 268435455) (by decide)
      (by decide) (by decide) (by decide) (RingHom.id F) dom (u 0) (u 1) f hi (by omega)
      (by omega) htot ?_ G fam.q hroot ?_
    · rw [hn]
      apply strict_count _ f.natDegree _ hb₂ hb₃ hn _ (degree_floor _ f hi.ne_zero) hw hcharge
      intro i
      exact (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans (by
        rw [TerminalQuarticLocalization.local_degree,
          TerminalQuarticHessianTransport.permute_degree])
    · intro z hz
      refine ⟨by have := fam.degree_lt z (hG hz); omega, fullAgreement dom (u 0) (u 1) z (fam.q z),
        ht.trans (fam.threshold_le z (hG hz)), fun i hi => (mem_filter.mp hi).2⟩
  · omega

end ArkLib.ProximityGap.Frontier.QuarterSuccessorNonlinearPopulation
