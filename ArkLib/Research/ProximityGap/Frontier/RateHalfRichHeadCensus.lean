/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._FSMB_CoreAbsorptionLadder
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection

/-!
# Rich polynomial heads at the half-rate predecessor

At 313174698 errors, a one-fresh witness needs 760567125 joint agreements.
For arbitrary received rows, at most 118 distinct half-rate polynomial pairs reach
that level. Any four such pairs also determine a common primitive polynomial direction
whose two degrees are at most 59652323. At the maximal population of 118,
the corresponding degree cap is 12961. No quotient structure is assumed.
-/

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder

namespace ProximityGap.RateHalfRichHeadCensus

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The integer tangent through consecutive points of the square function. -/
private theorem tangent (m a : ℕ) : (2*a+1)*m ≤ m^2+a*(a+1) := by
  by_cases h : m ≤ a
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.zero_le (d ^ 2)]
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (show a+1 ≤ m by omega)
    nlinarith [Nat.zero_le (d ^ 2)]

/-- Pair intersections constrain every integer tangent to the second moment of the
per-coordinate agreement multiplicity, including near-integer average multiplicities. -/
theorem incidence_bound {s t b : ℕ} (Z : Fin s → Finset I)
    (hsize : ∀ i, t ≤ (Z i).card)
    (hpair : ∀ i j, i ≠ j → (Z i ∩ Z j).card ≤ b) (a : ℕ) :
    2*a*(s*t) ≤ s*(s-1)*b + a*(a+1)*Fintype.card I := by
  classical
  have hS : s*t ≤ ∑ i, (Z i).card := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin s))) (fun i _ => hsize i)
  have htan : (2*a+1)*(∑ i, (Z i).card) ≤
      (∑ i, ∑ j, (Z i ∩ Z j).card) + a*(a+1)*Fintype.card I := by
    rw [ArkLib.Coverage.sum_card_eq_sum_degree, sum_inter_card_eq_sum_degree_sq, Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum (fun x _ => tangent ((univ.filter (fun i => x ∈ Z i)).card) a))
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_univ, nsmul_eq_mul, Nat.mul_comm]
    exact le_rfl
  have hinner (i : Fin s) : (∑ j, (Z i ∩ Z j).card) ≤ (Z i).card+(s-1)*b := by
    rw [← Finset.add_sum_erase univ (fun j => (Z i ∩ Z j).card) (mem_univ i)]
    refine Nat.add_le_add (by simp) ?_
    calc
      ∑ j ∈ univ.erase i, (Z i ∩ Z j).card ≤ ∑ _j ∈ univ.erase i, b :=
        sum_le_sum fun j hj => hpair i j (mem_erase.mp hj).1.symm
      _ = _ := by simp [card_erase_of_mem]
  have hupper := Finset.sum_le_sum (s := (univ : Finset (Fin s))) (fun i _ => hinner i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hupper
  have hscaled := Nat.mul_le_mul_left (2*a) hS
  rw [Nat.add_mul, one_mul] at htan
  rw [Nat.mul_assoc s]
  omega

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Polynomial degree and the exact joint agreement needed before adding a fresh site. -/
def Rich (dom : I ↪ F) (u₀ u₁ : I → F) (c : PolynomialLine F) : Prop :=
  c.1.natDegree < 536870912 ∧ c.2.natDegree < 536870912 ∧
    760567125 ≤ (jointCore dom u₀ u₁ c.1 c.2).card

/-- Uniform cap on the number of rich polynomial pairs on any domain of production length. -/
theorem card_le_118 (dom : I ↪ F) (u₀ u₁ : I → F) (hn : Fintype.card I = 1073741824)
    (H : Finset (PolynomialLine F)) (hr : ∀ c ∈ H, Rich dom u₀ u₁ c) : H.card ≤ 118 := by
  classical
  by_contra! hc
  obtain ⟨S, hsub, hS⟩ := Finset.exists_subset_card_eq (show 119 ≤ H.card by omega)
  have e := S.equivFin
  rw [hS] at e
  let f (i : Fin 119) := (e.symm i).val
  have hf (i : Fin 119) := hr _ (hsub (e.symm i).property)
  have hinj : Function.Injective f := fun _ _ h => e.symm.injective (Subtype.ext h)
  have hp (i j : Fin 119) (hne : i ≠ j) :
      (jointCore dom u₀ u₁ (f i).1 (f i).2 ∩ jointCore dom u₀ u₁ (f j).1 (f j).2).card
      ≤ 536870911 := by
    have hd : (f i).1 ≠ (f j).1 ∨ (f i).2 ≠ (f j).2 := by
      by_contra! h
      exact hne (hinj (Prod.ext h.1 h.2))
    exact jointCore_inter_jointCore_card_le dom u₀ u₁ (by decide : 1 ≤ 536870912)
      (hf i).1 (hf i).2.1 (hf j).1 (hf j).2.1 hd
  have h := incidence_bound (fun i => jointCore dom u₀ u₁ (f i).1 (f i).2)
    (fun i => (hf i).2.2) hp 84
  rw [hn] at h
  norm_num at h

omit [DecidableEq I] in
/-- Any three rich pairs are collinear over the polynomial fraction field. -/
theorem determinant_zero (dom : I ↪ F) (u₀ u₁ : I → F) (hn : Fintype.card I = 1073741824)
    {a b c : PolynomialLine F} (ha : Rich dom u₀ u₁ a)
    (hb : Rich dom u₀ u₁ b) (hc : Rich dom u₀ u₁ c) : lineDeterminant a b c = 0 := by
  have hd := threeLineDeterminant_eq_zero_of_jointCore_card_sum_sub_domain_gt dom u₀ u₁ a b c
    ha.1 ha.2.1 hb.1 hb.2.1 hc.1 hc.2.1 (by
      have := ha.2.2
      have := hb.2.2
      have := hc.2.2
      omega)
  simpa only [lineDeterminant, threeLineDeterminant, mul_comm] using hd

/-- Coincident joint evaluations are roots of the common polynomial content of a
difference of two distinct heads. -/
private theorem overlap_le_content (dom : I ↪ F) (u₀ u₁ : I → F)
    {a b : PolynomialLine F} (hne : a ≠ b) :
    (jointCore dom u₀ u₁ a.1 a.2 ∩ jointCore dom u₀ u₁ b.1 b.2).card ≤
      (referenceContent a b).natDegree := by
  apply le_trans (Finset.card_le_card ?_)
    (ArkLib.CS25.card_domain_roots_le dom _ (referenceContent_ne_zero_of_ne hne))
  intro i hi
  simp only [Finset.mem_inter, jointCore, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  change IsRoot (referenceContent a b) (dom i)
  rw [← dvd_iff_isRoot, referenceContent, _root_.dvd_gcd_iff]
  simp only [dvd_iff_isRoot, IsRoot, eval_sub, hi.1.1, hi.1.2, hi.2.1, hi.2.2, sub_self, and_self]

/-- Two members of a family generate a coprime polynomial direction of degree at most
`d`, and every rich head has a polynomial parameter in that direction. -/
def HasDirectionAtMost {s : ℕ} (dom : I ↪ F) (u₀ u₁ : I → F)
    (v : Fin s → PolynomialLine F) (d : ℕ) : Prop :=
  ∃ i j, i ≠ j ∧
    max (primitiveIntercept (v i) (v j)).natDegree (primitiveSlope (v i) (v j)).natDegree ≤ d ∧
    ∀ c, Rich dom u₀ u₁ c → ∃ f : F[X],
      c.1 - (v i).1 = primitiveIntercept (v i) (v j) * f ∧
      c.2 - (v i).2 = primitiveSlope (v i) (v j) * f

/-- Integer pair incidence bounds the residual primitive direction degree for every
feasible rich-head population at the predecessor. -/
theorem direction_of_incidence {s : ℕ} (dom : I ↪ F) (u₀ u₁ : I → F)
    (hn : Fintype.card I = 1073741824) (v : Fin s → PolynomialLine F)
    (hv : Function.Injective v) (hr : ∀ i, Rich dom u₀ u₁ (v i)) (m b : ℕ)
    (hcost : s*(s-1)*b + m*(m+1)*1073741824 < 2*m*(s*760567125)) :
    HasDirectionAtMost dom u₀ u₁ v (536870911-(b+1)) := by
  let Z (i : Fin s) := jointCore dom u₀ u₁ (v i).1 (v i).2
  have hover : ∃ i j : Fin s, i ≠ j ∧ b+1 ≤ (Z i ∩ Z j).card := by
    by_contra! h
    have hbound := incidence_bound Z (fun i => (hr i).2.2)
      (b := b) (fun i j hij => by have := h i j hij; omega) m
    rw [hn] at hbound
    exact hcost.not_ge hbound
  obtain ⟨i, j, hij, hlarge⟩ := hover
  have hd : v i ≠ v j := hv.ne hij
  have hcontent := hlarge.trans (overlap_le_content dom u₀ u₁ hd)
  have hdegree {q r : F[X]} (hq : q.natDegree < 536870912)
      (hqr : q = referenceContent (v i) (v j) * r) : r.natDegree ≤ 536870911-(b+1) := by
    by_cases hz : r = 0
    · simp [hz]
    · rw [hqr, natDegree_mul (referenceContent_ne_zero_of_ne hd) hz] at hq
      omega
  refine ⟨i, j, hij, max_le ?_ ?_, fun c hc =>
    exists_polynomial_factor_of_lineDeterminant_eq_zero _ _ _ hd
      (determinant_zero dom u₀ u₁ hn (hr i) (hr j) hc)⟩
  · exact hdegree ((natDegree_sub_le ..).trans_lt (max_lt (hr j).1 (hr i).1))
      (referenceIntercept_eq_content_mul_primitive hd)
  · exact hdegree ((natDegree_sub_le ..).trans_lt (max_lt (hr j).2.1 (hr i).2.1))
      (referenceSlope_eq_content_mul_primitive hd)

/-- With four heads their cores force a reference difference with at least 477218588
roots and leave degree at most 59652323 for the primitive direction. -/
theorem four_head_direction (dom : I ↪ F) (u₀ u₁ : I → F) (hn : Fintype.card I = 1073741824)
    (v : Fin 4 → PolynomialLine F) (hv : Function.Injective v)
    (hr : ∀ i, Rich dom u₀ u₁ (v i)) : HasDirectionAtMost dom u₀ u₁ v 59652323 :=
  direction_of_incidence dom u₀ u₁ hn v hv hr 2 477218587 (by decide)

/-- A family as large as the 118-head cap forces a direction of degree at most 12961. -/
theorem full_population_direction (dom : I ↪ F) (u₀ u₁ : I → F) (hn : Fintype.card I = 1073741824)
    (v : Fin 118 → PolynomialLine F) (hv : Function.Injective v)
    (hr : ∀ i, Rich dom u₀ u₁ (v i)) : HasDirectionAtMost dom u₀ u₁ v 12961 :=
  direction_of_incidence dom u₀ u₁ hn v hv hr 83 536857949 (by decide)

#print axioms incidence_bound
#print axioms card_le_118
#print axioms determinant_zero
#print axioms direction_of_incidence
#print axioms four_head_direction
#print axioms full_population_direction

end ProximityGap.RateHalfRichHeadCensus
