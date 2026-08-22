/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80JDivisorSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80LEnergyRefinedConsumer

/-!
# G80J weld: divisor second moment to multiplicative energy

This file turns the pure-Nat second-moment estimate into the input expected by G80L's
subgroup interval consumer.  The result remains below the square-root-modulus fence and does
not close the production proximity prize.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80JEnergySecondMomentWeld

open G80JDivisorSecondMoment G80LEnergyRefinedConsumer G80OProductDivisorInterval

/-- A positive factorization `a * b = y` is determined by the divisor `a` of `y`. -/
theorem card_productFiber_le_card_divisors (A : Finset ℕ) (hpos : ∀ a ∈ A, 1 ≤ a) (y : ℕ) :
    ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y)).card ≤ y.divisors.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun ab => ab.1) ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hab
    show a ∈ y.divisors
    rw [Nat.mem_divisors]
    exact ⟨⟨b, hab.2.symm⟩, by
      rw [← hab.2]
      exact Nat.mul_ne_zero
        (Nat.one_le_iff_ne_zero.mp (hpos a hab.1.1))
        (Nat.one_le_iff_ne_zero.mp (hpos b hab.1.2))⟩
  · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hac
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hab hcd
    have ha : 0 < a := hpos a hab.1.1
    simp only at hac
    subst c
    have : b = d := Nat.eq_of_mul_eq_mul_left ha (hab.2.trans hcd.2.symm)
    simp [this]

/-- For `A ⊆ [1,W]`, its integer multiplicative energy is bounded by the divisor second
moment through `W²`. -/
theorem mulEnergy_le_divisor_secondMoment (A : Finset ℕ) {W : ℕ}
    (hA : A ⊆ Finset.Icc 1 W) :
    mulEnergy A ≤ ∑ y ∈ Finset.Icc 1 (W * W), y.divisors.card ^ 2 := by
  classical
  let P : Finset ℕ := Finset.Icc 1 (W * W)
  let r : ℕ → ℕ := fun y => ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y)).card
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha => (Finset.mem_Icc.mp (hA ha)).1
  have hsplit : ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
      (fun q => q.1.1 * q.1.2 = q.2.1 * q.2.2)
      = P.biUnion (fun y =>
          ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y)) ×ˢ
          ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y))) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, P,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hab, hcd⟩, heq⟩
      have ha := Finset.mem_Icc.mp (hA hab.1)
      have hb := Finset.mem_Icc.mp (hA hab.2)
      exact ⟨a * b, ⟨Nat.mul_pos ha.1 hb.1, Nat.mul_le_mul ha.2 hb.2⟩,
        ⟨⟨hab, rfl⟩, ⟨hcd, heq.symm⟩⟩⟩
    · rintro ⟨y, _, ⟨⟨hab, hy1⟩, ⟨hcd, hy2⟩⟩⟩
      exact ⟨⟨hab, hcd⟩, hy1.trans hy2.symm⟩
  rw [mulEnergy, hsplit, Finset.card_biUnion]
  · simp only [Finset.card_product, P]
    refine Finset.sum_le_sum fun y _ => ?_
    have h := card_productFiber_le_card_divisors A hpos y
    calc
      ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y)).card *
          ((A ×ˢ A).filter (fun ab => ab.1 * ab.2 = y)).card
          ≤ y.divisors.card * y.divisors.card := Nat.mul_le_mul h h
      _ = y.divisors.card ^ 2 := by rw [pow_two]
  · intro y _ y' _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨ab, cd⟩ hab hab'
    simp only [Finset.mem_product, Finset.mem_filter] at hab hab'
    exact hne (hab.1.2.symm.trans hab'.1.2)

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- Unconditional logarithmic second-moment interval bound obtained by welding G80L to G80J. -/
theorem intervalCount_pow_four_le_logSecondMoment
    (H : Finset (ZMod p)) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : W * W < p) :
    intervalCount p H W ^ 4 ≤
      H.card * ((W * W) * (Nat.log 2 (W * W) + 1) ^ 3) := by
  let A := (Finset.Icc 1 W).filter (fun s => ((s : ℕ) : ZMod p) ∈ H)
  calc
    intervalCount p H W ^ 4 ≤ H.card * mulEnergy A :=
      intervalCount_pow_four_le_energy H hmul hW
    _ ≤ H.card * (∑ y ∈ Finset.Icc 1 (W * W), y.divisors.card ^ 2) := by
      refine Nat.mul_le_mul_left _ (mulEnergy_le_divisor_secondMoment A ?_)
      intro a ha
      exact (Finset.mem_filter.mp ha).1
    _ ≤ H.card * ((W * W) * (Nat.log 2 (W * W) + 1) ^ 3) :=
      Nat.mul_le_mul_left _ (sum_sq_card_divisors_le (W * W))

end ArkLib.ProximityGap.Frontier.G80JEnergySecondMomentWeld

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80JEnergySecondMomentWeld.mulEnergy_le_divisor_secondMoment
#print axioms
  ArkLib.ProximityGap.Frontier.G80JEnergySecondMomentWeld.intervalCount_pow_four_le_logSecondMoment
