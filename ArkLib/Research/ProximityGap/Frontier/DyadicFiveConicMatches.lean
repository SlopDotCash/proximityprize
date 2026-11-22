/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicConicPairs

/-! # At most four matches on the exceptional dyadic conic

A product and its sum determine the unordered endpoints. Five different
source coordinates therefore require three different pair products.
-/
namespace ProximityGap.DyadicExceptionalConic
open DyadicConicPairs Finset
variable {L : Type*} [Field L]

private theorem three_products {z B c : L} (x y : Fin 5 → ℕ)
    (xi : Function.Injective (fun i => z^(x i)))
    (law : ∀ i, B*(z^(x i))*(z^(y i))+z^(x i)+z^(y i)+B*c=0) :
    ∃ i j k, z^(x i)*z^(y i)≠z^(x j)*z^(y j) ∧
      z^(x i)*z^(y i)≠z^(x k)*z^(y k) ∧ z^(x j)*z^(y j)≠z^(x k)*z^(y k) := by
  classical
  let f (i : Fin 5) := z^(x i)*z^(y i)
  let s := univ.image f
  have fiber (u : L) (hu : u∈s) : (univ.filter (fun i => f i=u)).card≤2 := by
    obtain ⟨j,-,rfl⟩ := mem_image.mp hu
    rw [← card_image_of_injOn xi.injOn]
    apply le_trans _ (card_le_two (a:=z^(x j)) (b:=z^(y j)))
    apply card_le_card
    intro t ht
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    have eq := (mem_filter.mp hi).2
    unfold f at eq
    have sumeq : z^(x i)+z^(y i)=z^(x j)+z^(y j) := by
      linear_combination law i-law j-B*eq
    have roots : (z^(x i)-z^(x j))*(z^(x i)-z^(y j))=0 := by
      linear_combination z^(x i)*sumeq-eq
    rcases mul_eq_zero.mp roots with left|right
    · simp [sub_eq_zero.mp left]
    · simp [sub_eq_zero.mp right]
  have size : 5 ≤ s.card*2 := calc
    5 = (univ : Finset (Fin 5)).card := by simp
    _ = ∑ u ∈ s, (univ.filter fun i => f i=u).card := card_eq_sum_card_image f univ
    _ ≤ ∑ _u ∈ s, 2 := sum_le_sum fiber
    _ = _ := by simp
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp (by omega : 2<s.card)
  obtain ⟨i,-,rfl⟩ := mem_image.mp ha
  obtain ⟨j,-,rfl⟩ := mem_image.mp hb
  obtain ⟨k,-,rfl⟩ := mem_image.mp hc
  exact ⟨i,j,k,ab,ac,bc⟩

/-- A nonsingular exceptional conic with a nonzero coefficient and an
odd-power constant cannot match five dyadic sites, including fixed sites. -/
theorem five [Algebra ℚ L] {m : ℕ} [IsCyclotomicExtension {2^(m+1)} ℚ L] {z : L}
    (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (q : ℕ) (odd : q%2=1) (B : L)
    (nonzero : B≠0) (det : B^2*z^q≠1) (x y : Fin 5 → ℕ)
    (xi : Function.Injective (fun i => z^(x i))) (_yi : Function.Injective (fun i => z^(y i)))
    (law : ∀ i, B*(z^(x i))*(z^(y i))+z^(x i)+z^(y i)+B*z^q=0) : False := by
  cases m with
  | zero => omega
  | succ r =>
    let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    let : IsGalois ℚ L := IsCyclotomicExtension.isGalois {2^(r+2)} ℚ L
    obtain ⟨σ,flip⟩ := DyadicParityGalois.exists_flip hz
    have anti : σ (z^q)= -(z^q) := by
      simpa [odd] using DyadicParityGalois.action σ.toRingEquiv flip q
    have zn : z≠0 := by intro eq; simpa [eq] using hz.pow_eq_one
    obtain ⟨i,j,k,ij,ik,jk⟩ := three_products x y xi law
    exact no_three (by omega : 0<r+1) hz σ flip nonzero anti
      (oriented _ _) (oriented _ _) (oriented _ _)
      (paired_orient (law i)) (paired_orient (law j)) (paired_orient (law k))
      det (pow_ne_zero _ zn) (by simpa only [prod_orient] using ij)
      (by simpa only [prod_orient] using ik) (by simpa only [prod_orient] using jk)

end ProximityGap.DyadicExceptionalConic
#print axioms ProximityGap.DyadicExceptionalConic.five
