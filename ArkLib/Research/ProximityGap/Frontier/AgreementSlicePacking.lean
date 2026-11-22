/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237

/-!
# Two-block bounds for arbitrary-center Reed–Solomon lists

Fix a sample of coordinates and condition on the number of agreements in it.
Cauchy–Schwarz on each of the two coordinate blocks bounds the size of each
such fibre. Counting the samples recovers a bound on the whole list.
-/

namespace ProximityGap.AgreementSlicePacking

open Finset Code

variable {I J : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in
private theorem mult_sum (T : Finset J) (S : J → Finset I) (R : Finset I) (a : ℕ)
    (ha : ∀ j ∈ T, ((S j) ∩ R).card = a) :
    ∑ x ∈ R, (∑ j ∈ T, if x ∈ S j then 1 else 0) = T.card * a := by
  rw [sum_comm]
  have row (j) (hj : j ∈ T) : (∑ x ∈ R, if x ∈ S j then 1 else 0) = a := by
    rw [sum_boole]
    simpa [Finset.filter_mem_eq_inter, inter_comm] using ha j hj
  exact (sum_congr rfl row).trans (by simp)

private theorem mult_sq (T : Finset J) (S : J → Finset I) (t s : ℕ)
    (ht : ∀ i ∈ T, (S i).card = t)
    (hp : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (S i ∩ S j).card ≤ s) :
    (∑ x : I, (∑ j ∈ T, if x ∈ S j then 1 else 0)^2) ≤
      T.card * (t + (T.card-1)*s) := by
  classical
  let f (i : J) (x : I) : ℕ := if x ∈ S i then 1 else 0
  have cross (i j : J) : (∑ x : I, f i x * f j x) = (S i ∩ S j).card := by
    simp [f, mul_ite, inter_comm]
  have row (i) (hi : i ∈ T) : (∑ j ∈ T, (S i ∩ S j).card) ≤ t + (T.card-1)*s := by
    rw [← add_sum_erase _ _ hi, inter_self, ht i hi]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _j ∈ T.erase i, s := sum_le_sum fun j hj =>
        hp i hi j (mem_erase.mp hj).2 (mem_erase.mp hj).1.symm
      _ = _ := by simp [card_erase_of_mem hi]
  change (∑ x : I, (∑ j ∈ T, f j x)^2) ≤ _
  simp_rw [sq, sum_mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ i ∈ T, ∑ j ∈ T, (S i ∩ S j).card := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      simp only [cross]
    _ ≤ ∑ _i ∈ T, (t+(T.card-1)*s) := sum_le_sum row
    _ = _ := by simp

/-- The single-block second-moment bound, including the list cardinality in
the diagonal term. -/
theorem plotkin (T : Finset J) (S : J → Finset I) (t d : ℕ)
    (ht : ∀ i ∈ T, (S i).card = t)
    (hp : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (S i ∩ S j).card ≤ d) :
    T.card * t ^ 2 ≤ Fintype.card I * (t + (T.card - 1) * d) := by
  classical
  obtain he | hne := T.eq_empty_or_nonempty
  · simp [he]
  let c (x : I) := ∑ j ∈ T, if x ∈ S j then 1 else 0
  have hs : ∑ x, c x = T.card * t := mult_sum T S univ t (by simpa using ht)
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset I)) (f := c)
  rw [hs, card_univ] at h
  have ss := mult_sq T S t d ht hp
  change (∑ x, c x ^ 2) ≤ _ at ss
  have aux : T.card * (T.card * t ^ 2) ≤
      T.card * (Fintype.card I * (t + (T.card - 1) * d)) := by
    calc
      _ = (T.card * t) ^ 2 := by ring
      _ ≤ Fintype.card I * (T.card * (t + (T.card - 1) * d)) :=
        h.trans (Nat.mul_le_mul_left _ ss)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left aux (card_pos.mpr hne)

/-- The local Plotkin inequality for blocks with exactly `a` marked and `b`
unmarked sites, in regions of size `w` and `z`. -/
theorem slice_bound (T : Finset J) (S : J → Finset I) (R : Finset I) (w z t s a b : ℕ)
    (hw : R.card = w) (hz : Rᶜ.card = z) (ht : ∀ i ∈ T, (S i).card = t)
    (ha : ∀ i ∈ T, (S i ∩ R).card = a) (hb : ∀ i ∈ T, (S i ∩ Rᶜ).card = b)
    (hp : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (S i ∩ S j).card ≤ s) :
    T.card * (a^2*z+b^2*w) ≤ w*z*(t+(T.card-1)*s) := by
  classical
  obtain he | hne := T.eq_empty_or_nonempty
  · simp [he]
  let c (x : I) : ℕ := ∑ j ∈ T, if x ∈ S j then 1 else 0
  have h1 := sq_sum_le_card_mul_sum_sq (s := R) (f := c)
  have h2 := sq_sum_le_card_mul_sum_sq (s := Rᶜ) (f := c)
  rw [show (∑ x ∈ R, c x) = _ from mult_sum T S R a ha, hw] at h1
  rw [show (∑ x ∈ Rᶜ, c x) = _ from mult_sum T S Rᶜ b hb, hz] at h2
  have h3 := mult_sq T S t s ht hp
  change (∑ x : I, (c x)^2) ≤ _ at h3
  rw [← sum_add_sum_compl R] at h3
  refine le_of_mul_le_mul_left (a := T.card) ?_ hne.card_pos
  calc
    _ = (T.card*a)^2*z+(T.card*b)^2*w := by ring
    _ ≤ (w * ∑ x ∈ R, c x^2)*z+(z * ∑ x ∈ Rᶜ, c x^2)*w :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_right _ h2)
    _ = w*z*((∑ x ∈ R, c x^2)+(∑ x ∈ Rᶜ, c x^2)) := by ring
    _ ≤ w*z*(T.card*(t+(T.card-1)*s)) := Nat.mul_le_mul_left _ h3
    _ = _ := by ring

private theorem samples_of_block (S : Finset I) (w a : ℕ) (ha : a ≤ w) :
    S.card.choose a * (Fintype.card I - S.card).choose (w-a) ≤
      ((univ.powersetCard w).filter fun R => (S ∩ R).card = a).card := by
  classical
  let T := S.powersetCard a ×ˢ Sᶜ.powersetCard (w-a)
  have splitPair (x : Finset I × Finset I) (hx : x ∈ T) :
      S ∩ (x.1 ∪ x.2) = x.1 ∧ Sᶜ ∩ (x.1 ∪ x.2) = x.2 := by
    obtain ⟨h1,h2⟩ := mem_product.mp hx
    obtain ⟨h1,-⟩ := mem_powersetCard.mp h1
    obtain ⟨h2,-⟩ := mem_powersetCard.mp h2
    constructor <;> ext i <;> simp only [mem_inter, mem_union, mem_compl]
    all_goals
      have hL : i ∈ x.1 → i ∈ S := fun h => h1 h
      have hR : i ∈ x.2 → i ∉ S := fun h => mem_compl.mp (h2 h)
      tauto
  have bound : T.card ≤ _ := card_le_card_of_injOn (fun x : Finset I × Finset I => x.1 ∪ x.2)
    (t := (univ.powersetCard w).filter fun R => (S ∩ R).card = a) (by
      intro x hx
      obtain ⟨h1,h2⟩ := mem_product.mp hx
      obtain ⟨hl,hlc⟩ := mem_powersetCard.mp h1
      obtain ⟨hr,hrc⟩ := mem_powersetCard.mp h2
      have hd : Disjoint x.1 x.2 := Finset.disjoint_left.mpr fun i hi hj =>
        mem_compl.mp (hr hj) (hl hi)
      apply mem_filter.mpr
      exact ⟨mem_powersetCard.mpr ⟨subset_univ _, by rw [card_union_of_disjoint hd,hlc,hrc]; omega⟩,
        (splitPair x hx).1 ▸ hlc⟩) (by
      intro x hx y hy h
      change x.1 ∪ x.2 = y.1 ∪ y.2 at h
      exact Prod.ext (by rw [← (splitPair x hx).1, ← (splitPair y hy).1, h])
        (by rw [← (splitPair x hx).2, ← (splitPair y hy).2,h]))
  simpa [T,card_compl] using bound

/-- Incidence averaging across samples. The local inequality can be checked
with integer arithmetic at any block length. -/
theorem block_bound {m : ℕ} (S : Fin m → Finset I) (w t s a L : ℕ) (ha : a ≤ w)
    (ht : ∀ i, (S i).card = t)
    (hp : Pairwise fun i j => (S i ∩ S j).card ≤ s)
    (localBound : ∀ M : ℕ, M*(a^2*(Fintype.card I-w)+(t-a)^2*w) ≤
      w*(Fintype.card I-w)*(t+(M-1)*s) → M ≤ L) :
    m * (t.choose a * (Fintype.card I-t).choose (w-a)) ≤
      (Fintype.card I).choose w * L := by
  classical
  let samples := (univ : Finset I).powersetCard w
  let cond (i : Fin m) (R : Finset I) := (S i ∩ R).card = a
  have fiber (R : Finset I) (hR : R ∈ samples) : (univ.filter fun i => cond i R).card ≤ L := by
    apply localBound
    have hr := (mem_powersetCard.mp hR).2
    apply slice_bound _ S R _ _ _ _ _ _ hr (by rw [card_compl,hr]) (fun i _ => ht i)
    · exact fun i hi => (mem_filter.mp hi).2
    · intro i hi
      have hpartition := card_union_add_card_inter (S i ∩ R) (S i ∩ Rᶜ)
      have hu : (S i ∩ R) ∪ (S i ∩ Rᶜ) = S i := by ext; simp; tauto
      have hd : (S i ∩ R) ∩ (S i ∩ Rᶜ) = ∅ := by ext; simp; tauto
      rw [hu, hd, card_empty, ht i] at hpartition
      have ha' : (S i ∩ R).card = a := (mem_filter.mp hi).2
      omega
    · exact fun _ _ _ _ hne => hp hne
  have h := card_mul_le_card_mul (s := (univ : Finset (Fin m))) (t := samples) cond
    (fun i _ => (ht i ▸ samples_of_block (S i) w a ha))
    (fun R hR => fiber R hR)
  simpa [samples] using h

/-- Any list decodable by a two-block slice certificate obeys the bound at every
received word and every finite interleaving width. -/
theorem interleaved_bound {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k t arity w a L B : ℕ) (δ : ℝ) (ha : a ≤ w)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (localBound : ∀ M : ℕ, M*(a^2*(Fintype.card I-w)+(t-a)^2*w) ≤
      w*(Fintype.card I-w)*(t+(M-1)*(k-1)) → M ≤ L)
    (budget : (Fintype.card I).choose w * L <
      (B+1) * (t.choose a * (Fintype.card I-t).choose (w-a))) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (B : ℕ∞) := by
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k t arity B δ hδ
  intro m S ht hp
  have h := (block_bound S w t (k-1) a L ha ht hp localBound).trans_lt budget
  by_contra! hmore
  exact (not_lt_of_ge (Nat.mul_le_mul_right _ hmore)) h

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

set_option maxRecDepth 10000

/-- The 237-bit budget holds on every length-1024 evaluation domain over any
field at these four agreement counts, for arbitrary centers and interleavings.
Its numerical value is calibrated to the field of order `P`. -/
theorem length1024 {F : Type*} [Field F] [Nonempty I] (D : I ↪ F) (hn : Fintype.card I = 1024)
    (k t arity : ℕ) (h : (k=512 ∧ t=702) ∨ (k=256 ∧ t=479) ∨
      (k=128 ∧ t=315) ∨ (k=64 ∧ t=191)) (δ : ℝ) (hδ : δ * 1024 < 1025 - t) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (I → F))) δ ≤
      (P / 2^128 : ℕ) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  case' inl => apply interleaved_bound D 512 702 arity 131 31 363 _ δ
  case' inr.inl => apply interleaved_bound D 256 479 arity 389 269 479 _ δ
  case' inr.inr.inl => apply interleaved_bound D 128 315 arity 128 98 320 _ δ
  case' inr.inr.inr => apply interleaved_bound D 64 191 arity 58 50 187 _ δ
  all_goals first
    | decide
    | (rw [hn]; norm_num at hδ ⊢; linarith)
    | (rw [hn]; intro M; cases M <;> norm_num; omega)
    | (rw [hn]; simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

/-- On the 128-site subdomain the same budget holds at 67 agreements in
dimension 64. -/
theorem length128 {F : Type*} [Field F] [Nonempty I] (D : I ↪ F) (hn : Fintype.card I = 128)
    (arity : ℕ) (δ : ℝ) (hδ : δ * 128 < 62) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D 64 : Set (I → F))) δ ≤
      (P / 2^128 : ℕ) := by
  apply interleaved_bound D 64 67 arity 61 2 31 _ δ (by decide)
  · rw [hn]; norm_num; exact hδ
  · rw [hn]; intro M; cases M <;> norm_num; omega
  · rw [hn]; simp only [Nat.choose_eq_descFactorial_div_factorial]; decide

end ProximityGap.AgreementSlicePacking

#print axioms ProximityGap.AgreementSlicePacking.length1024
#print axioms ProximityGap.AgreementSlicePacking.length128
