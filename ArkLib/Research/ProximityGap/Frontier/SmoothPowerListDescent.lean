/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothDeepMcaThreshold
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent
import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap

/-! # Lifting list lower bounds to larger smooth evaluation domains

A coordinate map with positive, equal-sized fibers preserves relative Hamming distance
under precomposition. When the coordinate map is given by a polynomial of degree `m`,
composition lifts dimension `j` Reed–Solomon words to dimension `j * m`. On smooth
domains, applying this to the power map transfers the small-domain prescribed-product
list obstruction to every admissible multiple of the base length and every nonempty width.
-/

set_option autoImplicit false
namespace ProximityGap.SmoothPowerListDescent
open Finset Code Polynomial
open scoped ENNReal

section Coordinates

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Repeating every coordinate equally often preserves relative Hamming distance. -/
theorem relHammingDist_pullback [Nonempty I] [Nonempty J] {A : Type*} [DecidableEq A]
    (π : I → J) {m : ℕ} (hm : 0 < m) (hfib : ∀ j, (univ.filter fun i => π i = j).card = m)
    (u v : J → A) : relHammingDist (u ∘ π) (v ∘ π) = relHammingDist u v := by
  have card_pull (S : Finset J) : (univ.filter fun i => π i ∈ S).card = S.card * m := by
    rw [← sum_card_fiberwise_eq_card_filter]
    exact sum_const_nat fun j _ => hfib j
  have hn : Fintype.card I = Fintype.card J * m := by simpa using card_pull univ
  have hd : hammingDist (u ∘ π) (v ∘ π) = hammingDist u v * m := by
    simpa [hammingDist, Function.comp_def] using card_pull (univ.filter fun j => u j ≠ v j)
  rw [relHammingDist, relHammingDist, hd, hn, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast hm.ne')

/-- A regular coordinate pullback taking codewords into codewords only increases the
largest list, at every relative radius. -/
theorem lambda_le_pullback {A : Type*} [Nonempty I] [Nonempty J]
    (π : I → J) {m : ℕ} (hm : 0 < m) (hfib : ∀ j, (univ.filter fun i => π i = j).card = m)
    {C : Set (J → A)} {D : Set (I → A)} (maps : ∀ c ∈ C, c ∘ π ∈ D) (δ : ℝ) :
    Lambda C δ ≤ Lambda D δ := by
  classical
  have surj : Function.Surjective π := by
    intro j
    obtain ⟨i, hi⟩ := card_pos.mp (hm.trans_eq (hfib j).symm)
    exact ⟨i, (mem_filter.mp hi).2⟩
  apply Lambda_le_iff_forall_encard_le.mpr
  intro f
  have inj : Set.InjOn (fun c : J → A => c ∘ π) (closeCodewordsRel C f δ) :=
    surj.injective_comp_right.injOn
  rw [← inj.encard_image]
  apply encard_le_Lambda_of_subset_closeCodewordsRel (f := f ∘ π)
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨hC, hd⟩ := mem_closeCodewordsRel_iff.mp hc
  apply mem_closeCodewordsRel_iff.mpr
  exact ⟨maps _ hC, by rwa [relHammingDist_pullback π hm hfib]⟩

end Coordinates

variable {I J F : Type} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] [DecidableEq J]
    [Field F]

/-- Composition with a degree-`m` polynomial with full fibers transfers base RS list
lower bounds at the same radius. -/
theorem rs_lambda_le (D : I ↪ F) (E : J ↪ F) (π : I → J) (P : F[X]) {j m : ℕ}
    (hm : 0 < m) (hj : 0 < j) (hP : P.natDegree = m) (hdom : ∀ i, P.eval (D i) = E (π i))
    (hfib : ∀ v, (univ.filter fun i => π i = v).card = m) (δ : ℝ) :
    Lambda (ReedSolomon.code E j : Set (J → F)) δ ≤
      Lambda (ReedSolomon.code D (j * m) : Set (I → F)) δ := by
  classical
  let : NeZero j := ⟨hj.ne'⟩
  apply lambda_le_pullback π hm hfib _ δ
  intro c hc
  obtain ⟨q, hq, he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (q.comp P)
  · rw [natDegree_comp, hP]
    exact Nat.mul_lt_mul_of_pos_right hq hm
  · intro i
    rw [eval_comp, hdom, he]
    rfl

/-- If the base prescribed-product count exceeds `B`, every larger smooth domain at
the same rate violates that list budget, even at width one. -/
theorem smooth_list_exceeds_of_count (κ : Type) [Nonempty κ] [Fintype F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] {m h j a B : ℕ} (hm : 0 < m)
    (hn : Fintype.card I = m * h) (hp : ∃ b : ℕ, h = 2 ^ b) (hj : 0 < j)
    (hB : h * Fintype.card F ^ a * B < h.choose (j + 1 + a)) :
    (B : ℕ∞) < Lambda (interleavedCodeSet (κ := κ) (ReedSolomon.code D (j * m) : Set (I → F)))
      (((h - (j + 1 + a) : ℕ) : ℝ) / (h : ℝ)) := by
  classical
  obtain ⟨V, hV, hmem, hfib, ⟨sm⟩, -⟩ := SmoothPowerMcaDescent.exists_smooth_base D hm hn hp
  let := sm
  let : Nonempty V := Fintype.card_pos_iff.mp (by obtain ⟨b, hb⟩ := hp; simp [hV, hb])
  let E := Function.Embedding.subtype (· ∈ V)
  let π (i : I) : V := ⟨D i ^ m, hmem i⟩
  have hf (v : V) : (univ.filter (fun i => π i = v)).card = m := by
    simpa [π, Subtype.ext_iff] using hfib v v.property
  have hbase := SmoothDeepMcaThreshold.smooth_list_lower E (a := a) hj (L := B)
    (by simpa [hV] using hB)
  simp only [Fintype.card_coe, hV] at hbase
  apply (hbase.trans_le (rs_lambda_le D E π (X ^ m) hm hj (by simp) (by simp [π, E]) hf _)).trans_le
  let e (x : F) : κ → F := fun _ => x
  apply Lambda_le_of_injective_comp (e := e)
  · exact fun _ _ he => congrFun he (Classical.arbitrary κ)
  · exact fun _ hc _ => hc

/-- Taking one extra agreement on the base gives a field-size-independent obstruction
at relative distance `(h - (j + 1))/h` on all smooth lengths `m * h`. -/
theorem smooth_list_exceeds (κ : Type) [Nonempty κ] [Finite F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] {m h j B : ℕ} (hm : 0 < m)
    (hn : Fintype.card I = m * h) (hp : ∃ b : ℕ, h = 2 ^ b) (hj : 0 < j)
    (hB : h * B < h.choose (j + 1)) :
    (B : ℕ∞) < Lambda (interleavedCodeSet (κ := κ) (ReedSolomon.code D (j * m) : Set (I → F)))
      (((h - (j + 1) : ℕ) : ℝ) / (h : ℝ)) := by
  classical
  let := Fintype.ofFinite F
  exact smooth_list_exceeds_of_count κ D (a := 0) hm hn hp hj (by simpa using hB)

end ProximityGap.SmoothPowerListDescent

#print axioms ProximityGap.SmoothPowerListDescent.relHammingDist_pullback
#print axioms ProximityGap.SmoothPowerListDescent.lambda_le_pullback
#print axioms ProximityGap.SmoothPowerListDescent.rs_lambda_le
#print axioms ProximityGap.SmoothPowerListDescent.smooth_list_exceeds_of_count
#print axioms ProximityGap.SmoothPowerListDescent.smooth_list_exceeds
