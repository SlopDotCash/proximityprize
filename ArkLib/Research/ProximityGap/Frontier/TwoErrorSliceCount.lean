/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceRows
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceAveraging
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection

/-! # The list-size bound from the two-error slice certificate -/
namespace ProximityGap.TwoErrorSlice

open Finset Polynomial Code

variable {I J F : Type*} [Fintype I] [DecidableEq I] [Field F]

private theorem row_arithmetic (e : ℕ) (hlo : 3 ≤ e) (hhi : e ≤ 62) :
    66*345960 ≤ (e.choose 2 - e/2) * ((128-e).choose (63-e) * 186) := by
  interval_cases e <;> simp only [Nat.choose_eq_descFactorial_div_factorial] <;> decide

/-- A lower bound on all one-site extensions of a pair of true errors gives
a sum over all fixed-size samples of one codeword. -/
theorem row_from_extensions (D : I ↪ F) (E : Finset I) (w : Finset I → ℕ)
    {n r C : ℕ} (hn : Fintype.card I=n) (hr : r+2 ≤ n) (hlo : 3≤E.card) (hhi : E.card≤r+1)
    (extn : ∀ A : Finset I, A.card=2 → A⊆E → (∀ u∈A,∀ v∈A,u≠v → D u≠-D v) →
      ∀ Q ⊆ univ \ E, ((univ \ E) \ Q).card=n-r-1 →
        C ≤ ∑ x ∈ (univ \ E) \ Q, w ((E \ A) ∪ insert x Q)) :
    (E.card.choose 2-E.card/2)*((n-E.card).choose (r+2-E.card)*C) ≤
      (n-r-1)*∑ R ∈ (univ : Finset I).powersetCard r,w R := by
  classical
  let G := univ \ E
  let l := r+2-E.card
  let clean := (E.powersetCard 2).filter fun A => ∀ u∈A,∀ v∈A,u ≠ v → D u ≠ -D v
  let samples := (univ : Finset I).powersetCard r
  let pairs := clean ×ˢ G.powersetCard l
  let sample (p : Finset I × Finset I) := (E \ p.1) ∪ p.2
  have cardG : G.card=n-E.card := by simp [G,card_sdiff_of_subset (subset_univ E),hn]
  have indexed {p : Finset I × Finset I} (hp : p ∈ pairs) :
      p.1 ⊆ E ∧ p.1.card=2 ∧ p.2 ⊆ G ∧ p.2.card=l := by
    obtain ⟨h1,h2⟩ := mem_product.mp hp
    have h1' := mem_powersetCard.mp (mem_filter.mp h1).1
    have h2' := mem_powersetCard.mp h2
    exact ⟨h1'.1,h1'.2,h2'.1,h2'.2⟩
  have image_subset : pairs.image sample ⊆ samples := by
    intro R hR
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
    obtain ⟨h1,hc1,h2,hc2⟩ := indexed hp
    have dis : Disjoint (E \ p.1) p.2 := disjoint_left.mpr fun x hx hy =>
      (mem_sdiff.mp (h2 hy)).2 (mem_sdiff.mp hx).1
    apply mem_powersetCard.mpr
    use subset_univ _
    change ((E \ p.1) ∪ p.2).card=r
    rw [card_union_of_disjoint dis,card_sdiff_of_subset h1,hc1,hc2]
    dsimp [l]; omega
  have reconstruct {p : Finset I × Finset I} (hp : p ∈ pairs) :
      E \ sample p=p.1 ∧ G ∩ sample p=p.2 := by
    obtain ⟨h1,-,h2,-⟩ := indexed hp
    constructor <;> ext x <;> simp only [sample,G,mem_union,mem_inter,mem_sdiff,mem_univ,true_and]
    all_goals
      have he : x∈p.1 → x∈E := fun h => h1 h
      have hne : x∈p.2 → x∉E := fun h => (mem_sdiff.mp (h2 h)).2
      tauto
  have hinj : (↑pairs : Set _).InjOn sample := by
    intro p hp q hq he
    exact Prod.ext (by rw [← (reconstruct hp).1,he,(reconstruct hq).1])
      (by rw [← (reconstruct hp).2,he,(reconstruct hq).2])
  have total : (∑ A ∈ clean, ∑ S ∈ G.powersetCard l, w (sample (A,S))) ≤
      ∑ R ∈ samples, w R := by
    rw [← sum_product clean (G.powersetCard l) (fun p => w (sample p))]
    change (∑ p ∈ pairs, w (sample p)) ≤ _
    rw [← sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg image_subset (fun _ _ _ => Nat.zero_le _)
  have each (A) (hA : A∈clean) : G.card.choose l*C ≤
      (n-r-1)*∑ S ∈ G.powersetCard l, w (sample (A,S)) := by
    obtain ⟨hA',hc⟩ := mem_filter.mp hA
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hA'
    apply TwoErrorSliceAveraging.sample_average_general G l C (n-r-1) _ (by dsimp [l]; omega) _
      (by rw [cardG]; dsimp [l]; omega) (by rw [cardG]; dsimp [l]; omega)
    intro Q hQ
    obtain ⟨hq,hcQ⟩ := mem_powersetCard.mp hQ
    apply extn A hcard hsub hc Q hq
    change (G\Q).card=n-r-1
    rw [card_sdiff_of_subset hq,hcQ,cardG]
    dsimp [l]; omega
  have sm := sum_le_sum each
  rw [sum_const,nsmul_eq_mul, ← mul_sum] at sm
  have hc : E.card.choose 2-E.card/2 ≤ clean.card := by
    apply (TwoErrorSliceAveraging.clean_pairs_lower D E).trans_eq
    apply congrArg Finset.card
    ext A
    simp [clean]
  change (E.card.choose 2-E.card/2)*((n-E.card).choose l*C) ≤ (n-r-1)*∑ R ∈ samples,w R
  rw [← cardG]
  exact (Nat.mul_le_mul_right _ hc).trans (sm.trans (Nat.mul_le_mul_left _ total))

/-- Every word with between 3 and 62 errors receives at least 345960 units. -/
theorem row (D : I ↪ F) (cert : PenaltyBound D) (hn : Fintype.card I=128)
    (E : Finset I) (err : I → F) (herr : ∀ x ∈ E, err x ≠ 0)
    (hlo : 3 ≤ E.card) (hhi : E.card ≤ 62) :
    345960 ≤ ∑ R ∈ (univ : Finset I).powersetCard 61, credit D E err R := by
  apply Nat.le_of_mul_le_mul_left (c := 66) _ (by decide)
  apply (row_arithmetic E.card hlo hhi).trans
  exact row_from_extensions D E (credit D E err) (n:=128) (r:=61) (C:=186)
    hn (by decide) hlo hhi (fun A hA sub cle Q hQ size =>
      last_site D cert E A Q err herr hA sub cle hQ size)

/-- Fix a scalar center and a finite family of distinct candidate polynomials.
A word with at most two errors is unique. Otherwise the row and column counts
give the stated bound. -/
theorem family_bound (D : I ↪ F) (cert : PenaltyBound D) (hn : Fintype.card I=128)
    (P : J → F[X]) (hin : Function.Injective P) (W : I → F) (T : Finset J)
    (E : J → Finset I) (hE : ∀ j ∈ T, ∀ x, x ∈ E j ↔ (P j).eval (D x) ≠ W x)
    (hdeg : ∀ j ∈ T, (P j).natDegree < 64) (hsize : ∀ j ∈ T, (E j).card ≤ 62) :
    T.card ≤ 361269899996423739323753777598085 := by
  classical
  by_cases small : ∃ j ∈ T, (E j).card ≤ 2
  · obtain ⟨j,hj,hs⟩ := small
    have hsub : T ⊆ {j} := by
      intro i hi
      simp only [mem_singleton]
      by_contra hne
      let U := (univ : Finset I) \ (E i ∪ E j)
      have hu : U.card ≥ 64 := by
        have hc := card_union_le (E i) (E j)
        have hi' := hsize i hi
        dsimp [U]; rw [card_sdiff_of_subset (subset_univ _),card_univ,hn]
        omega
      have hr (x) (hx : x∈U) : (P i).eval (D x)=(P j).eval (D x) := by
        have hh := (mem_sdiff.mp hx).2
        have hai : x∉E i := fun h => hh (mem_union_left _ h)
        have haj : x∉E j := fun h => hh (mem_union_right _ h)
        rw [not_ne_iff.mp (fun h => hai ((hE i hi x).mpr h)),
          not_ne_iff.mp (fun h => haj ((hE j hj x).mpr h))]
      exact hne (hin (eq_of_natDegree_lt_card_of_eval_eq (P i) (P j)
        (f := fun x : U => D x.val) (D.injective.comp Subtype.val_injective)
        (fun x => hr x x.property) (by rw [Fintype.card_coe]; exact (max_lt (hdeg i hi) (hdeg j hj)).trans_le hu)))
    have h := card_le_card hsub
    simp only [card_singleton] at h
    omega
  let samples := (univ : Finset I).powersetCard 61
  let w j R := credit D (E j) (fun x => (P j).eval (D x)-W x) R
  have hrow (j) (hj : j∈T) : 345960 ≤ ∑ R ∈ samples, w j R := row D cert hn (E j) _
    (fun x hx => sub_ne_zero.mpr ((hE j hj x).mp hx)) (by
      by_contra! h; exact small ⟨j,hj,by omega⟩) (hsize j hj)
  have hcol (R) (hR : R∈samples) : (∑ j∈T, w j R) ≤ 6 := by
    apply column D P hin W T E hE hdeg
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn,(mem_powersetCard.mp hR).2]
  have lo := sum_le_sum hrow
  rw [sum_comm] at lo
  have hi := lo.trans (sum_le_sum hcol)
  simp only [sum_const,nsmul_eq_mul,samples,card_powersetCard,card_univ,hn] at hi
  rw [show Nat.choose 128 61 = 20830822433793792809407642816305590400 by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide] at hi
  simp only [Nat.cast_id] at hi
  omega

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.family_bound
