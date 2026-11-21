/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.QuotientDeepCore
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius

/-! # A quantitative DEEP-quotient transfer on an arbitrary evaluation domain

The sum of evaluation-image deficits, over all allowed off-domain points, is at
most the sum of the pairwise difference degrees. No simultaneous separation
hypothesis is necessary. -/

set_option autoImplicit false
namespace ProximityGap.DeepListMcaTransfer
open Polynomial Finset Code
open scoped NNReal ENNReal
variable {F : Type} [Field F] [DecidableEq F]

private theorem filter_equal_le (A : Finset F) (f g : F[X]) {k : ℕ}
    (hne : f ≠ g) (hf : f.natDegree ≤ k) (hg : g.natDegree ≤ k) :
    (A.filter fun z => f.eval z = g.eval z).card ≤ k := by
  let R := f-g
  have hR : R ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (A.filter fun z => f.eval z = g.eval z) ⊆ R.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hR]
    exact (show (f-g).eval z = 0 by simp only [eval_sub, (mem_filter.mp hz).2, sub_self])
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' R).trans ((natDegree_sub_le ..).trans (max_le hf hg))))

/-- The number of collisions lost by using a single evaluation of each polynomial,
summed over all test points, is bounded by k times the number of unordered pairs. -/
theorem sum_evaluation_deficit_le (A : Finset F) (L : Finset F[X]) {k : ℕ}
    (hdeg : ∀ f ∈ L, f.natDegree ≤ k) :
    ∑ z ∈ A, (L.card - (L.image (fun f => f.eval z)).card) ≤ k * L.card.choose 2 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp
  | @insert f L hf ih =>
    have hd : ∀ g ∈ L, g.natDegree ≤ k := fun g hg => hdeg g (mem_insert_of_mem hg)
    have hdf := hdeg f (mem_insert_self ..)
    let T := A.filter (fun z => f.eval z ∈ L.image (fun g => g.eval z))
    have hT : T ⊆ L.biUnion (fun g => A.filter fun z => f.eval z = g.eval z) := by
      intro z hz
      obtain ⟨hz,hg⟩ := mem_filter.mp hz
      obtain ⟨g,hg,he⟩ := mem_image.mp hg
      exact mem_biUnion.mpr ⟨g,hg,mem_filter.mpr ⟨hz,he.symm⟩⟩
    have hb : T.card ≤ k * L.card := calc
      T.card ≤ _ := card_le_card hT
      _ ≤ ∑ g ∈ L, (A.filter fun z => f.eval z = g.eval z).card := card_biUnion_le
      _ ≤ ∑ _g ∈ L, k := sum_le_sum fun g hg =>
        filter_equal_le A f g (fun h => hf (h ▸ hg)) hdf (hd g hg)
      _ = _ := by simp [Nat.mul_comm]
    have step (z : F) : (insert f L).card - ((insert f L).image (fun g => g.eval z)).card =
        (L.card - (L.image (fun g => g.eval z)).card) +
          (if f.eval z ∈ L.image (fun g => g.eval z) then 1 else 0) := by
      rw [card_insert_of_notMem hf, Finset.image_insert]
      have him : (L.image (fun g => g.eval z)).card ≤ L.card := card_image_le
      split_ifs with h
      · rw [insert_eq_of_mem h]
        omega
      · rw [card_insert_of_notMem h]
        omega
    simp_rw [step]
    rw [sum_add_distrib, Finset.sum_boole]
    rw [card_insert_of_notMem hf, Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add]
    exact (Nat.add_le_add (ih hd) hb).trans_eq (Nat.add_comm ..)

variable {I : Type} [Fintype I]

/-- Distinct labels can be retained even if some pairs collide at every possible
DEEP point. This form permits a source list larger than the target budget. -/
theorem exists_deep_image_gt [Fintype F] (D : I ↪ F) (L : Finset F[X]) {k B : ℕ}
    (hdeg : ∀ f ∈ L, f.natDegree ≤ k)
    (hroom : k * L.card.choose 2 <
      (Fintype.card F - Fintype.card I) * (L.card - B)) :
    ∃ z : F, (∀ i, D i ≠ z) ∧ B < (L.image (fun f => f.eval z)).card := by
  classical
  let A := (univ : Finset F) \ univ.map D
  have hA : A.card = Fintype.card F - Fintype.card I := by
    simp [A, card_sdiff_of_subset (Finset.subset_univ _)]
  by_contra! h
  have hs := sum_evaluation_deficit_le A L hdeg
  have hl : A.card * (L.card-B) ≤ ∑ z ∈ A, (L.card - (L.image (fun f => f.eval z)).card) := by
    calc
      A.card * (L.card-B) = ∑ _z ∈ A, (L.card-B) := by simp
      _ ≤ _ := sum_le_sum fun z hz => Nat.sub_le_sub_left (h z (fun i hi =>
        (mem_sdiff.mp hz).2 (mem_map.mpr ⟨i,mem_univ _,hi⟩))) _
  rw [hA] at hl
  exact (not_lt_of_ge (hl.trans hs)) hroom

open ArkLib.ProximityGap.QuotientCore

/-- One off-domain DEEP evaluation gives a bad scalar at the same agreement threshold. -/
theorem quotient_event (D : I ↪ F) {k : ℕ} (hk : 0 < k) (z : F)
    (hz : ∀ i, D i ≠ z) (u : I → F) (f : F[X]) (hdeg : f.natDegree ≤ k)
    (S : Finset I) (δ : ℝ≥0) (hsize : (1-δ) * Fintype.card I ≤ (S.card : ℝ≥0))
    (hsk : k < S.card) (hagr : ∀ i ∈ S, u i = f.eval (D i)) :
    mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ
      (fun i => u i * (D i - z)⁻¹) (fun i => (D i - z)⁻¹) (-(f.eval z)) := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨q, hq⟩ := quotient_exists f z 1
  have hqdeg := quotient_natDegree_le (m := 1) (r := k+1) (by decide) (by omega)
    (by simpa using hdeg) hq
  simp only [Nat.mul_one] at hqdeg
  have hqk : q.natDegree < k := by omega
  refine ⟨S, hsize, ⟨fun i => q.eval (D i),
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨q,hqk,fun _ => rfl⟩, ?_⟩, ?_⟩
  · intro i hi
    have h := congrArg (eval (D i)) hq
    simp only [eval_sub, eval_C, eval_mul, eval_comp, eval_pow, eval_X, pow_one] at h
    simp only [smul_eq_mul, hagr i hi]
    field_simp [sub_ne_zero.mpr (hz i)]
    linear_combination -h
  · rintro ⟨_, _, v, hv, hpair⟩
    obtain ⟨g,hg,he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
    have hb := farness_card_le (S.map D) z (m := 1) hk (by decide) g hg
    have hsub : S.map D ⊆ (S.map D).filter (fun x => g.eval x * (x ^ 1 - z) = 1) := by
      intro x hx
      refine mem_filter.mpr ⟨hx, ?_⟩
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      rw [pow_one, he, (hpair i hi).2, inv_mul_cancel₀ (sub_ne_zero.mpr (hz i))]
    have hh := (card_le_card hsub).trans hb
    simp only [card_map] at hh
    omega

open Classical in
/-- Transfer a scalar list in dimension k+1 to bad randomizers in dimension k.
Both rows use a single off-domain point and each quotient retains its original
agreement coordinates. The integer t is the number of required agreements. -/
theorem exists_bad_count_of_list [Fintype F] (D : I ↪ F) (δ : ℝ≥0) {k t B L : ℕ}
    (hk : 0 < k) (hkt : k < t) (htn : t ≤ Fintype.card I)
    (hδ : (1-δ) * (Fintype.card I : ℝ≥0) ≤ t)
    (hlist : (L : ℕ∞) < Lambda (ReedSolomon.code D (k+1) : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / (Fintype.card I : ℝ)))
    (hroom : k * (L+1).choose 2 < (Fintype.card F - Fintype.card I) * (L+1-B)) :
    ∃ u₀ u₁ : I → F, B <
      (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card := by
  classical
  let C := (ReedSolomon.code D (k+1) : Set (I → F))
  let r := (((Fintype.card I - t : ℕ) : ℝ) / (Fintype.card I : ℝ))
  obtain ⟨u,W,hW,hlarge⟩ : ∃ (u : I → F) (W : Finset (I → F)),
      (∀ c ∈ W, c ∈ closeCodewordsRel C u r) ∧ L < W.card := by
    by_contra! h
    exact (not_le_of_gt hlist) (Lambda_le_of_forall_finset_card_le fun u W hW => h u W hW)
  obtain ⟨V,hVW,hV⟩ := exists_subset_card_eq (show L+1 ≤ W.card by omega)
  have hclose (w : V) := hW w (hVW w.property)
  have hex (w : V) := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp
    (mem_closeCodewordsRel_iff.mp (hclose w)).1
  choose rep hd he using hex
  let P := univ.image rep
  have hin : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact ((he a i).symm.trans (congrArg (eval (D i)) hab)).trans (he b i)
  have hP : P.card = L+1 := by simp [P,card_image_of_injective _ hin, hV]
  have hdeg : ∀ f ∈ P, f.natDegree ≤ k := by
    intro f hf
    obtain ⟨w,_,rfl⟩ := mem_image.mp hf
    exact Nat.le_of_lt_succ (hd w)
  obtain ⟨z,hz,hsep⟩ := exists_deep_image_gt D P hdeg (hP ▸ hroom)
  let u₀ := fun i => u i * (D i - z)⁻¹
  let u₁ := fun i => (D i - z)⁻¹
  let vals := (P.image (fun f => f.eval z)).map (Equiv.neg F).toEmbedding
  refine ⟨u₀,u₁, (show B < vals.card by simpa [vals] using hsep).trans_le (card_le_card ?_)⟩
  intro γ hγ
  obtain ⟨v,hv,rfl⟩ := mem_map.mp hγ
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hv
  obtain ⟨w,_,rfl⟩ := mem_image.mp hf
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  let S := univ.filter (fun i => (w : I → F) i = u i)
  have hw := (mem_closeCodewordsRel_iff.mp (hclose w)).2
  have hn := lt_of_lt_of_le (Nat.zero_lt_of_lt hkt) htn
  have hr : r = 1 - (t : ℝ) / Fintype.card I := by
    dsimp [r]
    rw [Nat.cast_sub htn, sub_div, div_self (by exact_mod_cast hn.ne')]
  rw [hr] at hw
  have htS : t ≤ S.card := by
    exact_mod_cast (relHammingDist_le_one_sub_div_iff hn).mp hw
  exact quotient_event D hk z hz u (rep w) (Nat.le_of_lt_succ (hd w)) S δ
    (hδ.trans (by exact_mod_cast htS)) (hkt.trans_le htS)
    (fun i hi => (mem_filter.mp hi).2.symm.trans (he w i).symm)

#print axioms sum_evaluation_deficit_le
#print axioms exists_bad_count_of_list
end ProximityGap.DeepListMcaTransfer
