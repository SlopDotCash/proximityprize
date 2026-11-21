/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.InterleavedCode.Projection
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Scalar and interleaved list budgets over a large field

For a linear code over a finite field, a linear combination of rows preserves every
coordinate of agreement. A finite list of interleaved words has a separating row
combination whenever its number of unordered pairs is at most the field cardinality.
Independently of the number of pairs, preserving the disagreement coordinates of
all but one list member suffices when each scalar list is smaller than the field.
At the prize tolerance this removes the width dependence for every field when
the length or the error count is at most the inverse tolerance.
-/

open Code
open scoped BigOperators

namespace ProximityGap.InterleavedListProjection

variable {F ι κ : Type*} [Field F] [Fintype F] [Fintype ι] [Fintype κ]

private noncomputable def project (w : ι → κ → F) : (κ → F) →ₗ[F] (ι → F) :=
  Fintype.linearCombination F (fun j i ↦ w i j)

private def constantOn (s : Finset (ι → κ → F)) : Submodule F (κ → F) where
  carrier := {l | ∀ x ∈ s, ∀ y ∈ s, project x l = project y l}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx y hy
    rw [map_add, map_add, ha x hx y hy, hb x hx y hy]
  smul_mem' := by
    intro a b hb x hx y hy
    rw [map_smul, map_smul, hb x hx y hy]

/-- A finite list can be separated by a single linear combination of its rows whenever
there are at most as many pairs as field elements. -/
theorem exists_separating_projection (s : Finset (ι → κ → F))
    (hs : s.card.choose 2 ≤ Nat.card F) :
    ∃ l : κ → F, Set.InjOn (fun w ↦ ∑ j, l j • (fun i ↦ w i j)) (↑s : Set (ι → κ → F)) := by
  classical
  have hproper : ∀ t ∈ s.powersetCard 2, constantOn t ≠ ⊤ := by
    intro t ht htop
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
    apply hxy
    funext i j
    have hj : Pi.single j (1 : F) ∈ constantOn ({x,y} : Finset _) := htop ▸ Submodule.mem_top
    have heq := hj x (by simp) y (by simp)
    simpa [project] using congrFun heq i
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_card_le
    (s.powersetCard 2) constantOn hproper (by simpa using hs)
  refine ⟨l, ?_⟩
  intro x hx y hy heq
  by_contra hxy
  apply hl {x,y} (Finset.mem_powersetCard.mpr ⟨by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hy'
    · exact hx
    · exact Finset.mem_singleton.mp hy' ▸ hy, by simp [hxy]⟩)
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact heq
  · exact heq.symm
  · rfl

omit [Fintype F] in
private theorem interleaved_le_of_separates [Nonempty ι] (C : Submodule F (ι → F))
    (δ : ℝ) (B : ℕ) (h : Lambda (C : Set (ι → F)) δ ≤ B)
    (separates : ∀ (f : ι → κ → F) (s : Finset (ι → κ → F)), s.card = B + 1 →
      (↑s : Set _) ⊆ closeCodewordsRel (interleavedCodeSet (C : Set (ι → F))) f δ →
      ∃ l : κ → F, Set.InjOn (fun w : ι → κ → F ↦ ∑ j, l j • (fun i ↦ w i j)) (↑s : Set (ι → κ → F))) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro f T hT
  by_contra! htoo
  obtain ⟨s, hsT, hcard⟩ := Finset.exists_subset_card_eq (show B+1 ≤ T.card by omega)
  obtain ⟨l, hsep⟩ := separates f s hcard (fun x hx ↦ hT x (hsT hx))
  let P (v : ι → κ → F) : ι → F := ∑ j, l j • (fun i ↦ v i j)
  have hclose : (↑(s.image P) : Set (ι → F)) ⊆ closeCodewordsRel (C : Set (ι → F)) (P f) δ := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hc, hd⟩ := mem_closeCodewordsRel_iff.mp (hT w (hsT hw))
    apply mem_closeCodewordsRel_iff.mpr
    refine ⟨C.sum_mem fun j _ ↦ C.smul_mem (l j) (hc j), ?_⟩
    have hdist : relHammingDist (P f) (P w) ≤ relHammingDist f w := by
      unfold relHammingDist
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hd' := hammingDist_comp_le_hammingDist (fun (_ : ι) (z : κ → F) ↦ ∑ j, l j * z j)
        (x := f) (y := w)
      have hP (v : ι → κ → F) : P v = fun i ↦ ∑ j, l j * v i j := by
        funext i
        simp [P, Finset.sum_apply]
      have hn : hammingDist (P f) (P w) ≤ hammingDist f w := by
        simpa only [hP] using hd'
      exact_mod_cast hn
    exact (show (relHammingDist (P f) (P w) : ℝ) ≤ relHammingDist f w by exact_mod_cast hdist).trans hd
  have hsize := (encard_le_Lambda_of_subset_closeCodewordsRel hclose).trans h
  have himage : (s.image P).card = s.card := Finset.card_image_of_injOn hsep
  simp only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at hsize
  omega

/-- At a budget with at most `q` forbidden pairs, a scalar list bound transfers at the
same radius to every interleaving of a linear code. -/
theorem interleaved_le_of_scalar_le [Nonempty ι] (C : Submodule F (ι → F)) (δ : ℝ) (B : ℕ)
    (hB : (B + 1).choose 2 ≤ Nat.card F) (h : Lambda (C : Set (ι → F)) δ ≤ B) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B :=
  interleaved_le_of_separates C δ B h fun _ s hs _ ↦ exists_separating_projection s (hs ▸ hB)

omit [Fintype F] in
private theorem scalar_le_of_interleaved_le [Nonempty ι] [Nonempty κ]
    (C : Submodule F (ι → F)) (δ : ℝ) (B : ℕ)
    (h : Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B) :
    Lambda (C : Set (ι → F)) δ ≤ B := by
  classical
  apply Lambda_le_iff_forall_encard_le.mpr
  intro f
  let e : F → (κ → F) := fun v _ ↦ v
  have hinj : Function.Injective e := fun _ _ heq ↦ congrFun heq (Classical.arbitrary κ)
  let S := closeCodewordsRel (C : Set (ι → F)) f δ
  have hmaps : (fun c ↦ e ∘ c) '' S ⊆
      closeCodewordsRel (interleavedCodeSet (κ := κ) (C : Set (ι → F))) (e ∘ f) δ := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hC, hd⟩ := mem_closeCodewordsRel_iff.mp hc
    apply mem_closeCodewordsRel_iff.mpr
    exact ⟨fun _ ↦ hC, by rw [relHammingDist_comp hinj]; exact hd⟩
  have hword : Set.InjOn (fun c : ι → F ↦ e ∘ c) S :=
    fun _ _ _ _ heq ↦ funext fun i ↦ hinj (congrFun heq i)
  exact hword.encard_image ▸ (encard_le_Lambda_of_subset_closeCodewordsRel hmaps).trans h

/-- A nonempty interleaving and its base code cross a small integer list budget
at precisely the same radii. -/
theorem list_budget_iff [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F)) (δ : ℝ)
    (B : ℕ) (hB : (B + 1).choose 2 ≤ Nat.card F) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B ↔
      Lambda (C : Set (ι → F)) δ ≤ B :=
  ⟨scalar_le_of_interleaved_le C δ B, interleaved_le_of_scalar_le C δ B hB⟩

/-- The list budget for 128 bits of security satisfies the pair hypothesis on
every field in the sub-256-bit prize envelope. -/
theorem prize_list_budget_iff [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F)) (δ : ℝ)
    (hq : Nat.card F < 2 ^ 256) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ (Nat.card F / 2 ^ 128 : ℕ) ↔
      Lambda (C : Set (ι → F)) δ ≤ (Nat.card F / 2 ^ 128 : ℕ) := by
  apply list_budget_iff
  let q := Nat.card F
  let B := q / 2 ^ 128
  have hB : B < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 128)).mpr
    norm_num [q] at hq ⊢
    exact hq
  have hround : 2 ^ 128 * B ≤ q := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self q (2 ^ 128)
  have hside : B + 1 ≤ 2 ^ 128 := hB
  have hmul : (B + 1) * B ≤ q := (Nat.mul_le_mul_right B hside).trans hround
  change (B + 1).choose 2 ≤ q
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ 2).trans (by simpa using hmul)

private theorem support_determines [Nonempty ι] (C : Submodule F (ι → F))
    (δ : ℝ) (B : ℕ) (hB : B < Nat.card F) (h : Lambda (C : Set (ι → F)) δ ≤ B)
    {f w v : ι → κ → F} (hw : w ∈ closeCodewordsRel (interleavedCodeSet (C : Set (ι → F))) f δ)
    (hv : v ∈ interleavedCodeSet (C : Set (ι → F)))
    (hs : ∀ i, f i = w i → w i = v i) : w = v := by
  classical
  obtain ⟨hwC, hd⟩ := mem_closeCodewordsRel_iff.mp hw
  by_contra hne
  obtain ⟨i, j, hij⟩ : ∃ i j, w i j ≠ v i j := by
    by_contra! he
    exact hne (funext fun i ↦ funext (he i))
  let d : ι → F := (fun x ↦ w x j) - (fun x ↦ v x j)
  have hdm : d ∈ C := C.sub_mem (hwC j) (hv j)
  have hd0 : d ≠ 0 := fun he ↦ hij (sub_eq_zero.mp (congrFun he i))
  let g : F → (ι → F) := fun z ↦ z • d
  have hg : Function.Injective g := smul_left_injective F hd0
  have hsub : (↑(Finset.univ.image g) : Set _) ⊆ closeCodewordsRel (C : Set (ι → F)) 0 δ := by
    intro u hu
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hu
    apply mem_closeCodewordsRel_iff.mpr
    refine ⟨C.smul_mem z hdm, ?_⟩
    have hdist : hammingDist (0 : ι → F) (g z) ≤ hammingDist f w := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      intro he
      have hzero : d x = 0 := sub_eq_zero.mpr (congrFun (hs x he) j)
      exact hx (by simp [g, hzero])
    rw [relHammingDist_coe] at hd ⊢
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hdist) (by positivity)).trans hd
  have hbad := (encard_le_Lambda_of_subset_closeCodewordsRel hsub).trans h
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hg, Finset.card_univ,
    Nat.cast_le] at hbad
  exact (not_le_of_gt hB) (by simpa [Nat.card_eq_fintype_card] using hbad)

private theorem budget_iff_of_error_bound [DecidableEq F] [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F))
    (δ : ℝ) (B E : ℕ) (hB : B < Nat.card F) (hn : B * E ≤ Nat.card F)
    (hE : ∀ f w : ι → κ → F, w ∈ closeCodewordsRel (interleavedCodeSet (C : Set (ι → F))) f δ →
      hammingDist f w ≤ E) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B ↔
      Lambda (C : Set (ι → F)) δ ≤ B := by
  classical
  refine ⟨scalar_le_of_interleaved_le C δ B, fun h ↦ interleaved_le_of_separates C δ B h ?_⟩
  intro f s hcard hclose
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  let mismatches (w : ι → κ → F) := Finset.univ.filter fun i ↦ w i ≠ f i
  let T := (s.erase a).sigma mismatches
  let bad (wi : Sigma (fun _ : ι → κ → F ↦ ι)) : Submodule F (κ → F) :=
    LinearMap.ker (Fintype.linearCombination F (fun j ↦ wi.1 wi.2 j - f wi.2 j))
  have hproper : ∀ wi ∈ T, bad wi ≠ ⊤ := by
    intro wi hwi htop
    have hne := (Finset.mem_filter.mp (Finset.mem_sigma.mp hwi).2).2
    apply hne
    funext j
    have hmem : Pi.single j (1 : F) ∈ bad wi := htop ▸ Submodule.mem_top
    simpa [bad, LinearMap.mem_ker, sub_eq_zero] using hmem
  have hcount : T.card ≤ Nat.card F := by
    calc
      T.card = ∑ w ∈ s.erase a, (mismatches w).card := Finset.card_sigma _ _
      _ ≤ ∑ _w ∈ s.erase a, E := by
        apply Finset.sum_le_sum
        intro w hw
        change hammingDist w f ≤ E
        rw [hammingDist_comm]
        exact hE f w (hclose (Finset.mem_of_mem_erase hw))
      _ = B * E := by simp [Finset.card_erase_of_mem ha, hcard]
      _ ≤ Nat.card F := hn
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_card_le T bad hproper hcount
  refine ⟨l, ?_⟩
  intro u hu v hv huv
  have directed (w y : ι → κ → F) (hw : w ∈ s) (hy : y ∈ s) (hyne : y ≠ a)
      (he : (∑ j, l j • fun i ↦ w i j) = (∑ j, l j • fun i ↦ y i j)) : w = y := by
    apply support_determines C δ B hB h (hclose hw) (mem_closeCodewordsRel_iff.mp (hclose hy)).1
    intro i hi
    rw [← hi]
    by_contra hne
    have hpair : (⟨y,i⟩ : Sigma (fun _ : ι → κ → F ↦ ι)) ∈ T :=
      Finset.mem_sigma.mpr ⟨Finset.mem_erase.mpr ⟨hyne,hy⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩⟩
    apply hl ⟨y,i⟩ hpair
    have heval := congrFun he i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hi] at heval
    simpa [bad, LinearMap.mem_ker, Fintype.linearCombination_apply, mul_sub, Finset.sum_sub_distrib,
      sub_eq_zero] using heval.symm
  by_cases hv' : v = a
  · by_cases hu' : u = a
    · exact hu'.trans hv'.symm
    · exact (directed v u hv hu hu' huv.symm).symm
  · exact directed u v hu hv hv' huv

/-- At most `B * E` forbidden row hyperplanes suffice at radii admitting
at most `E` errors, for any scalar budget below the field size. -/
theorem support_list_budget_iff_at_errors [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F))
    (δ : ℝ) (B E : ℕ) (hB : B < Nat.card F) (hn : B * E ≤ Nat.card F)
    (hδ : δ * (Fintype.card ι : ℝ) < E + 1) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B ↔
      Lambda (C : Set (ι → F)) δ ≤ B := by
  classical
  apply budget_iff_of_error_bound C δ B E hB hn
  intro f w hw
  have hd := (mem_closeCodewordsRel_iff.mp hw).2
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [relHammingDist_coe, div_le_iff₀ hnpos] at hd
  have hh : (hammingDist f w : ℝ) < E + 1 := hd.trans_lt hδ
  exact Nat.lt_succ_iff.mp (by exact_mod_cast hh)

/-- With at most `q` coordinate tests across all but one candidate, the scalar
and every positive-width interleaved list cross the same budget. -/
theorem support_list_budget_iff [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F))
    (δ : ℝ) (B : ℕ) (hB : B < Nat.card F) (hn : B * Fintype.card ι ≤ Nat.card F) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B ↔
      Lambda (C : Set (ι → F)) δ ≤ B := by
  classical
  exact budget_iff_of_error_bound C δ B _ hB hn fun _ _ _ ↦ hammingDist_le_card_fintype

/-- For every finite field and every code of length at most the security
denominator, scalar and positive-width interleaved lists cross the same budget. -/
theorem list_budget_iff_of_length_le [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F))
    (δ : ℝ) {Q : ℕ} (hQ : 1 < Q) (hn : Fintype.card ι ≤ Q) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ (Nat.card F / Q : ℕ) ↔
      Lambda (C : Set (ι → F)) δ ≤ (Nat.card F / Q : ℕ) := by
  apply support_list_budget_iff
  · exact Nat.div_lt_self (Nat.card_pos) hQ
  · exact (Nat.mul_le_mul_left _ hn).trans (Nat.div_mul_le_self _ _)

end ProximityGap.InterleavedListProjection

#print axioms ProximityGap.InterleavedListProjection.exists_separating_projection
#print axioms ProximityGap.InterleavedListProjection.list_budget_iff
#print axioms ProximityGap.InterleavedListProjection.prize_list_budget_iff

#print axioms ProximityGap.InterleavedListProjection.support_list_budget_iff
#print axioms ProximityGap.InterleavedListProjection.list_budget_iff_of_length_le
#print axioms ProximityGap.InterleavedListProjection.support_list_budget_iff_at_errors
