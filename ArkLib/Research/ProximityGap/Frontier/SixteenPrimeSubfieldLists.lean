/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ListScalarExtension
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus
import Mathlib.Algebra.Field.ZMod

/-! # Two explicit lists on the nonzero elements of the field of order seventeen

At half rate ten words lie within six errors of a single center. At quarter rate
eight cubic words lie within nine errors. The lists persist over field extensions
and at every nonempty interleaving width.
-/

namespace ProximityGap.SixteenPrimeSubfieldLists

open Finset Polynomial Code
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The multiplicative subgroup in exponent order. -/
def domain : Fin 16 ↪ ZMod 17 := ⟨fun i => 3 ^ i.val, by decide⟩

private def word {k : ℕ} (a : Fin k → ZMod 17) (i : Fin 16) : ZMod 17 :=
  ∑ j, a j * domain i ^ j.val

private theorem codeword {k : ℕ} (hk : 0 < k) (a : Fin k → ZMod 17) :
    word a ∈ ReedSolomon.code domain k := by
  let P : (ZMod 17)[X] := ∑ j, C (a j) * X ^ j.val
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval P
  · have h : P.natDegree ≤ k - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro j _
      exact (natDegree_C_mul_X_pow_le _ _).trans (by have := j.isLt; omega)
    omega
  · intro i
    simp [word, P, eval_finsetSum]

private def halfCenter : Fin 16 → ZMod 17 :=
  ![1, 1, 11, 0, 0, 0, 0, 0, 12, 0, 4, 0, 0, 0, 0, 0]

private def half : Fin 10 → Fin 8 → ZMod 17 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 14, 16, 11, 5, 6, 7, 9],
    ![3, 3, 2, 11, 6, 11, 11, 2], ![4, 11, 16, 10, 16, 10, 13, 6],
    ![5, 4, 8, 1, 15, 7, 4, 8], ![8, 8, 2, 9, 14, 6, 16, 6],
    ![12, 11, 7, 12, 4, 16, 9, 15], ![14, 1, 9, 15, 15, 5, 13, 14],
    ![15, 12, 9, 8, 3, 7, 5, 10], ![15, 14, 15, 14, 9, 5, 9, 5]]

private def quarterCenter (i : Fin 16) : ZMod 17 :=
  domain i ^ 5 * (1 + 5 * domain i ^ 8)

private def quarter (j : Fin 8) (i : Fin 4) : ZMod 17 :=
  let t : ZMod 17 := 9 ^ j.val
  ![3, 12, 11, 8] i * t ^ (3 + i.val)

private theorem from_table {s k e : ℕ} (hk : 0 < k)
    (center : Fin 16 → ZMod 17) (a : Fin s → Fin k → ZMod 17)
    (separate : Function.Injective (fun j => word (a j)))
    (close : ∀ j, hammingDist center (word (a j)) ≤ e)
    {F : Type*} [Field F] (f : ZMod 17 →+* F) (κ : Type*) [Nonempty κ] :
    (s : ℕ∞) ≤ Lambda (interleavedCodeSet (κ := κ)
      (ReedSolomon.code (domain.trans ⟨f, f.injective⟩) k : Set (Fin 16 → F))) (e / 16) := by
  let B := ReedSolomon.code domain k
  have mem : (↑(univ.image (fun j => word (a j))) : Set (Fin 16 → ZMod 17)) ⊆
      closeCodewordsRel (B : Set (Fin 16 → ZMod 17)) center (e / 16) := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := mem_image.mp hw
    refine mem_closeCodewordsRel_iff.mpr ⟨codeword hk _, ?_⟩
    simp only [relHammingDist, NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fin]
    exact div_le_div_of_nonneg_right (by exact_mod_cast close j) (by positivity)
  have h := encard_le_Lambda_of_subset_closeCodewordsRel mem
  rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ separate, card_univ,
    Fintype.card_fin] at h
  apply (h.trans (ListScalarExtension.lambda_le f domain k _)).trans
  let rep : F → κ → F := fun z _ => z
  let C' : Set (Fin 16 → F) := ReedSolomon.code (domain.trans ⟨f, f.injective⟩) k
  have maps : ∀ c ∈ C', rep ∘ c ∈ interleavedCodeSet (κ := κ) C' := by
    intro c hc j
    exact hc
  exact Lambda_le_of_injective_comp (e := rep)
    (fun _ _ eq => congrFun eq (Classical.arbitrary κ)) maps _

set_option maxRecDepth 16000 in
/-- Ten half-rate words meet a single six-error ball over every extension. -/
theorem half_ten {F : Type*} [Field F] (f : ZMod 17 →+* F) (κ : Type*) [Nonempty κ] :
    (10 : ℕ∞) ≤ Lambda (interleavedCodeSet (κ := κ)
      (ReedSolomon.code (domain.trans ⟨f, f.injective⟩) 8 : Set (Fin 16 → F))) (6 / 16) := by
  apply from_table (e := 6) (by decide) halfCenter half (by decide +kernel)
    (by decide +kernel) f κ

set_option maxRecDepth 16000 in
/-- Eight quarter-rate words meet a single nine-error ball over every extension. -/
theorem quarter_eight {F : Type*} [Field F] (f : ZMod 17 →+* F) (κ : Type*) [Nonempty κ] :
    (8 : ℕ∞) ≤ Lambda (interleavedCodeSet (κ := κ)
      (ReedSolomon.code (domain.trans ⟨f, f.injective⟩) 4 : Set (Fin 16 → F))) (9 / 16) := by
  apply from_table (e := 9) (by decide) quarterCenter quarter (by decide +kernel)
    (by decide +kernel) f κ

private theorem cap_of_incidence {F : Type*} [Field F] (D : Fin 16 ↪ F)
    (k t m B a : ℕ) (δ : ℝ) (hδ : δ * 16 < (16 : ℝ) - t + 1)
    (blocked : (B + 1) * B * (k - 1) + a * (a + 1) * 16 < 2 * a * ((B + 1) * t)) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k :
      Set (Fin 16 → F))) δ ≤ B := by
  classical
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k t m B
  · simpa using hδ
  · intro s S hs hp
    by_contra! h
    let emb : Fin (B + 1) → Fin s := Fin.castLE (by omega)
    have hinj : Function.Injective emb := Fin.castLE_injective _
    have bound := RateHalfRichHeadCensus.incidence_bound
      (fun i => S (emb i)) (fun i => (hs (emb i)).ge)
      (fun i j hij => hp (hinj.ne hij)) a
    simp only [Nat.add_sub_cancel, Fintype.card_fin] at bound
    omega

/-- Seven words each agreeing on eleven sites would exceed the pairwise root bound. -/
theorem half_cap {F : Type*} [Field F] (D : Fin 16 ↪ F) (m : ℕ)
    (δ : ℝ) (hδ : δ < 6 / 16) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 8 :
      Set (Fin 16 → F))) δ ≤ 6 := by
  apply cap_of_incidence D 8 11 m 6 4 δ (by push_cast; linarith) (by decide)

set_option maxRecDepth 16000 in
/-- Exactly six words are possible in a worst five-error ball over every extension. -/
theorem half_five_errors {F : Type*} [Field F] (f : ZMod 17 →+* F) (m : ℕ) [NeZero m] :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code
      (domain.trans ⟨f, f.injective⟩) 8 : Set (Fin 16 → F))) (5 / 16) = 6 := by
  apply le_antisymm (half_cap _ m _ (by norm_num))
  let six (i : Fin 6) : Fin 8 → ZMod 17 := half (![0, 2, 3, 4, 6, 9] i)
  apply from_table (e := 5) (by decide) halfCenter six (by decide +kernel)
    (by decide +kernel) f (Fin m)

/-- At half rate the first failing count for budget six is six over every extension. -/
theorem half_good_iff {F : Type*} [Field F] (f : ZMod 17 →+* F) (m : ℕ) [NeZero m]
    (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code
      (domain.trans ⟨f, f.injective⟩) 8 : Set (Fin 16 → F))) δ ≤ 6 ↔ δ < 6 / 16 := by
  constructor
  · intro safe
    by_contra! crossed
    have h := (half_ten f (Fin m)).trans ((Lambda_mono crossed).trans safe)
    exact (by decide : ¬ (10 : ℕ∞) ≤ 6) h
  · exact half_cap _ m δ

/-- At most five degree-below-four words can each agree at eight of sixteen sites. -/
theorem quarter_cap {F : Type*} [Field F] (D : Fin 16 ↪ F) (m : ℕ)
    (δ : ℝ) (hδ : δ < 9 / 16) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 4 :
      Set (Fin 16 → F))) δ ≤ 5 := by
  apply cap_of_incidence D 4 8 m 5 2 δ (by push_cast; linarith) (by decide)

/-- At quarter rate the first failing count for budget six is nine over every extension. -/
theorem quarter_good_iff {F : Type*} [Field F] (f : ZMod 17 →+* F) (m : ℕ) [NeZero m]
    (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code
      (domain.trans ⟨f, f.injective⟩) 4 : Set (Fin 16 → F))) δ ≤ 6 ↔ δ < 9 / 16 := by
  constructor
  · intro safe
    by_contra! crossed
    have h := (quarter_eight f (Fin m)).trans ((Lambda_mono crossed).trans safe)
    exact (by decide : ¬ (8 : ℕ∞) ≤ 6) h
  · intro below
    exact (quarter_cap _ m δ below).trans (by decide)

#print axioms half_ten
#print axioms quarter_eight
#print axioms half_five_errors
#print axioms half_good_iff
#print axioms quarter_good_iff

end ProximityGap.SixteenPrimeSubfieldLists
