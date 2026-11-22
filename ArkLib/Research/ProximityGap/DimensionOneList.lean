/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Data.CodingTheory.ProximityGap.BGKS20SeparationRegime
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius

/-! # Exact list sizes and thresholds for every dimension-one Reed–Solomon code

A constant interleaved word with at least `t` agreements uses sites disjoint
from those of every other constant. Conversely, place each of the selected
symbols on a disjoint block of `t` sites to realize the packing bound.
-/

namespace ProximityPrize.DimensionOneList

open Code Finset FullPrizeReview ProximityGap ProximityGap.GrandChallenges Polynomial
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

/-- The number of different constant symbols which fit in the available sites.
At zero required agreements every symbol belongs to the list. -/
def listCount (n q m t : ℕ) : ℕ := if t = 0 then q ^ m else min (q ^ m) (n / t)

/-- Compare the size of the constant alphabet to the budget without materializing
a field-order power whose size can grow linearly with the interleaving width. -/
private def powerFits (q m B : ℕ) : Decidable (q ^ m ≤ B) :=
  if hq : 1 < q then
    if hz : B = 0 then
      isFalse (by have := Nat.pow_pos (Nat.zero_lt_one.trans hq) (n := m); omega)
    else decidable_of_iff (m ≤ Nat.log q B) (Nat.le_log_iff_pow_le hq hz)
  else inferInstance

/-- The first failing error count for an integer list budget. -/
def boundary (n q m B : ℕ) : Boundary n :=
  letI := powerFits q m B
  if q ^ m ≤ B then none else some ⟨n - n / (B + 1), Nat.lt_succ_of_le (Nat.sub_le ..)⟩

/-- The dimension-one RS code interleaved at width m. -/
abbrev words (D : I ↪ F) (m : ℕ) : Set (I → Fin m → F) :=
  interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 1 : Set (I → F))

private theorem packing_lower (D : I ↪ F) (m t L : ℕ) (alphabet : L ≤ Fintype.card F ^ m)
    (space : L * t ≤ Fintype.card I) :
    (L : ℕ∞) ≤ Lambda (words D m) (1 - (t : ℝ) / Fintype.card I) := by
  classical
  obtain ⟨symbol⟩ : Nonempty (Fin L ↪ (Fin m → F)) :=
    Function.Embedding.nonempty_iff_card_le.mpr (by simpa using alphabet)
  obtain ⟨site⟩ : Nonempty ((Fin L × Fin t) ↪ I) :=
    Function.Embedding.nonempty_iff_card_le.mpr (by simpa using space)
  let y := Function.extend site (fun p => symbol p.1) (fun _ => 0)
  let encode (b : Fin L) : I → Fin m → F := fun _ => symbol b
  have mem (b : Fin L) : encode b ∈ words D m := by
    intro j
    exact ReedSolomon.mem_code_iff_eval.mpr ⟨C (symbol b j),
      degree_C_le.trans_lt (by norm_num), fun _ => eval_C⟩
  have hits (b : Fin L) : t ≤ agree (encode b) y := by
    let block := (univ : Finset (Fin t)).image (fun j => site (b,j))
    have card : block.card = t := by
      rw [show block.card = _ from card_image_of_injective _
        (fun i j h => congrArg Prod.snd (site.injective h))]
      simp
    rw [← card]
    apply card_le_card
    intro x hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    exact (site.injective.extend_apply (fun p => symbol p.1) (fun _ => 0) (b,j)).symm
  have hinj : Function.Injective encode := fun _ _ h =>
    symbol.injective (congrFun h (Classical.arbitrary I))
  have h := encard_setOf_le_agree_encode_le_Lambda (words D m) y t
    (S := Set.univ) hinj.injOn (fun b _ => mem b)
  simpa [hits, Set.encard_univ] using h

private theorem total_bound (D : I ↪ F) (m : ℕ) (r : ℝ) :
    Lambda (words D m) r ≤ (Fintype.card F ^ m : ℕ) := by
  classical
  apply Lambda_le_iff_forall_ncard_le.mpr
  intro y
  let const (v : Fin m → F) : I → Fin m → F := fun _ => v
  have inj : Function.Injective const := fun _ _ h => congrFun h (Classical.arbitrary I)
  have sub : closeCodewordsRel (words D m) y r ⊆ Set.range const := by
    intro w hw
    let i₀ := Classical.arbitrary I
    refine ⟨w i₀, ?_⟩
    funext i j
    exact CodingTheory.BGKS20SeparationRegime.rs_code_one_const D
      ((mem_closeCodewordsRel_iff.mp hw).1 j) i₀ i
  refine ⟨Set.toFinite _, (Set.ncard_le_ncard sub (Set.toFinite _)).trans_eq ?_⟩
  rw [Set.ncard_range_of_injective inj, Nat.card_eq_fintype_card]
  simp

/-- Exact worst closed-ball list size when the required agreement count is `t`. -/
theorem lambda_agreement (D : I ↪ F) (m t : ℕ) :
    Lambda (words D m) (1 - (t : ℝ) / Fintype.card I) =
      (listCount (Fintype.card I) (Fintype.card F) m t : ℕ∞) := by
  classical
  have cap := total_bound D m (1 - (t : ℝ) / Fintype.card I)
  by_cases z : t = 0
  · subst t
    simpa [listCount] using le_antisymm cap
      (packing_lower D m 0 (Fintype.card F ^ m) le_rfl (by simp))
  have pos : 0 < t := Nat.pos_of_ne_zero z
  rw [listCount, ite_eq_right z]
  apply le_antisymm
  · have packed := AgreementSubsetListPacking.interleaved_lambda_le_choose_div D 1 t m
      (1 - (t : ℝ) / Fintype.card I) pos (by
        have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hn]; linarith)
    rcases le_total (Fintype.card F ^ m) (Fintype.card I / t) with h | h
    · simpa only [min_eq_left h] using cap
    · simpa only [min_eq_right h, Nat.choose_one_right, words] using packed
  · exact packing_lower D m t _ (min_le_left _ _)
      ((Nat.le_div_iff_mul_le pos).mp (min_le_right _ _))

/-- At any nonnegative real radius the error count is rounded down to the Hamming grid. -/
theorem lambda_radius (D : I ↪ F) (m : ℕ) (δ : ℝ≥0) :
    Lambda (words D m) (δ : ℝ) = (listCount (Fintype.card I) (Fintype.card F) m
      (Fintype.card I - ⌊δ * Fintype.card I⌋₊) : ℕ∞) := by
  let n := Fintype.card I
  let e := ⌊δ * (n : ℝ≥0)⌋₊
  have hn : 0 < n := Fintype.card_pos
  have hp : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases le : e ≤ n
  · have same : Lambda (words D m) (δ : ℝ) =
        Lambda (words D m) (((e : ℝ≥0) / n : ℝ≥0) : ℝ) := by
      apply lambda_eq_of_floor_eq
      change e = ⌊((e : ℝ≥0) / n) * n⌋₊
      rw [div_mul_cancel₀ _ hp, Nat.floor_natCast]
    have grid : (((e : ℝ≥0) / n : ℝ≥0) : ℝ) = 1 - ((n - e : ℕ) : ℝ) / n := by
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_sub le]
      field_simp
      ring
    rw [same, grid]
    exact lambda_agreement D m (n - e)
  · have full : (1 : ℝ) ≤ δ := by
      have h := (Nat.le_floor_iff (by positivity : (0 : ℝ≥0) ≤ δ * n)).mp (show n ≤ e by omega)
      have hδ : 1 ≤ δ := (le_mul_iff_one_le_left (by positivity : (0 : ℝ≥0) < n)).mp h
      exact_mod_cast hδ
    change _ = (listCount n _ _ (n - e) : ℕ∞)
    rw [Nat.sub_eq_zero_of_le (by omega : n ≤ e)]
    simp only [listCount, ite_true]
    apply le_antisymm (total_bound D m _)
    have low := (lambda_agreement D m 0).ge
    exact (by simpa [listCount] using low : (Fintype.card F ^ m : ℕ) ≤ Lambda (words D m) 1).trans
      (Lambda_mono full)

private theorem count_le_iff {n q m B e : ℕ} (he : e ≤ n) :
    listCount n q m (n - e) ≤ B ↔ q ^ m ≤ B ∨ e < n - n / (B + 1) := by
  by_cases h : n - e = 0
  · simp only [listCount, h, ite_true]
    have : ¬ e < n - n / (B + 1) := fun he' => by have := Nat.sub_le n (n / (B + 1)); omega
    simp [this]
  have ht : 0 < n - e := Nat.pos_of_ne_zero h
  have transposed : n / (n - e) ≤ B ↔ n / (B + 1) < n - e := by
    rw [show n / (n - e) ≤ B ↔ n / (n - e) < B + 1 by omega,
      Nat.div_lt_iff_lt_mul ht, Nat.div_lt_iff_lt_mul (Nat.succ_pos B), Nat.mul_comm]
  rw [listCount, ite_eq_right h, min_le_iff, transposed]
  omega

/-- The exact operational answer in every field and domain at any nonnegative tolerance.
The width may be zero. The result distinguishes failure at zero from an all-safe grid. -/
theorem listAnswer_eq (D : I ↪ F) (ε : ℝ≥0) (m : ℕ) :
    RankReview.listAnswer D ε 1 m =
      boundary (Fintype.card I) (Fintype.card F) m (RankReview.budget F ε) := by
  classical
  apply FullPrizeReview.correctBoundary_unique Fintype.card_pos
    (RankReview.listAnswer_correct D ε 1 m Fintype.card_pos)
  intro δ hδ
  let n := Fintype.card I
  let B := RankReview.budget F ε
  let e := ⌊δ * (n : ℝ≥0)⌋₊
  have he : e ≤ n := Nat.le_of_lt_succ (RankBoundary.cell n δ hδ).isLt
  have hn : (0 : ℝ≥0) < n := by exact_mod_cast Fintype.card_pos (α := I)
  change ((Lambda (words D m) (δ : ℝ) : ℝ≥0∞) ≤ _ ↔ _)
  rw [ListSupportRank.lambda_le_floor_iff (K := F), lambda_radius]
  change ((listCount n (Fintype.card F) m (n - e) : ℕ∞) ≤ (B : ℕ∞) ↔ _)
  rw [Nat.cast_le, count_le_iff he]
  unfold boundary
  by_cases cap : Fintype.card F ^ m ≤ B
  · simp [cap, B]
  · have grid : e < n - n / (B + 1) ↔ δ < ((n - n / (B + 1) : ℕ) : ℝ≥0) / n := by
      rw [lt_div_iff₀ hn]
      exact Nat.floor_lt (by positivity)
    simpa only [show ¬ Fintype.card F ^ m ≤ RankReview.budget F ε from cap, ite_false,
      false_or, cap] using grid

end ProximityPrize.DimensionOneList
