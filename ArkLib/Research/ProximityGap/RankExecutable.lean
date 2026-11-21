/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Research.ProximityGap.Frontier.ListSupportGaussian
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportGaussian
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.UniversalStaircaseCollapse
import ArkLib.Research.ProximityGap.Frontier.TwoParityMca
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.SmoothListExecutable
import ArkLib.Research.ProximityGap.Frontier.ListBudgetOne

/-! # Computing operational radii from a presented domain and integer budget

An input budget is the maximum permitted number of field labels or list members.
The executable functions use natural numbers and field arithmetic.
Their correctness statements also apply when the budget is obtained from a real tolerance.
-/
set_option autoImplicit false

namespace ProximityPrize.RankExecutable

open Code FullPrizeReview RankBoundary ProximityGap ProximityGap.GrandChallenges CoreDefinitions
open scoped NNReal ENNReal

/-- Return the least failing error count, or certify that every error count passes. -/
def scan (n : ℕ) (safe : Fin (n + 1) → Bool) : Boundary n :=
  Fin.find? fun e => !(safe e)

/-- The executable search returns the first count satisfying the mathematical failure test. -/
theorem scan_eq_firstFailure {n : ℕ} (safe : Fin (n + 1) → Bool) (fails : Fin (n + 1) → Prop)
    (hs : ∀ e, safe e = true ↔ ¬ fails e) : scan n safe = firstFailure n fails := by
  classical
  let T := Finset.univ.filter fails
  have hbad (e) : (!safe e) = true ↔ fails e := by
    simpa only [Bool.not_eq_true', Bool.not_eq_true, not_not] using not_congr (hs e)
  change Fin.find? (fun e => !(safe e)) = if h : T.Nonempty then some (T.min' h) else none
  rw [Fin.find?_eq_dite]
  by_cases ht : T.Nonempty
  · have hb : ∃ e, (!safe e) = true :=
      ⟨T.min' ht, (hbad _).mpr (Finset.mem_filter.mp (T.min'_mem ht)).2⟩
    rw [dite_eq_left ht, dite_eq_left hb, Option.some.injEq, Fin.find_eq_iff]
    refine ⟨(hbad _).mpr (Finset.mem_filter.mp (T.min'_mem ht)).2, ?_⟩
    intro j hj h
    exact (not_lt_of_ge (T.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hbad _).mp h⟩))) hj
  · have hb : ¬ ∃ e, (!safe e) = true := by
      rintro ⟨e, he⟩
      exact ht ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hbad _).mp he⟩⟩
    rw [dite_eq_right ht, dite_eq_right hb]


variable {F I : Type} [Field F] [DecidableEq F] [DecidableEq I]

/-- Compute a certified list cutoff from the integer parameters by unique decoding or interpolation
packing. A missing value leaves the support search to decide the answer. -/
def packingBoundary (n k q m B : ℕ) : Boundary n :=
  if h : 0 < k ∧ k ≤ n ∧ 0 < m ∧ B = 1 then
    some ⟨(n - k + 2) / 2, by omega⟩
  else
    let limit := (B + 1) * (k + 1)
    let count := BoundedChoose.capped n k limit
    if h : 0 < k ∧ k ≤ n ∧ 0 < m ∧ B < q ∧ count < limit then
      some ⟨if count ≤ B then n - k + 1 else n - k, by split <;> omega⟩
    else none

omit [DecidableEq F] [DecidableEq I] in
/-- A returned packing cutoff is the rank answer on every injective domain of the supplied size. -/
theorem packingBoundary_correct [Fintype I] [Nonempty I] [Fintype F]
    (D : I ↪ F) (ε : NNReal) (k m : ℕ) {e : Fin (Fintype.card I + 1)}
    (result : packingBoundary (Fintype.card I) k (Fintype.card F) m (RankReview.budget F ε) =
      some e) :
    some e = RankReview.listAnswer D ε k m := by
  classical
  unfold packingBoundary at result
  split at result
  · rename_i h
    obtain ⟨hk, hkn, hm, one⟩ := h
    cases result
    apply correctBoundary_unique Fintype.card_pos _ (RankReview.listAnswer_correct D ε k m hkn)
    intro δ _
    refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) (δ : ℝ) ε).trans ?_
    change (Code.Lambda _ _ ≤ (RankReview.budget F ε : ℕ∞)) ↔ _
    dsimp only
    rw [one, Nat.cast_one]
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    exact ListBudgetOne.rs_safe_iff D k m hk hkn hm (δ : ℝ)
  · dsimp only at result
    split at result
    · rename_i fast
      obtain ⟨hkp, hk, hm, hq, hcap⟩ := fast
      rw [BoundedChoose.capped_eq, min_lt_iff] at hcap
      have hlt := hcap.resolve_right (lt_irrefl _)
      have packed := (Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mpr hlt
      have hc : BoundedChoose.capped (Fintype.card I) k
          ((RankReview.budget F ε + 1) * (k + 1)) = (Fintype.card I).choose k := by
        rw [BoundedChoose.capped_eq, min_eq_left hlt.le]
      cases result
      apply correctBoundary_unique Fintype.card_pos _ (RankReview.listAnswer_correct D ε k m hk)
      intro δ _
      refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
        (ListInterpolationBoundary.words D k m) (δ : ℝ) ε).trans ?_
      have spec := ListInterpolationBoundary.good_iff D hkp hk hm
        (Nat.le_of_lt_succ packed) hq (δ : ℝ)
      refine spec.trans ?_
      dsimp only
      rw [hc, ← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    · cases result

private def listSupportBoundary (points : List I) (D : I ↪ F) (n k q m B : ℕ) : Boundary n :=
  scan n fun e =>
    if 0 < m ∧ (B + 1).choose 2 ≤ q then
      ListSupportRank.gaussianPairSafe points D k B (n - e.val)
    else ListSupportRank.gaussianSafe points D k q m B (n - e.val)

/-- Compute the list boundary from a coordinate list, its evaluation map, and an integer budget. -/
def listBoundary (points : List I) (D : I ↪ F) (n k q m B : ℕ) : Boundary n :=
  match packingBoundary n k q m B with
  | some e => some e
  | none => listSupportBoundary points D n k q m B

/-- Executing the list search produces the universal operational answer. -/
theorem listBoundary_eq [Fintype I] [Fintype F] (points : List I) (hp : ∀ i, i ∈ points)
    (D : I ↪ F) (ε : NNReal) (k m : ℕ) (hn : 0 < Fintype.card I) (hk : k ≤ Fintype.card I) :
    listBoundary points D (Fintype.card I) k (Fintype.card F) m (RankReview.budget F ε) =
      RankReview.listAnswer D ε k m := by
  let : Nonempty I := Fintype.card_pos_iff.mp hn
  unfold listBoundary
  split
  · rename_i e he
    exact packingBoundary_correct D ε k m he
  · unfold listSupportBoundary
    apply scan_eq_firstFailure
    intro e
    let B := RankReview.budget F ε
    have hs : (if 0 < m ∧ (B + 1).choose 2 ≤ Fintype.card F then
          ListSupportRank.gaussianPairSafe points D k B (Fintype.card I - e.val)
        else ListSupportRank.gaussianSafe points D k (Fintype.card F) m B
          (Fintype.card I - e.val)) = true ↔
          Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
            (1 - ((Fintype.card I - e.val : ℕ) : ℝ) / Fintype.card I) ≤ (B : ℕ∞) := by
      split_ifs with h
      · exact ListSupportRank.gaussianPairSafe_iff points hp D k m B _ hn hk h.1 h.2
      · exact ListSupportRank.gaussianSafe_iff points hp D k m B _ hn hk
    rw [hs, ListSupportRank.rs_vandermonde_safe_iff D k m _ _ hn hk]
    unfold RankReview.listFails
    push Not
    rfl

/-- Compute the smooth-domain list cutoff. Coordinates are supplied on demand, so all
parameter-only branches can run even when materializing the domain would exhaust memory. -/
def smoothListBoundary (points : Unit → List I) (D : I ↪ F) (n k q m B : ℕ) : Boundary n :=
  match packingBoundary n k q m B with
  | some e => some e
  | none => match productBoundary n k m B with
    | some e => some e
    | none => listSupportBoundary (points ()) D n k q m B

/-- The smooth-domain shortcuts and fallback return the same canonical first failure. -/
theorem smoothListBoundary_eq [Fintype I] [Nonempty I] [Fintype F]
    (points : Unit → List I) (hi : ∀ i, i ∈ points ()) (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) (k m : ℕ) (hk : k ≤ Fintype.card I) :
    smoothListBoundary points D (Fintype.card I) k (Fintype.card F) m (RankReview.budget F ε) =
      RankReview.listAnswer D ε k m := by
  unfold smoothListBoundary
  split
  · exact packingBoundary_correct D ε k m ‹_›
  · rename_i hp
    split
    · exact productBoundary_correct D ε k m ‹_›
    · simpa only [listBoundary, hp] using listBoundary_eq (points ()) hi D ε k m Fintype.card_pos hk

/-- Constant-time boundary when two parity checks determine the entire MCA curve. -/
def twoCheckBoundary (n B : ℕ) : Boundary n :=
  if B = 0 then some 0 else if h : n ≤ B then none else some ⟨1, by omega⟩

private theorem twoCheckBoundary_eq_scan {n k : ℕ} [Finite I] [Nonempty I] [Finite F]
    [SampleableType F] (E : Fin n ≃ I) (labels : List F) (hl : ∀ g, g ∈ labels)
    (D : I ↪ F) (B : ℕ) (hn : n = k + 2) :
    twoCheckBoundary n B =
      scan n (fun e => SimultaneousSupportGaussian.anchoredSafe E labels D k B (n - e.val)) := by
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite F
  let safe (e : Fin (n + 1)) := SimultaneousSupportGaussian.anchoredSafe E labels D k B (n - e.val)
  have card : Fintype.card I = n := (Fintype.card_congr E).symm.trans (Fintype.card_fin n)
  have npos : (0 : ℝ≥0) < n := by exact_mod_cast (show 0 < n by omega)
  have qnz : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have test (e : Fin (n + 1)) : (!safe e) = true ↔ B < (if e.val = 0 then 1 else n) := by
    have prob := SimultaneousSupportGaussian.anchoredSafe_iff E labels hl D k B e.val (by omega)
    have grid := epsMCA_eq_mcaError (ReedSolomon.code D k) ((e.val : ℝ≥0)/n)
    rw [TwoParityMca.profile D (card.trans hn), card] at grid
    have ge : 1/(n : ℝ≥0) ≤ (e.val : ℝ≥0)/n ↔ e.val ≠ 0 := by
      rw [div_le_div_iff_of_pos_right npos]
      exact_mod_cast (show 1 ≤ e.val ↔ e.val ≠ 0 by omega)
    simp only [ge] at grid
    have saf : safe e = true ↔ (if e.val = 0 then 1 else n) ≤ B := by
      rw [show safe e = true ↔ _ from prob]
      rw [show ((e.val : ℝ) / n) = (((e.val : ℝ≥0)/n : ℝ≥0) : ℝ) by norm_cast,
        ← grid, ENNReal.div_le_iff qnz (ENNReal.natCast_ne_top _),
        ENNReal.div_mul_cancel qnz (ENNReal.natCast_ne_top _)]
      by_cases h : e.val=0 <;> simp [h]
    simpa only [Bool.not_eq_true', Bool.not_eq_true, not_le] using not_congr saf
  change twoCheckBoundary n B = Fin.find? (fun e => !safe e)
  unfold twoCheckBoundary
  split_ifs with hz hb
  · symm
    change (0 : Fin (n + 1)) ∈ Fin.find? _
    exact Fin.mem_find?_iff.mpr ⟨(test 0).mpr (by simp [hz]), by simp⟩
  · symm
    have never : ¬ ∃ e, (!safe e) = true := by
      rintro ⟨e, he⟩
      have h := (test e).mp he
      split_ifs at h <;> omega
    simp only [Fin.find?_eq_dite, never, dite_false]
  · let one : Fin (n + 1) := ⟨1, by omega⟩
    symm
    change one ∈ Fin.find? _
    apply Fin.mem_find?_iff.mpr
    refine ⟨(test one).mpr (by simpa [one] using Nat.lt_of_not_ge hb), ?_⟩
    intro j hj hjbad
    have zero : j.val = 0 := by change j.val < 1 at hj; omega
    have h := (test j).mp hjbad
    simp [zero] at h
    omega

/-- The circuit count alone can certify every MCA radius using just the length,
dimension, and scalar budget. -/
def circuitsCovered (n k B : ℕ) : Bool :=
  BoundedChoose.capped n (k + 1) (B + 1) ≤ B

omit [DecidableEq F] [DecidableEq I] in
/-- A successful circuit count certificate makes the entire MCA grid safe on every domain. -/
theorem circuitsCovered_correct [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (D : I ↪ F) (ε : ℝ≥0) (k : ℕ)
    (covered : circuitsCovered (Fintype.card I) k (RankReview.budget F ε) = true) :
    none = RankReview.mcaAnswer D ε k := by
  classical
  apply correctBoundary_unique Fintype.card_pos _ (RankReview.mcaAnswer_correct D ε k)
  intro δ hδ
  simp only [iff_true]
  rw [← epsMCA_eq_mcaError, SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
  apply ((epsMCA_mono _ hδ).trans (epsMCA_one_le_choose_div D k)).trans
  apply ENNReal.div_le_div_right
  have hc : (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε := by
    simpa [circuitsCovered, BoundedChoose.capped_eq, min_le_iff] using covered
  exact_mod_cast hc

/-- Check whether the staircase upper bound covers the predecessor and the
spike construction fits at the next error count. -/
def spikeBoundary (n k B : ℕ) : Boundary n :=
  if h : k + 3 * (B - 1) ≤ n ∧ k + (B + 1) ≤ n then
    some ⟨B, by omega⟩
  else none

omit [DecidableEq I] [DecidableEq F] in
/-- In the spike window the first failing count is the budget itself on every
injective domain, including at an arbitrary real tolerance. -/
theorem spikeBoundary_correct [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) {e : Fin (Fintype.card I + 1)}
    (res : spikeBoundary (Fintype.card I) k (RankReview.budget F ε) = some e) :
    some e = RankReview.mcaAnswer D ε k := by
  classical
  let B := RankReview.budget F ε
  change spikeBoundary (Fintype.card I) k B = some e at res
  unfold spikeBoundary at res
  split at res
  · rename_i h
    obtain ⟨pre, room⟩ := h
    cases res
    symm
    apply correctBoundary_unique Fintype.card_pos (RankReview.mcaAnswer_correct D ε k)
    intro δ _
    change mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤ _ ↔
      δ < (B : ℝ≥0) / Fintype.card I
    rw [← epsMCA_eq_mcaError, SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
    have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
    constructor
    · intro safe
      by_contra! crossed
      have fit : B+1 ≤ Fintype.card I := by omega
      obtain ⟨pos⟩ : Nonempty (Fin (B+1) ↪ I) :=
        Function.Embedding.nonempty_of_card_le (by simpa using fit)
      have spike := SpikeFloor.epsMCA_ge_j_div_card (ReedSolomon.code D k)
        (MCAStaircaseRS.rs_noWeightLE D room) (δ := δ) (by simpa using (div_le_iff₀ hn).mp crossed)
        (by omega) fit pos (pos.trans D) (b := (1 : F)) one_ne_zero
      have le := spike.trans safe
      change ((B+1 : ℕ) : ℝ≥0∞) / Fintype.card F ≤ (B : ℝ≥0∞) / Fintype.card F at le
      rw [ENNReal.div_le_iff (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _),
        ENNReal.div_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)] at le
      exact (Nat.not_succ_le_self B) (by exact_mod_cast le)
    · exact fun good => SpikeFloor.epsMCA_le_j_div_card (ReedSolomon.code D k)
        (MCAStaircaseRS.rs_noWeightLE D pre) ((lt_div_iff₀ hn).mp good)
  · contradiction

/-- Compute the MCA boundary, requesting field labels only when a simultaneous
support search is necessary. -/
def mcaBoundaryWith {n : ℕ} (E : Fin n ≃ I) (labels : Unit → List F) (D : I ↪ F)
    (k B : ℕ) : Boundary n :=
  match spikeBoundary n k B with
  | some e => some e
  | none =>
    if circuitsCovered n k B then none else
      if n = k + 2 then twoCheckBoundary n B else
        let fieldLabels := labels ()
        scan n fun e => SimultaneousSupportGaussian.anchoredSafe E fieldLabels D k B (n - e.val)

/-- Compute the MCA boundary with a supplied list of field elements. -/
def mcaBoundary {n : ℕ} (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k B : ℕ) : Boundary n :=
  mcaBoundaryWith E (fun _ => labels) D k B

/-- Executing the MCA search produces the universal operational answer. -/
theorem mcaBoundary_eq [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hlabels : ∀ g, g ∈ labels)
    (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) :
    mcaBoundary E labels D k (RankReview.budget F ε) = RankReview.mcaAnswer D ε k := by
  classical
  unfold mcaBoundary mcaBoundaryWith
  split
  next e result => exact spikeBoundary_correct D ε k result
  next =>
    by_cases covered : circuitsCovered (Fintype.card I) k (RankReview.budget F ε) = true
    · rw [ite_eq_left covered]
      exact circuitsCovered_correct D ε k covered
    · rw [ite_eq_right covered]
      rw [ite_eq_right_iff.mpr (twoCheckBoundary_eq_scan E labels hlabels D _)]
      apply scan_eq_firstFailure
      intro e
      rw [SimultaneousSupportGaussian.anchoredSafe_iff E labels hlabels D k _ e.val
        Fintype.card_pos]
      let δ := gridPt (ι := I) e.val
      change (mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤ _) ↔ _
      rw [← epsMCA_eq_mcaError, ← not_lt, SimultaneousSupportRank.budget_failure_iff]
      unfold RankReview.mcaFails
      have hs (S : Finset I) : ((1 - δ) * Fintype.card I ≤ (S.card : ℝ≥0)) ↔
          Fintype.card I - e.val ≤ S.card := by
        rw [← relDist_floor_bound_iff_complement_bound, gridPt_mul_card, Nat.floor_natCast]
      simp_rw [ge_iff_le, hs]

/-- Delaying the field enumeration preserves the answer of the public rank evaluator. -/
theorem mcaBoundaryWith_eq [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : Unit → List F) (hl : ∀ g, g ∈ labels ())
    (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) :
    mcaBoundaryWith E labels D k (RankReview.budget F ε) = RankReview.mcaAnswer D ε k := by
  have h : (fun _ : Unit => labels ()) = labels := by funext u; cases u; rfl
  simpa only [mcaBoundary, h] using mcaBoundary_eq E (labels ()) hl D ε k

/-- Both executable boundary functions classify every real radius in the prize contract. -/
theorem correctForEveryDomain [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hf : ∀ g, g ∈ labels)
    (points : List I) (hi : ∀ i, i ∈ points) (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) :
    correctForDomain D ε
      (fun k => mcaBoundary E labels D k (RankReview.budget F ε))
      (fun k m => listBoundary points D (Fintype.card I) k (Fintype.card F) m
        (RankReview.budget F ε)) := by
  intro k hk
  have hk' : k ≤ Fintype.card I := by
    rcases hk with h | h | h | h <;> omega
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain D ε k hk
  constructor
  · simpa only [mcaBoundary_eq E labels hf D ε k] using hM
  · intro m hm
    simpa only [listBoundary_eq points hi D ε k m Fintype.card_pos hk'] using hL m hm

/-- Delaying the coordinates allows the parameter-only list certificates to run on large domains. -/
theorem correctForEverySmoothDomain [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : Unit → List F) (hf : ∀ g, g ∈ labels ())
    (points : Unit → List I) (hi : ∀ i, i ∈ points ()) (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) :
    correctForDomain D ε
      (fun k => mcaBoundaryWith E labels D k (RankReview.budget F ε))
      (fun k m => smoothListBoundary points D (Fintype.card I) k (Fintype.card F) m
        (RankReview.budget F ε)) := by
  intro k hk
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain D ε k hk
  constructor
  · simpa only [mcaBoundaryWith_eq E labels hf D ε k] using hM
  · intro m hm
    have hkn : k ≤ Fintype.card I := by rcases hk with h | h | h | h <;> omega
    simpa only [smoothListBoundary_eq points hi D ε k m hkn] using hL m hm

/-- At the prize example tolerance, the evaluator only needs ordinary integer division. -/
theorem prizeBudget (F : Type) [Fintype F] :
    RankReview.budget F (prizeThreshold : ℝ≥0) = Fintype.card F / 2 ^ 128 := by
  unfold RankReview.budget
  have h : (prizeThreshold : ℝ≥0) = 1 / (2 ^ 128 : ℕ) := by
    norm_num [prizeThreshold]
  rw [h, one_div, mul_comm, ← div_eq_mul_inv, Nat.floor_div_eq_div]

/-- The executable evaluators at 128-bit tolerance take the field order directly. -/
theorem correctAtPrizeTolerance [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hf : ∀ g, g ∈ labels)
    (points : List I) (hi : ∀ i, i ∈ points) (D : I ↪ F) [ReedSolomon.Smooth D] :
    correctForDomain D (prizeThreshold : ℝ≥0)
      (fun k => mcaBoundary E labels D k (Fintype.card F / 2 ^ 128))
      (fun k m => listBoundary points D (Fintype.card I) k (Fintype.card F) m
        (Fintype.card F / 2 ^ 128)) := by
  simpa only [prizeBudget] using correctForEveryDomain E labels hf points hi D
    (prizeThreshold : ℝ≥0)

/-- The smooth-domain evaluator with on-demand coordinates at the sponsor tolerance. -/
theorem smoothCorrectAtPrizeTolerance [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : Unit → List F) (hf : ∀ g, g ∈ labels ())
    (points : Unit → List I) (hi : ∀ i, i ∈ points ()) (D : I ↪ F) [ReedSolomon.Smooth D] :
    correctForDomain D (prizeThreshold : ℝ≥0)
      (fun k => mcaBoundaryWith E labels D k (Fintype.card F / 2 ^ 128))
      (fun k m => smoothListBoundary points D (Fintype.card I) k (Fintype.card F) m
        (Fintype.card F / 2 ^ 128)) := by
  simpa only [prizeBudget] using correctForEverySmoothDomain E labels hf points hi D
    (prizeThreshold : ℝ≥0)

#print axioms smoothCorrectAtPrizeTolerance
#print axioms correctAtPrizeTolerance
#print axioms listBoundary_eq
#print axioms mcaBoundary_eq
#print axioms correctForEveryDomain

end ProximityPrize.RankExecutable
