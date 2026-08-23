/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorSurjectivity
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorInjectivity
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorFiber

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **Per-fiber disagreement is column-visible** (Brick-Y packaging): the per-fiber
disagreement set of `f, g` injects into the disagreeing columns of their pre-tensor stacks. -/
lemma pair_fiberwiseDistance_le_interleaved_hammingDist
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f g ≤
    hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f))
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) := by
  classical
  obtain ⟨dv, hdvlt⟩ := destIdx
  simp only at h_destIdx
  subst h_destIdx
  have hle' : i.val + steps ≤ ℓ := by simpa using h_destIdx_le
  have h𝓡 := Nat.pos_of_neZero 𝓡
  unfold pair_fiberwiseDistance
  rw [hammingDist]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  rw [mem_fiberwiseDisagreementSetPerFiber] at hy
  intro hcols
  apply absurd hy
  push_neg
  intro idx
  -- all interleaved columns equal at y → all binary rows equal at y
  have hrows : ∀ j : Fin (2 ^ steps),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by omega⟩) (steps := steps)
        (destIdx := ⟨i.val + steps, hdvlt⟩)
        (h_destIdx := rfl) (h_destIdx_le := h_destIdx_le)
        (f := f) (r_challenges := bitsOfIndex (L := L) j) y =
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by omega⟩) (steps := steps)
        (destIdx := ⟨i.val + steps, hdvlt⟩)
        (h_destIdx := rfl) (h_destIdx_le := h_destIdx_le)
        (f := g) (r_challenges := bitsOfIndex (L := L) j) y := by
    intro j
    have := congrFun hcols j
    simpa [Code.interleaveWordStack, preTensorCombine_WordStack] using this
  -- convert to steps level and apply Brick Y
  have hfib := fiber_agree_of_binary_folds_agree 𝔽q β steps i.val (by omega)
    (by omega) (by omega) (by omega)
    f g y
    (by
      intro j
      exact hrows j)
    idx
  -- fiberEvaluations applies f at the lifted fiber point; the lift is `⟨y.val, _⟩ ≡ y` by eta
  exact hfib


set_option maxHeartbeats 8000000 in
/-- **Lemma 4.22, far direction**: joint proximity of the pre-tensor stack bounds the
fiberwise distance. Combines the Brick-X lift (every interleaved codeword is a pre-tensor
stack of a codeword) with the Brick-Y column-visibility bound. -/
lemma fiberwiseDistance_le_of_jointProximityNat
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (e : ℕ)
    (h : jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) e) :
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f_i ≤ e := by
  classical
  set C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)) with hC
  have hne : Nonempty (interleavedCodeSet (κ := Fin (2 ^ steps)) (C := C_dest)) := by
    refine ⟨⟨(0 : Matrix (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (Fin (2 ^ steps)) L), ?_⟩⟩
    intro k
    exact (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx).zero_mem
  obtain ⟨V, hV_mem, hV_eq⟩ := @exists_closest_codeword_of_Nonempty_Code
    (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) _ (Fin (2 ^ steps) → L) _
    (interleavedCodeSet (κ := Fin (2 ^ steps)) (C := C_dest)) hne
    (Code.interleaveWordStack
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i))
  obtain ⟨g, hg_mem, hg_eq⟩ := exists_codeword_preTensorCombine_eq_of_rows_mem 𝔽q β
    i steps h_destIdx h_destIdx_le (fun k y => V y k) (fun k => hV_mem k)
  have hVpack : Code.interleaveWordStack
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) = V := by
    rw [hg_eq]
    rfl
  -- the Nat-level chain
  have h1 : fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f_i ≤
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        (by simpa using h_destIdx) h_destIdx_le f_i g := by
    unfold fiberwiseDistance
    exact Nat.sInf_le ⟨⟨g, by simpa [C_dest] using hg_mem⟩, Set.mem_univ _, rfl⟩
  have h2 := pair_fiberwiseDistance_le_interleaved_hammingDist 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i g
  rw [hVpack] at h2
  -- ℕ∞ extraction of the closest distance
  have h3 : (hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)) V : ℕ∞) ≤
      (e : ℕ∞) := by
    have hh := h
    unfold jointProximityNat at hh
    calc (hammingDist _ V : ℕ∞)
        = Δ₀((Code.interleaveWordStack
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)), V) := by
          rfl
      _ = Δ₀((Code.interleaveWordStack
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)),
            (interleavedCodeSet (C := C_dest))) := hV_eq
      _ ≤ (e : ℕ∞) := hh
  have h3' : hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)) V ≤ e := by
    exact_mod_cast h3
  omega

/- A destination-radius bound on the fiberwise distance is enough to recover both conjuncts
of `fiberwiseClose`. The source UDR conjunct follows by choosing a closest source codeword
and applying the fiberwise-to-Hamming bound. -/
set_option maxHeartbeats 1200000 in
/-- Source Hamming distance is bounded by the number of bad quotient fibers times the fiber
size. Local port of the (currently commented-out) `Code.lean` lemma onto the per-fiber
disagreement surface. -/
lemma hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    Δ₀(f, g) ≤
      (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f g) * 2 ^ steps := by
  classical
  -- Hoist destIdx-free bound proofs so the `subst` below is not self-referential.
  have hle : i.val + steps ≤ ℓ := by
    rw [← h_destIdx]
    exact h_destIdx_le
  have hi_lt_r : i.val < r := by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.isLt
  have hlt_r : i.val + steps < r := by
    have hR := h_ℓ_add_R_rate
    omega
  have hdest : destIdx = (⟨i.val + steps, hlt_r⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst hdest
  have h_i_add_steps : i.val + steps ≤ ℓ := hle
  let d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r))
    (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r))
    (steps := steps) h_destIdx h_destIdx_le f g
  have hNat : hammingDist f g ≤ d_fw * 2 ^ steps := by
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    set Y_bad := fiberwiseDisagreementSetPerFiber 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r))
      (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r))
      (steps := steps) h_destIdx h_destIdx_le f g
    let fiberSet : (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i.val + steps, hlt_r⟩ : Fin r) →
        Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i.val, hi_lt_r⟩ : Fin r)) := fun y =>
      (Set.image
        (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
          (h_i_add_steps := by
            simp only
            exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
          (y := y))
        (Set.univ : Set (Fin (2 ^ steps)))).toFinset
    have h_subset : ΔH ⊆ Finset.biUnion Y_bad (t := fiberSet) := by
      intro x hx
      simp only [ΔH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      let y_of_x := AdditiveNTT.iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr
      refine ⟨y_of_x, ?_, ?_⟩
      · rw [mem_fiberwiseDisagreementSetPerFiber]
        let idx := pointToIterateQuotientIndex 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (ℓ + 1)))
          (steps := steps) h_i_add_steps x
        refine ⟨idx, ?_⟩
        have hres :=
          (is_fiber_iff_generates_quotient_point 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
            (x := x) (y := y_of_x)).mp rfl
        have hf :
            fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := (⟨i.val, hi_lt_r⟩ : Fin r))
              (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r)) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
              (f := f) (y := y_of_x) idx = f x := by
          rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
            (h_i_add_steps_le := h_i_add_steps) (h_i_add_steps_lt_r := hlt_r)
            (f := f) (y := y_of_x) (idx := idx)]
          simpa using congrArg f hres
        have hg :
            fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := (⟨i.val, hi_lt_r⟩ : Fin r))
              (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r)) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
              (f := g) (y := y_of_x) idx = g x := by
          rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
            (h_i_add_steps_le := h_i_add_steps) (h_i_add_steps_lt_r := hlt_r)
            (f := g) (y := y_of_x) (idx := idx)]
          simpa using congrArg g hres
        intro hfg
        exact hx (by simpa [hf, hg] using hfg)
      · set idx := pointToIterateQuotientIndex 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (ℓ + 1)))
          (steps := steps) h_i_add_steps x
        have hres :=
          (is_fiber_iff_generates_quotient_point 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
            (x := x) (y := y_of_x)).mp rfl
        have hmem :
            x ∈ Set.image
              (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                (h_i_add_steps := by
                  simp only
                  exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y_of_x))
              (Set.univ : Set (Fin (2 ^ steps))) := by
          exact ⟨idx, Set.mem_univ idx, hres⟩
        change x ∈ fiberSet y_of_x
        dsimp only [fiberSet]
        rw [Set.mem_toFinset]
        exact hmem
    refine (Finset.card_le_card h_subset).trans ?_
    rw [Finset.card_biUnion]
    · have h_each : ∀ y ∈ Y_bad, (fiberSet y).card = 2 ^ steps := by
        intro y hy
        have h := card_qMap_total_fiber 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps y
        have h_card :
            (fiberSet y).card =
              Fintype.card
                (Set.image
                  (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                    (h_i_add_steps := by
                      simp only
                      exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                    (y := y))
                  (Set.univ : Set (Fin (2 ^ steps)))) := by
          dsimp only [fiberSet]
          exact Set.toFinset_card
            (s := Set.image
              (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                (h_i_add_steps := by
                  simp only
                  exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y))
              (Set.univ : Set (Fin (2 ^ steps))))
        exact h_card.trans h
      rw [Finset.sum_congr rfl h_each]
      simp [Y_bad, d_fw, pair_fiberwiseDistance]
    · intro y₁ hy₁ y₂ hy₂ hy_ne
      have h :=
        qMap_total_fiber_disjoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps)
        (y₁ := y₁) (y₂ := y₂) hy_ne
      simpa [fiberSet] using h
  exact hNat

lemma pairUDRClose_of_pairFiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := Nat.le_of_lt i.isLt) (f := f) (g := g) := by
  unfold pair_fiberwiseClose at h_fw_dist_lt
  unfold pair_UDRClose
  set d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
    h_destIdx h_destIdx_le f g
  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    exact hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f g
  set d_cur := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r))
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega
  have hmul : 2 * (d_fw * 2 ^ steps) ≤ d_next * 2 ^ steps - 2 ^ steps := by
    rw [← mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [← one_mul (2 ^ steps)]
      rw [← Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)]
    exact Nat.mul_le_mul_right _ h_2_fw_dist_le
  have hdist_rel : d_next * 2 ^ steps - 2 ^ steps = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := h_destIdx_le),
      BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (h_i := Nat.le_of_lt i.isLt)]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - destIdx.val + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - destIdx.val + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega
  have h_le_pred : 2 * (d_fw * 2 ^ steps) ≤ d_cur - 1 := by
    omega
  have hcur_pos : 0 < d_cur := by
    dsimp only [d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (h_i := Nat.le_of_lt i.isLt)]
    omega
  exact lt_of_le_of_lt (le_trans h_le h_le_pred)
    (Nat.sub_one_lt (Nat.ne_of_gt hcur_pos))

lemma fiberwiseClose_of_fiberwiseDistance_le_uniqueDecodingRadius
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_le_udr :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        (by simpa using h_destIdx) h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) :
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) := by
  classical
  have h_destIdx_fin : destIdx = (⟨i, by omega⟩ : Fin r).val + steps := by
    simpa using h_destIdx
  set C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)) with hC_dest
  have h_dist_pos : 0 < ‖C_dest‖₀ := by
    have h_pos : 0 <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
      simp [BBF_CodeDistance_eq (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)]
    simpa [C_dest, BBF_CodeDistance] using h_pos
  haveI : NeZero ‖C_dest‖₀ := NeZero.of_pos h_dist_pos
  have h_dest_lt :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
          h_destIdx_fin h_destIdx_le f_i <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) := by
    have h' := (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).1 (by
      simpa [C_dest] using h_le_udr)
    simpa [C_dest, BBF_CodeDistance] using h'
  obtain ⟨g, hg_mem, hg_min⟩ := exists_fiberwiseClosestCodeword 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
    h_destIdx_fin h_destIdx_le f_i
  have h_pair_close : pair_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (⟨i, by omega⟩ : Fin r))
      (destIdx := destIdx) (steps := steps) (h_destIdx := h_destIdx_fin)
      (h_destIdx_le := h_destIdx_le) (f := f_i) (g := g) := by
    dsimp only [pair_fiberwiseClose]
    rw [← hg_min]
    exact h_dest_lt
  have h_pair_udr := pairUDRClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (destIdx := destIdx) (steps := steps) (h_destIdx := h_destIdx_fin)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (g := g)
    (h_fw_dist_lt := h_pair_close)
  have h_source_lt :
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (⟨i, by omega⟩ : Fin r))) <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) := by
    calc
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (⟨i, by omega⟩ : Fin r))) ≤
          2 * Δ₀(f_i, g) := by
        rw [ENat.mul_le_mul_left_iff (ha := by
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
          (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
        exact Code.distFromCode_le_dist_to_mem
          (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (⟨i, by omega⟩ : Fin r)) (u := f_i) (v := g) hg_mem
      _ < _ := by
        exact_mod_cast h_pair_udr
  exact ⟨h_source_lt, h_dest_lt⟩

/-- Lemma 4.22, contrapositive form used by Proposition 4.21 case 2 assembly. -/
lemma not_jointProximityNat_of_not_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    ¬ jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)
      (Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) := by
  intro h_joint
  have h_le := fiberwiseDistance_le_of_jointProximityNat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i
    (Code.uniqueDecodingRadius
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) h_joint
  exact h_far (fiberwiseClose_of_fiberwiseDistance_le_uniqueDecodingRadius 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i h_le)

end
end Binius.BinaryBasefold
