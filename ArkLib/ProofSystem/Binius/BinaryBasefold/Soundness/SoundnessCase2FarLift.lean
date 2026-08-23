/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase2Assembly
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase1Discharge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase1Bridge
import ArkLib.Data.Probability.TensorSchwartzZippel

/-!
# Lemma 4.22, far direction: joint proximity forces fiberwise closeness

DP24 Lemma 4.22 (p.41) far-lift, in contrapositive consumer form: if the pre-tensor stack of
`f` is jointly close (within unique decoding radius) to the interleaved destination code, then
`f` is fiberwise close to the source code. The in-tree `PreTensor*` suite proves the CLOSE
direction (`preTensorCombine_jointProximityNat_of_fiberwiseClose`); this file provides the FAR
direction needed by `prop421Case2_holds_of_bridges`.

Proof skeleton (replacing DP24's novel-coefficient interleaving with a fold-recursion lift):

1. **Codeword extraction**: joint proximity gives an interleaved codeword `V` within UDR of
   `⋈|stack_f` (`closeToCode_iff_closeToCodeword_of_minDist`).
2. **The binary-row lift** (`exists_lift_of_binary_rows`): by induction on `steps`, any family
   of `2^steps` destination codewords arises as the binary-challenge folds of a single source
   codeword `g`. The induction step uses `exists_unfold_of_binary_BBF_Codewords`: two
   level-`(i+1)` codewords have a common level-`i` preimage under the challenge-`0`/`1` folds.
3. **Column transfer** (`fiberEvaluations_eq_of_rows_eq`): if all `2^steps` binary folds of `f`
   and `g` agree at a point `y`, then by the fold/tensor bridge (`hBridge`) the folds agree at
   *every* challenge vector; instantiating at the Boolean points `TensorSZ.cubePoint` turns the
   single-point matrix form into the coordinates of `foldMatrix y *ᵥ fiberEvaluations`, and
   nonsingularity (`foldMatrix_det_ne_zero`) forces the fiber evaluations to agree.
4. **Counting**: hence the per-fiber disagreement set of `(f, g)` embeds into the disagreeing
   columns, `pair_fiberwiseDistance f g ≤ Δ₀(⋈|stack_f, V) ≤ UDR`, and
   `2 · fiberwiseDistance < d_dest` follows.

The corollary `prop421Case2_probability_bound_of_bridge` combines this lift with an explicit
`iterated_fold`/`preTensorCombine` bridge. The global theorem that supplies the bridge from
`Soundness.Incremental` lives in `Prop421Case2Probability` to avoid an import cycle.
-/

set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold

open AdditiveNTT Matrix MvPolynomial Finset InterleavedCode Code
open scoped NNReal ProbabilityTheory
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-! ## Bit arithmetic for the index split -/

private lemma getBit_eq_div_mod (k n : ℕ) : Nat.getBit k n = (n / 2 ^ k) % 2 := by
  unfold Nat.getBit
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

private lemma getBit_mod_two_pow {p n j : ℕ} (hp : p < n) :
    Nat.getBit p (j % 2 ^ n) = Nat.getBit p j := by
  rw [getBit_eq_div_mod, getBit_eq_div_mod]
  have hsplit : 2 ^ n = 2 ^ p * 2 ^ (n - p) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  have hdvd : (2 : ℕ) ∣ 2 ^ (n - p) := dvd_pow_self 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]

private lemma index_split {n : ℕ} (j : Fin (2 ^ (n + 1))) :
    j.val = j.val % 2 ^ n + Nat.getBit n j.val * 2 ^ n := by
  have hlt : j.val / 2 ^ n < 2 :=
    Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact j.isLt)
  have hdm := Nat.div_add_mod j.val (2 ^ n)
  rw [Nat.mul_comm] at hdm
  rw [getBit_eq_div_mod, Nat.mod_eq_of_lt hlt]
  omega

/-- The low part of an index in `Fin (2^(n+1))`. -/
private def lowPart {n : ℕ} (j : Fin (2 ^ (n + 1))) : Fin (2 ^ n) :=
  ⟨j.val % 2 ^ n, Nat.mod_lt _ (pow_pos (by norm_num) n)⟩

private lemma bitsOfIndex_init {n : ℕ} (j : Fin (2 ^ (n + 1))) :
    Fin.init (bitsOfIndex (L := L) j) = bitsOfIndex (L := L) (lowPart j) := by
  funext p
  by_cases h : Nat.getBit p.val j.val = 1
  · simp [Fin.init, bitsOfIndex, lowPart, getBit_mod_two_pow p.isLt, h]
  · simp [Fin.init, bitsOfIndex, lowPart, getBit_mod_two_pow p.isLt, h]

private lemma bitsOfIndex_last {n : ℕ} (j : Fin (2 ^ (n + 1))) :
    bitsOfIndex (L := L) j (Fin.last n) =
      if Nat.getBit n j.val = 1 then (1 : L) else 0 := by
  simp [bitsOfIndex]

/-! ## The binary-row lift -/

/-- **The binary-row lift.** Any family of `2^steps` destination codewords is realized as the
binary-challenge folds of a single source codeword, given the single-step unfold-existence
hypothesis `hUnfold`. This is the recursion-side replacement for DP24's novel-coefficient
interleaving construction. -/
lemma exists_lift_of_binary_rows
    (hUnfold : ∀ (iv : Fin r) {dv : Fin r} (h1 : dv.val = iv.val + 1) (h1le : dv ≤ ℓ)
      (u₀ u₁ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) dv),
      u₀ ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) dv →
      u₁ ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) dv →
      ∃ g, g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) iv ∧
        fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := iv) (destIdx := dv)
          h1 h1le g 0 = u₀ ∧
        fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := iv) (destIdx := dv)
          h1 h1le g 1 = u₁) :
    ∀ (steps : ℕ) (i : Fin r) {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (V : Fin (2 ^ steps) → OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx),
      (∀ j, V j ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) →
      ∃ g, g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ∧
        ∀ j, iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
          (r_challenges := bitsOfIndex (L := L) j) = V j := by
  intro steps
  induction steps with
  | zero =>
    intro i destIdx h_destIdx h_destIdx_le V hV
    have h_eq : destIdx = i := Fin.eq_of_val_eq (by omega)
    subst h_eq
    refine ⟨V 0, hV 0, fun j => ?_⟩
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    funext y
    rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
      (h_destIdx_le := h_destIdx_le)]
    rfl
  | succ n ih =>
    intro i destIdx h_destIdx h_destIdx_le V hV
    have h_mid_lt : i.val + n < r := by
      have := destIdx.isLt
      omega
    set midIdx : Fin r := ⟨i.val + n, h_mid_lt⟩ with hmid_def
    have h_mid_le : midIdx ≤ ℓ := by
      have : destIdx.val ≤ ℓ := h_destIdx_le
      simp only [hmid_def]
      omega
    have h_mid_succ : destIdx.val = midIdx.val + 1 := by
      simp only [hmid_def]
      omega
    -- Pair up rows: indices `m` and `m + 2^n` share an unfolded preimage at `midIdx`.
    have hlow_lt : ∀ m : Fin (2 ^ n), m.val < 2 ^ (n + 1) := fun m =>
      lt_of_lt_of_le m.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hhigh_lt : ∀ m : Fin (2 ^ n), m.val + 2 ^ n < 2 ^ (n + 1) := fun m => by
      have hm := m.isLt
      rw [pow_succ]
      omega
    have hpair : ∀ m : Fin (2 ^ n),
        ∃ w, w ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx ∧
          fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
            h_mid_succ h_destIdx_le w 0 = V ⟨m.val, hlow_lt m⟩ ∧
          fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
            h_mid_succ h_destIdx_le w 1 = V ⟨m.val + 2 ^ n, hhigh_lt m⟩ := by
      intro m
      exact hUnfold midIdx h_mid_succ h_destIdx_le _ _ (hV _) (hV _)
    choose W hWmem hW0 hW1 using hpair
    obtain ⟨g, hg_mem, hg_rows⟩ := ih i (destIdx := midIdx)
      (h_destIdx := by simp only [hmid_def]) h_mid_le W hWmem
    refine ⟨g, hg_mem, fun j => ?_⟩
    -- Peel the last (top-level) fold and identify it with the paired `hUnfold` output.
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (midIdx := midIdx) (destIdx := destIdx) (steps := n)
      (h_midIdx := by simp only [hmid_def]) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := g)
      (r_challenges := bitsOfIndex (L := L) j)]
    rw [bitsOfIndex_init, bitsOfIndex_last]
    rw [hg_rows (lowPart j)]
    rcases Nat.getBit_eq_zero_or_one (k := n) (n := j.val) with hbit | hbit
    · have hc : (if Nat.getBit n j.val = 1 then (1 : L) else 0) = 0 := by
        rw [hbit]
        exact if_neg (by norm_num)
      rw [hc, hW0 (lowPart j)]
      congr 1
      apply Fin.eq_of_val_eq
      have hidx := index_split j
      rw [hbit] at hidx
      simp only [lowPart]
      omega
    · have hc : (if Nat.getBit n j.val = 1 then (1 : L) else 0) = 1 := by
        rw [hbit]
        exact if_pos rfl
      rw [hc, hW1 (lowPart j)]
      congr 1
      apply Fin.eq_of_val_eq
      have hidx := index_split j
      rw [hbit] at hidx
      simp only [lowPart]
      omega

/-! ## The column transfer -/

/-- **Column transfer.** If all `2^steps` binary-challenge folds of `f` and `g` agree at `y`,
the fiber evaluations of `f` and `g` over `y` agree — via the fold/tensor bridge at all
challenges, the single-point matrix form at the Boolean points, and fold-matrix
nonsingularity. -/
lemma fiberEvaluations_eq_of_binary_rows_eq
    (hBridge : ∀ (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
      (r_chal : Fin steps → L),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
          (r_challenges := r_chal)
        = multilinearCombine (F := L)
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal)
    (i : Fin ℓ) (steps : ℕ) (hsteps : steps ≠ 0) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (hrows : ∀ j : Fin (2 ^ steps),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := bitsOfIndex (L := L) j) y
      = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
        (r_challenges := bitsOfIndex (L := L) j) y) :
    fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y)
      = fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y) := by
  -- 1. All-challenge agreement at `y` via the bridge.
  have hall : ∀ rc : Fin steps → L,
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := rc) y
      = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
        (r_challenges := rc) y := by
    intro rc
    rw [hBridge i steps h_destIdx h_destIdx_le f rc,
      hBridge i steps h_destIdx h_destIdx_le g rc]
    unfold multilinearCombine
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact hrows j
  -- 2. At the Boolean points, the matrix form turns agreement into coordinatewise equality of
  -- `foldMatrix y *ᵥ fiberEvaluations`.
  have hM : Matrix.mulVec
        (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
          (steps := steps) h_destIdx h_destIdx_le y)
        (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y))
      = Matrix.mulVec
        (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
          (steps := steps) h_destIdx h_destIdx_le y)
        (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y)) := by
    funext j
    have hj := hall (TensorSZ.cubePoint L steps j)
    rw [← single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le
        i.isLt f (TensorSZ.cubePoint L steps j) y,
      ← single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le
        i.isLt g (TensorSZ.cubePoint L steps j) y] at hj
    simp only [single_point_localized_fold_matrix_form] at hj
    -- The challenge tensor at a cube point is the indicator at `j`.
    have hind : ∀ idx : Fin (2 ^ steps),
        (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) steps
          (TensorSZ.cubePoint L steps j)).get idx = if idx = j then 1 else 0 := by
      intro idx
      rw [challengeTensorProduct_get_eq_tensorWeight_eval (hm := hsteps)]
      exact TensorSZ.tensorWeight_eval_cube L steps idx j
    -- Dotting an indicator extracts the coordinate.
    have hdot : ∀ w : Fin (2 ^ steps) → L,
        dotProduct (fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
          steps (TensorSZ.cubePoint L steps j)).get idx) w = w j := by
      intro w
      unfold dotProduct
      have hsummand : ∀ idx : Fin (2 ^ steps),
          (fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
            steps (TensorSZ.cubePoint L steps j)).get idx) idx * w idx
          = (if idx = j then 1 else 0) * w idx := fun idx => by
        dsimp only
        rw [hind idx]
      calc
        (∑ idx, (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
            steps (TensorSZ.cubePoint L steps j)).get idx * w idx)
            = ∑ idx, (if idx = j then 1 else 0) * w idx := by
              apply Finset.sum_congr rfl
              intro idx _
              exact hsummand idx
        _ = w j := by
              simp [Finset.sum_ite_eq', ite_mul]
    rw [hdot, hdot] at hj
    exact hj
  -- 3. Nonsingularity.
  have hdet := foldMatrix_det_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r)) (steps := steps) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (y := y)
  have hsub := sub_eq_zero.mpr hM
  rw [← Matrix.mulVec_sub] at hsub
  have hzero := Matrix.eq_zero_of_mulVec_eq_zero hdet hsub
  have := sub_eq_zero.mp hzero
  exact this

set_option maxHeartbeats 1200000 in
/-- Source Hamming distance is bounded by the number of bad quotient fibers times the fiber
size. Local port of the (currently commented-out) `Code.lean` lemma onto the per-fiber
disagreement surface. -/
lemma hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps_farLiftLocal
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

lemma pairUDRClose_of_pairFiberwiseClose_farLift
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
    exact hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps_farLiftLocal 𝔽q β
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

/-! ## The far-lift -/

set_option maxHeartbeats 1200000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **Lemma 4.22, far direction (contrapositive form).** Joint proximity of the pre-tensor
stack at unique decoding radius forces fiberwise closeness of the source word. -/
lemma fiberwiseClose_of_jointProximityNat_farLiftLocal
    (hBridge : ∀ (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
      (r_chal : Fin steps → L),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
          (r_challenges := r_chal)
        = multilinearCombine (F := L)
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal)
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (hJP : jointProximityNat
      (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
        : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)
      (Code.uniqueDecodingRadius
        (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
          : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L))))) :
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i) := by
  classical
  set C_dest : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L) :=
    ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx → L)) with hC_def
  set e : ℕ := Code.uniqueDecodingRadius (C := C_dest) with he_def
  set u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i with hu_def
  -- 1. Extract a close interleaved codeword.
  unfold jointProximityNat at hJP
  obtain ⟨V, hV_mem, hV_close⟩ :=
    (closeToCode_iff_closeToCodeword_of_minDist (⋈|u) e).mp hJP
  -- 2. Lift its rows to a source codeword.
  obtain ⟨g, hg_mem, hg_rows⟩ := exists_lift_of_binary_rows 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (fun iv dv h1 h1le u₀ u₁ hu₀ hu₁ =>
      exists_unfold_of_binary_BBF_Codewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := iv) (destIdx := dv) h1 h1le u₀ u₁ hu₀ hu₁)
    steps ⟨i, by omega⟩
    (destIdx := destIdx) h_destIdx h_destIdx_le
    (fun j => fun y => V y j)
    (fun j => hV_mem j)
  -- 3. Per-fiber disagreements embed into disagreeing columns.
  have hsubset :
      fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i g ⊆
      Finset.univ.filter (fun y => (⋈|u) y ≠ V y) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hcol
    rw [mem_fiberwiseDisagreementSetPerFiber] at hy
    rcases hy with ⟨idx, hidx⟩
    apply hidx
    have hveq := fiberEvaluations_eq_of_binary_rows_eq 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) hBridge i steps (NeZero.ne steps)
      h_destIdx h_destIdx_le f_i g y
      (fun j => by
        have hcol_j := congrFun hcol j
        have hrow_g := congrFun (hg_rows j) y
        -- NOTE: do NOT prove this by `rfl`: the kernel-side defeq pits the low-height
        -- `Interleavable.interleave` projection against the high-height `iterated_fold`,
        -- forcing the kernel to expand the `Fin.dfoldl`/`cast` tower (memory blowup).
        -- The rewrite chain below reaches a common head cheaply instead.
        have hrow_f : (⋈|u) y j
            = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
              (r_challenges := bitsOfIndex (L := L) j) y := by
          rw [interleave_wordStack_eq, Matrix.transpose_apply, hu_def,
            preTensorCombine_WordStack]
        rw [hrow_f] at hcol_j
        rw [hcol_j, ← hrow_g])
    exact congrFun hveq idx
  -- 4. Counting: pair distance ≤ Hamming distance to V ≤ UDR.
  have hpair_le : pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i g ≤ e := by
    unfold pair_fiberwiseDistance
    calc (fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le f_i g).card
        ≤ (Finset.univ.filter (fun y => (⋈|u) y ≠ V y)).card :=
          Finset.card_le_card hsubset
      _ = Δ₀((⋈|u), V) := by
          rw [hammingDist]
      _ ≤ e := hV_close
  -- 5. Conclude fiberwise closeness.
  have hfwd_le : fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i ≤ e := by
    unfold fiberwiseDistance
    refine le_trans (Nat.sInf_le ?_) hpair_le
    exact ⟨⟨g, hg_mem⟩, Set.mem_univ _, rfl⟩
  have hd : 1 ≤ BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx h_destIdx_le]
    omega
  have he_eq : e = (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx - 1) / 2 := by
    simp only [he_def, hC_def]
    rfl
  unfold fiberwiseClose
  have he_lt :
      2 * e < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
    omega
  have hpair_close : pair_fiberwiseClose 𝔽q β
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i g := by
    unfold pair_fiberwiseClose
    omega
  have hpair_udr := pairUDRClose_of_pairFiberwiseClose_farLift 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i) (g := g)
    (h_fw_dist_lt := hpair_close)
  have hsource_close :
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (⟨i, by omega⟩ : Fin r))) <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) := by
    calc
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (⟨i, by omega⟩ : Fin r))) ≤ 2 * Δ₀(f_i, g) := by
        rw [ENat.mul_le_mul_left_iff
          (ha := by simp)
          (h_top := by simp)]
        exact Code.distFromCode_le_dist_to_mem
          (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (⟨i, by omega⟩ : Fin r)) :
              Set ((sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i, by omega⟩ : Fin r) → L)))
          f_i g hg_mem
      _ < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) := by exact_mod_cast hpair_udr
  have hfiber_close :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le f_i <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) := by
    omega
  exact ⟨hsource_close, hfiber_close⟩

/-- **Proposition 4.21 Case 2, reduced to the fold/tensor bridge.** -/
lemma prop421Case2_probability_bound_of_bridge
    (hBridge : ∀ (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
      (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
      (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
      (r_chal : Fin steps → L),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
          (r_challenges := r_chal)
        = multilinearCombine (F := L)
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal)
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let next_domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      let f_next := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        h_destIdx h_destIdx_le f_i r
      UDRClose 𝔽q β destIdx h_destIdx_le f_next
    ] ≤ ((steps * next_domain_size) / Fintype.card L) :=
  prop421Case2_probability_bound_of_bridges 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) hBridge
    (fun i steps _ _destIdx h_destIdx h_destIdx_le f_i h_far hJP =>
      h_far (fiberwiseClose_of_jointProximityNat_farLiftLocal 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        hBridge i steps h_destIdx h_destIdx_le f_i hJP))
    i steps h_destIdx h_destIdx_le f_i h_far

end

end Binius.BinaryBasefold
