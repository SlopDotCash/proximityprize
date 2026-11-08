/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import ProximityPrize.Compatibility.BiniusFolding

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Compliance
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.Data.MvPolynomial.MultilinearComputational
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# Binius binary Basefold: oracle bookkeeping

We set up the round/oracle indexing arithmetic for the binary-field Basefold protocol over `ℓ`
folding rounds committing every `ϑ` rounds. `toOutCodewordsCount` counts the codewords available
as oracles at each round and `isCommitmentRound` marks the commitment rounds; the bulk of the file
proves the arithmetic facts about these counts (e.g. `toOutCodewordsCount_succ_eq`,
`toOutCodewordsCount_last`) and the index-range bounds (`oracle_index_le_ℓ`,
`oracle_block_k_bound`, ...) used to address oracle positions and map them to domain indices via
`oraclePositionToDomainIndex` and `mkLastOracleIndex`.
-/

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

/-- Binary expansion of an index in statement-variable order.

The historical downstream statement convention stored variables in reverse order. This helper
retains that explicit Boolean-index view; canonical statements use chronological prefix order. -/
def statementOrderBitsOfIndex {L : Type} [Field L] {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun j => bitsOfIndex (L := L) k (Fin.rev j)

/-- Reverse the historical newest-first compatibility vector into chronological folding order.
Canonical statement challenges are already chronological and must not be passed through this
conversion without an explicit compatibility boundary. -/
def foldOrderChallenges {ℓ : ℕ} {L : Type} {i : Fin (ℓ + 1)}
    (challenges : Fin i → L) : Fin i → L :=
  fun j => challenges (Fin.rev j)

@[simp]
lemma foldOrderChallenges_cons {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
      (Fin.cons (α := fun _ => L) r_i' challenges) =
    (fun j : Fin i.succ =>
        Fin.snoc (n := i.val) (α := fun _ => L)
          (foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges) r_i' j) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp [foldOrderChallenges]
  | cast k =>
      simp [foldOrderChallenges, Fin.rev_castSucc]

/-- Old-block invariance for the fold-order view after prepending a fresh challenge.

Since statement vectors are newest-first, prepending `r_i'` via `Fin.cons` leaves every *earlier*
fold-order position unchanged. This is the `Fin.snoc_castSucc` face of `foldOrderChallenges_cons`. -/
lemma foldOrderChallenges_cons_of_lt {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) (idx : Fin i.castSucc) :
    foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
        (Fin.cons (α := fun _ => L) r_i' challenges) idx.castSucc =
      foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges idx := by
  have hfo := foldOrderChallenges_cons (ℓ := ℓ) (L := L) i challenges r_i'
  exact (congrFun hfo idx.castSucc).trans
    (Fin.snoc_castSucc (n := i.val) (α := fun _ : Fin (i.val + 1) => L)
      (x := r_i') (p := foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges)
      (i := idx))

/-- The fresh challenge lands at the last fold-order position after `Fin.cons`.
This is the `Fin.snoc_last` face of `foldOrderChallenges_cons`. -/
lemma foldOrderChallenges_cons_last {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
        (Fin.cons (α := fun _ => L) r_i' challenges) (Fin.last i.val) = r_i' := by
  have hfo := foldOrderChallenges_cons (ℓ := ℓ) (L := L) i challenges r_i'
  exact (congrFun hfo (Fin.last i.val)).trans
    (Fin.snoc_last (n := i.val) (α := fun _ : Fin (i.val + 1) => L)
      (x := r_i') (p := foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges))

/-- Extract the challenge vector belonging to an older oracle frontier from a later statement.

If `stmtIdx = oracleIdx + d`, the newest `d` statement challenges are not yet reflected in the
oracle frontier. Since statement vectors are newest-first, the older frontier is the suffix beginning
at offset `d`. -/
def olderStmtChallenges {ℓ : ℕ} {L : Type} {stmtIdx oracleIdx : Fin (ℓ + 1)}
    (h_le : oracleIdx.val ≤ stmtIdx.val) (challenges : Fin stmtIdx → L) :
    Fin oracleIdx → L :=
  fun j => challenges ⟨stmtIdx.val - oracleIdx.val + j.val, by
    have hj : j.val < oracleIdx.val := j.isLt
    omega⟩

@[simp]
lemma olderStmtChallenges_self {ℓ : ℕ} {L : Type} {i : Fin (ℓ + 1)}
    (challenges : Fin i → L) :
    olderStmtChallenges (ℓ := ℓ) (oracleIdx := i) (stmtIdx := i) (by rfl) challenges =
      challenges := by
  funext j
  simp only [olderStmtChallenges, Nat.sub_self, zero_add, Fin.eta]

@[simp]
lemma olderStmtChallenges_cons_castSucc {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
      (Fin.cons (α := fun _ => L) r_i' challenges) =
      challenges := by
  funext j
  simp only [olderStmtChallenges, Fin.val_succ, Fin.val_castSucc]
  let idx : Fin i.succ := ⟨i.val + 1 - i.val + j.val, by
      have hval : i.val + 1 - i.val + j.val = j.val + 1 := by
        rw [Nat.add_sub_cancel_left]
        exact Nat.add_comm 1 j.val
      have hj := j.isLt
      simp only [Fin.val_castSucc] at hj
      simp only [hval, Fin.val_succ]
      omega⟩
  have hidx : idx = j.succ := by
    apply Fin.ext
    simp only [idx, Fin.val_succ]
    rw [Nat.add_sub_cancel_left]
    exact Nat.add_comm 1 j.val
  change (Fin.cons (n := i.val) (α := fun _ => L) r_i' challenges) idx = challenges j
  exact Eq.trans (congrArg (Fin.cons (n := i.val) (α := fun _ => L) r_i' challenges) hidx)
    (Fin.cons_succ (n := i.val) (α := fun _ => L) r_i' challenges j)

@[simp]
lemma olderStmtChallenges_succ_castSucc {ℓ : ℕ} {L : Type} (i : Fin ℓ)
    (challenges : Fin i.succ → L) :
    olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges =
      Fin.tail challenges := by
  rw [← Fin.cons_self_tail challenges]
  exact olderStmtChallenges_cons_castSucc i (Fin.tail challenges)
    (challenges ⟨0, by simp only [Fin.val_succ]; omega⟩)

section OracleStatementIndex
variable (ℓ : ℕ) (ϑ : ℕ) [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

lemma div_add_one_eq_if_dvd (i ϑ : ℕ) [NeZero ϑ] :
    (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ := by
  split_ifs with h_dvd
  case pos => exact Nat.succ_div_of_dvd h_dvd
  case neg => exact Nat.succ_div_of_not_dvd h_dvd

/-- Historical spelling of the canonical commitment-round predicate. -/
abbrev isCommitmentRound (i : Fin ℓ) : Prop := IsCommitmentRound ℓ ϑ i

omit [NeZero ϑ] hdiv in
lemma toOutCodewordsCountOf0 : toOutCodewordsCount ℓ ϑ 0 = 1 :=
  toOutCodewordsCount_zero ℓ ϑ

omit [NeZero ϑ] [NeZero ℓ] hdiv in
lemma toCodewordsCount_mul_ϑ_le_i (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ ≤
    (if i.val < ℓ then i.val else ℓ - ϑ) := by
  intro j
  split_ifs with h_il
  -- Case 1: i.val < ℓ
  case pos =>
    have hj : j.val ≤ i.val / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte] at hj_lt
      omega
    have h_mul := Nat.mul_le_mul_right ϑ hj
    exact h_mul.trans (Nat.div_mul_le_self i.val ϑ)
  -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
  case neg =>
    have h_ival_eq_l : i.val = ℓ := by omega
    have hj : j.val < ℓ / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte, add_zero] at hj_lt
      apply Nat.succ_lt_succ
      calc j.val < i.val / ϑ := by omega
        _ = _ := by congr
    have hj : j.val ≤ ℓ / ϑ - 1 := by apply Nat.le_sub_one_of_lt hj
    have h_mul := Nat.mul_le_mul_right ϑ hj
    rw [Nat.mul_sub_right_distrib, one_mul] at h_mul
    exact h_mul.trans (Nat.sub_le_sub_right (Nat.div_mul_le_self ℓ ϑ) ϑ)

lemma toOutCodewordsCount_i_le_of_succ (i : Fin ℓ) :
    toOutCodewordsCount ℓ ϑ i.castSucc ≤ toOutCodewordsCount ℓ ϑ i.succ := by
  rw [toOutCodewordsCount_succ_eq ℓ ϑ]
  split_ifs
  · omega
  · omega

omit [NeZero ℓ] hdiv in
/--
If a new oracle is committed at round `i + 1` (i.e., `ϑ ∣ i + 1`), then the index of this
new oracle (which is the count of oracles from the previous round, `i`) multiplied by `ϑ`
equals the current round number `i + 1`.
The proof uses the commitment-round hypothesis to recover divisibility at `i + 1`.
-/
lemma toOutCodewordsCount_mul_ϑ_eq_i_succ (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.coe_castSucc, i.isLt, ↓reduceIte]
  have h_mod : i.val % ϑ = ϑ - 1 := by
    refine (mod_eq_sub_iff ?_ ?_).mpr hCR.1
    · omega
    · exact NeZero.one_le
  -- After unfolding, we have: (i.val / ϑ + 1) * ϑ = i.val + 1
  rw [Nat.add_mul, one_mul]
  -- Now we have: (i.val / ϑ) * ϑ + ϑ = i.val + 1
  -- Since ϑ ∣ (i.val + 1), we can use Nat.div_mul_cancel
  -- ⊢ ↑i / ϑ * ϑ + ϑ = ↑i + 1
  rw [Nat.div_mul_self_eq_mod_sub_self, h_mod]
  rw [←Nat.sub_add_comm (k:=ϑ - 1) (m:=ϑ) (by
    calc _ = i.val % ϑ := by omega
      _ ≤ i := by exact Nat.mod_le (↑i) ϑ
  )]
  -- ⊢ ↑i + ϑ - (ϑ - 1) = ↑i + 1
  rw [Nat.sub_sub_right (a:=i.val + ϑ) (b:=ϑ) (c:=1) (by exact NeZero.one_le)]
  omega

lemma toCodewordsCount_mul_ϑ_lt_ℓ (ℓ ϑ : ℕ) [NeZero ϑ] [NeZero ℓ] (i : Fin (ℓ + 1)) :
    ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ < ℓ := by
  intro j
  unfold toOutCodewordsCount
  have h_j_lt : j.val < i.val / ϑ + if i.val < ℓ then 1 else 0 := j.2
  have h_j_mul_ϑ_lt := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  calc
    ↑j * ϑ ≤ if ↑i < ℓ then ↑i else ℓ - ϑ := by omega
    _ < _ := by
      by_cases h_i_lt_ℓ : i.val < ℓ
      · -- Case 1: i.val < ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte]
      · -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte, tsub_lt_self_iff]
        constructor
        · exact pos_of_neZero ℓ
        · exact pos_of_neZero ϑ

/-- Historical spelling of the canonical last committed-oracle position. -/
abbrev mkLastOracleIndex (i : Fin (ℓ + 1)) : Fin (toOutCodewordsCount ℓ ϑ i) :=
  getLastOraclePositionIndex ℓ ϑ i

lemma mkLastOracleIndex_last : mkLastOracleIndex ℓ ϑ (Fin.last ℓ) = ℓ / ϑ - 1 := by
  exact congrArg Fin.val (getLastOraclePositionIndex_last ℓ ϑ)

lemma mkLastOracleIndex_eq_getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    mkLastOracleIndex ℓ ϑ i = getLastOraclePositionIndex ℓ ϑ i := rfl

end OracleStatementIndex

-- The structured-sumcheck primitives (`MultilinearPoly`, `MultiquadraticPoly`,
-- `SumcheckMultiplierParam`, `computeInitialSumcheckPoly`, `projectToMidSumcheckPoly`,
-- `projectToNextSumcheckPoly`) now live in `ArkLib.ProofSystem.Sumcheck.Structured`.
-- We re-export them under the `Binius.BinaryBasefold` namespace so that existing
-- references — qualified or unqualified — continue to resolve.
-- See `GENERIC_RING_SWITCHING_PLAN.md` §1.5 for the rationale.
export Sumcheck.Structured (MultilinearPoly MultiquadraticPoly
  SumcheckMultiplierParam computeInitialSumcheckPoly
  projectToMidSumcheckPoly projectToNextSumcheckPoly)

/-- Computable multilinear polynomial from hypercube evaluations (`CMvPolynomial` / `CMLE'`).
See `MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE'`. -/
def MultilinearPoly.ofCMLEEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) : MultilinearPoly L ℓ :=
  ⟨CPoly.fromCMvPolynomial (MvPolynomial.Computational.CMLE' evals), by
    rw [MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE']
    unfold MLE'
    exact MLE_mem_restrictDegree (evals ∘ finFunctionFinEquiv)⟩

theorem MultilinearPoly.ofCMLEEvals_val {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) :
    (ofCMLEEvals evals).val = MLE' evals := by
  simpa [ofCMLEEvals] using MvPolynomial.Computational.fromCMvPolynomial_CMLE'_eq_MLE' evals

/-- Same carrier as `⟨MLE evals, MLE_mem_restrictDegree evals⟩`, built via `CMLE'`. -/
def MultilinearPoly.ofHypercubeEvals {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) : MultilinearPoly L ℓ :=
  ofCMLEEvals (fun i => evals (finFunctionFinEquiv.symm i))

theorem MultilinearPoly.ofHypercubeEvals_val {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : (Fin ℓ → Fin 2) → L) :
    (ofHypercubeEvals evals).val = MLE evals := by
  rw [ofHypercubeEvals, ofCMLEEvals_val, MLE']
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

theorem MultilinearPoly.ofCMLEEvals_eval_zeroOne {L : Type} [CommRing L] [BEq L] [LawfulBEq L] {ℓ : ℕ}
    (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val = evals (finFunctionFinEquiv x) := by
  simpa [ofCMLEEvals_val] using MLE'_eval_zeroOne x evals

theorem MultilinearPoly.ofCMLEEvals_cmEval_eq_val_eval {L : Type} [CommRing L] [BEq L] [LawfulBEq L]
    {ℓ : ℕ} (evals : Fin (2 ^ ℓ) → L) (x : Fin ℓ → Fin 2) :
    CPoly.CMvPolynomial.eval (x : Fin ℓ → L) (MvPolynomial.Computational.CMLE' evals) =
      MvPolynomial.eval (x : Fin ℓ → L) (ofCMLEEvals evals).val := by
  rw [CPoly.eval_equiv]
  simpa [ofCMLEEvals]

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  -- [SampleableType L] => not used
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section IndexBounds
omit hdiv in
/-- ϑ is positive -/
lemma folding_steps_pos : (ϑ : ℕ) > 0 := pos_of_neZero ϑ

omit hdiv in
/-- ℓ - ϑ < ℓ when both are positive -/
lemma rounds_sub_steps_lt : ℓ - ϑ < ℓ :=
  Nat.sub_lt (pos_of_neZero ℓ) (folding_steps_pos)

lemma ϑ_sub_one_le_self : ϑ - 1 < ϑ := by
  have lt_0: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  exact Nat.sub_one_lt_of_lt lt_0

@[simp] -- main lemma for bIdx: Fin (ℓ / ϑ - 1) bounds
lemma bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x ≤ ℓ - ϑ := by
  have h_x_lt : x < ϑ + 1 := Nat.lt_succ_of_le hx
  have h_fin : x < ϑ ∨ x = ϑ := Nat.lt_or_eq_of_le hx
  calc
    ↑bIdx * ϑ + x ≤ ↑bIdx * ϑ + ϑ := by omega
    _ = (↑bIdx + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ = ℓ - ϑ := by
      have h_bound : 1 ≤ ℓ / ϑ := by
        have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
        rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
      rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    _ ≤ ℓ - ϑ := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_lt_ℓ_succ {m : ℕ} (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin ϑ) :
    ↑bIdx * ϑ + ↑i < ℓ + m :=
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt
    _ ≤ ℓ + m := by omega

@[simp]
lemma bIdx_mul_ϑ_add_x_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x < ℓ + 1 := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx x (hx:=hx)
    _ < ℓ + 1 := by omega

/-- When the block size allows it, we can get a strict inequality -/
lemma bIdx_succ_mul_ϑ_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) :
    (↑bIdx + 1) * ϑ < ℓ + 1 := by
  calc
    (↑bIdx + 1) * ϑ = ↑bIdx * ϑ + ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx ϑ (hx:=by omega)
    _ < ℓ + 1 := by omega

lemma bIdx_succ_mul_ϑ_le_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) : (↑bIdx + 1) * ϑ ≤ ℓ + 1 := by
  exact Nat.le_of_lt (bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx)
end IndexBounds

namespace OracleFrontierIndex

omit r L 𝔽q ℓ 𝓡 ϑ γ_repetitions [NeZero r] [Field L] [Fintype L]
  [DecidableEq L] [CharP L 2] [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  h_Fq_char_prime hF₂ [Algebra 𝔽q L] β hβ_lin_indep h_β₀_eq_1 [NeZero ℓ]
  [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 hdiv in
lemma val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx {m : ℕ} (i : Fin m) :
    (mkFromStmtIdxCastSuccOfSucc (ℓ := m) i).val =
      (mkFromStmtIdx (ℓ := m) i.castSucc).val := by rfl

attribute [simp] val_mkFromStmtIdx val_mkFromStmtIdxCastSuccOfSucc val_le_i
  val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx

end OracleFrontierIndex

section OracleReductionComponents
-- In this section, we use notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-!
## Core Protocol Structures

Basic structures and definitions used throughout the Binary Basefold protocol.
-/

-- `SumcheckBaseContext` and `Statement` now live in `ArkLib.ProofSystem.Sumcheck.Structured`.
-- Re-exported so existing references — qualified or unqualified — continue to resolve.
export Sumcheck.Structured (SumcheckBaseContext Statement)

def toStatement (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) :=
  {
    sumcheck_target := stmt.sumcheck_target,
    challenges := stmt.challenges,
    ctx := stmt.ctx
  }

/-- **Oracle HEq congruence.** An oracle family at propositionally equal positions gives
heterogeneously equal oracles (their types are equal by `congrArg`). -/
lemma OracleStatement.oracle_heq_congr {i : Fin (ℓ + 1)}
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    {j j' : Fin (toOutCodewordsCount ℓ ϑ (i := i))} (h_j : j = j') :
    HEq (oStmtIn j) (oStmtIn j') := by
  subst h_j
  rfl

/-- **Cast-lambda HEq congruence.** A domain-cast precomposition of an oracle at position `j`
is heterogeneously equal to the oracle at a propositionally equal position `j'`. This matches
the `getFirstOracle`-style goals where the cast is baked into a lambda. -/
lemma OracleStatement.oracle_cast_lambda_heq {i : Fin (ℓ + 1)}
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    {j j' : Fin (toOutCodewordsCount ℓ ϑ (i := i))} (h_j : j = j')
    {D : Type}
    (hdom : D = ((sDomain 𝔽q β h_ℓ_add_R_rate)
        ⟨j * ϑ, by have := toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j; omega⟩ : Type))
    (hD : D = ((sDomain 𝔽q β h_ℓ_add_R_rate)
        ⟨j' * ϑ, by have := toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j'; omega⟩ : Type)) :
    HEq (fun y : D => oStmtIn j (cast hdom y)) (oStmtIn j') := by
  subst h_j
  subst hdom
  refine heq_of_eq (funext fun y => ?_)
  rw [cast_eq]

/-- The extractor that recovers the multilinear polynomial t from f^(i) -/
noncomputable def extractMLP (i : Fin ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) :
    Option (L⦃≤ 1⦄[X Fin (ℓ - i)]) := by
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e: ℕ := d.toNat
  let k : ℕ := 2^(ℓ - i.val) -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega), hF₂.out]
    have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
    convert h_equiv
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  let berlekamp_welch_result: Option L[X] := BerlekampWelch.decoder e k ωs f_vals

  match berlekamp_welch_result with
  | none => exact none -- Decoder failed
  | some P =>
    -- 5. Check if degree < 2^ℓ (unique decoding condition)
    if hp_deg_lt: P.natDegree ≥ 2^(ℓ - i.val) then
      exact none -- Outside unique decoding radius
    else
      -- 6. Convert P(X) from monomial basis to novel polynomial basis
      -- P(X) = Σᵢ aᵢ Xᵢ (monomial) → P(X) = Σⱼ tⱼ X_{j}(X) (novel)
      -- We need the inverse of the change-of-basis matrix
      have h_deg_bound : P ∈ Polynomial.degreeLT L (2^(ℓ - i.val)) := by
        rw [Polynomial.mem_degreeLT]
        by_cases hi: i = ℓ
        · simp only [hi, tsub_self, pow_zero, cast_one]
          by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0, degree_zero]; omega
          · simp only [hi, tsub_self, pow_zero, ge_iff_le, not_le, lt_one_iff] at hp_deg_lt
            have h_deg_p: P.degree = 0 := by omega
            simp only [h_deg_p]
            omega
        · by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0];
            have h_i_lt_ℓ : i < ℓ := by omega
            simp only [degree_zero, cast_pow, cast_ofNat, gt_iff_lt]
            -- ⊢ ⊥ < 2 ^ (ℓ - ↑i)
            have h_deg_ne_bot : 2 ^ (ℓ - ↑i) ≠ ⊥ := by
              exact not_isBot_iff_ne_bot.mp fun a ↦ hp_deg_lt (a P.natDegree)
            exact compareOfLessAndEq_eq_lt.mp rfl
          · have h := Polynomial.natDegree_lt_iff_degree_lt (p:=P) (n:=2 ^ (ℓ - ↑i))
              (hp:=by exact hp_p_eq_0)
            rw [←h]; omega
      let P_bounded : L⦃<2^(ℓ - i.val)⦄[X] := ⟨P, h_deg_bound⟩
      -- Get monomial coefficients of P(X)
      let monomial_coeffs : Fin (2^(ℓ - i.val)) → L := fun i => P.coeff i.val
      -- Convert to novel polynomial basis coefficients using change of basis
      -- The changeOfBasisMatrix A has A[j,i] = coeff of X^i in novel basis vector X_j
      -- So we need A⁻¹ to convert monomial coeffs → novel coeffs
      let novel_coeffs : Option (Fin (2^(ℓ - i.val)) → L) :=
        let h_ℓ_le_r : ℓ ≤ r := by
          -- ℓ + 𝓡 < r implies ℓ < r, hence ℓ ≤ r
          have : ℓ < r := by omega
          exact Nat.le_of_lt this
        some (AdditiveNTT.monomialToNovelCoeffs 𝔽q β (ℓ - i.val) (by omega) monomial_coeffs)

      match novel_coeffs with
      | none => exact none
      | some t_coeffs =>
        -- Interpret novel coeffs as Lagrange cosefficients on Boolean hypercube
        -- and reconstruct the multilinear polynomial using MLE
        let hypercube_evals : (Fin (ℓ - i.val) → Fin 2) → L := fun w =>
          -- Map Boolean hypercube point w to its linear index
          let w_index : Fin (2^(ℓ - i.val)) := Nat.binaryFinMapToNat
            (n:=ℓ - i.val) (m:=w) (h_binary:=by intro j; simp only [Nat.cast_id]; omega)
          t_coeffs w_index

        let t_multilinear_mv := MvPolynomial.MLE hypercube_evals
        exact some ⟨t_multilinear_mv, MLE_mem_restrictDegree hypercube_evals⟩

def zeroLastWitness :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) := {
  t := ⟨0, by apply zero_mem⟩,
  H := ⟨0, by apply zero_mem⟩,
  f := fun _ => 0
}

-- `InitialStatement` was orphaned by the `RingSwitching/` extraction (its sole consumer,
-- `RingSwitching.MLPEvalStatement`, now defines the same 2-field shape locally).
-- Removed as part of the post-extraction cleanup.

open Classical in
def snoc_oracle {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.succ),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j =>
  have h_succ_val: i.succ.val = i.val + 1 := rfl
  if hj: j.val < (toOutCodewordsCount ℓ ϑ i.castSucc) then
    oStmtIn ⟨j, by omega⟩
  else -- j.val ≥ toOutCodewordsCount ℓ ϑ i.castSucc
    -- simp only [not_lt] at hj
    if hi: isCommitmentRound ℓ ϑ i then
      -- NEW PROOF --
      -- 1. Prove that the oracle count increases by exactly one.
      have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ =
        toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
        exact Eq.symm ((fun ℓ ϑ [NeZero ℓ] [NeZero ϑ] i ↦
          (toOutCodewordsCount_succ_eq_add_one_iff ℓ ϑ i).mp) ℓ ϑ i hi)
      -- 2. Prove that j must be the index of the new, last oracle.
      have h_j_eq_last_idx : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
        apply Nat.le_antisymm
        · rw [← Nat.lt_succ_iff]
          simp only [Nat.succ_eq_add_one]
          simp only [← h_count_succ, Fin.is_lt];
        · simp only [not_lt] at hj; exact hj
      have h_commit_round : j.val * ϑ = i.succ.val := by
        rw [h_j_eq_last_idx]
        -- This works iff i.succ < ℓ, since i.succ ≠ ℓ, this is TRUE
        have hi_succ_lt_ℓ: i.succ.val < ℓ := by
          have hi_succ_le_ℓ: i.succ.val ≤ ℓ := by omega
          have hi_succ_ne_ℓ: i.succ.val ≠ ℓ := by
            rw [h_succ_val]
            exact hi.2
          exact Nat.lt_of_le_of_ne hi_succ_le_ℓ hi_succ_ne_ℓ
        rw [toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hi]
        rfl
      have h_domain :
          ↥(sDomain 𝔽q β h_ℓ_add_R_rate destIdx) =
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.succ.val, by omega⟩) := by
        have h_fin : destIdx = (⟨i.succ.val, by omega⟩ : Fin r) := by
          apply Fin.eq_of_val_eq
          rw [h_destIdx]
          rfl
        exact congrArg (fun idx => ↥(sDomain 𝔽q β h_ℓ_add_R_rate idx)) h_fin
      cast (by
        simp only [OracleFunction, OracleStatement]
        simp_rw [h_commit_round]
        exact congrArg (fun D : Type => D → L) h_domain) newOracleFn
    else
      (false_of_newOracleIndex_of_not_isCommitmentRound hj hi).elim

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma snoc_oracle_new_heq_of_commit {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc) :
    HEq (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      h_destIdx oStmtIn newOracleFn j) newOracleFn := by
  subst h_destIdx
  unfold snoc_oracle
  simp only [hCR, hj, ↓reduceDIte]
  exact cast_heq _ newOracleFn

def take_snoc_oracle (i : Fin ℓ)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    {destIdx : Fin r} (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) → -- We specify range type so Lean won't be stuck
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j
    := fun j => snoc_oracle 𝔽q β h_destIdx oStmtIn newOracleFn ⟨j, by
      have h : (toOutCodewordsCount ℓ ϑ i.castSucc) ≤ toOutCodewordsCount ℓ ϑ i.succ := by
        exact toOutCodewordsCount_i_le_of_succ ℓ ϑ i
      omega
    ⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma take_snoc_oracle_eq_oStmtIn (i : Fin ℓ)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    {destIdx : Fin r} (h_destIdx : destIdx = ⟨i.val + 1, by omega⟩)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    (take_snoc_oracle 𝔽q β i oStmtIn h_destIdx newOracleFn) = oStmtIn := by
  unfold take_snoc_oracle
  unfold snoc_oracle
  simp

section SecurityRelations

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_proof_irrel (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (k : ℕ) (h h' : k + ϑ ≤ i) :
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i challenges k h =
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i challenges k h' := by
  funext cId
  unfold Compatibility.newestFirstFoldingChallenges getFoldingChallenges
  congr 1

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q] h_Fq_char_prime hF₂ [Algebra 𝔽q L]
  β hβ_lin_indep h_β₀_eq_1 [NeZero 𝓡] [NeZero ϑ] h_ℓ_add_R_rate 𝓑 in
/-- Splitting the full final-round fold-order challenge vector at the last oracle block recovers
the prefix challenge slice followed by the final block challenge slice. -/
lemma getFoldingChallenges_append_finalBlock
    (challenges : Fin (Fin.last ℓ) → L) :
    Fin.append
      (Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega))
      (Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
        (i := Fin.last ℓ) challenges (ℓ - ϑ) (h := by
          simp only [Fin.val_last]
          have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
          omega)) =
    fun cIdx : Fin ((ℓ - ϑ) + ϑ) =>
      foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges
        ⟨cIdx.val, by
          simp only [Fin.val_last]
          have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
          omega⟩ := by
  funext cIdx
  by_cases h : cIdx.val < ℓ - ϑ
  · have hcIdx : cIdx = Fin.castAdd ϑ ⟨cIdx.val, h⟩ := by
      apply Fin.ext
      simp
    rw [hcIdx, Fin.append_left]
    dsimp only [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges]
    congr 1
    apply Fin.ext
    simp
  · have h_le : ℓ - ϑ ≤ cIdx.val := Nat.le_of_not_gt h
    let j : Fin ϑ := ⟨cIdx.val - (ℓ - ϑ), by
      have hϑ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
      omega⟩
    have hcIdx : cIdx = Fin.natAdd (ℓ - ϑ) j := by
      apply Fin.ext
      simp only [j, Fin.val_natAdd]
      omega
    rw [hcIdx, Fin.append_right]
    dsimp only [Compatibility.newestFirstFoldingChallenges, getFoldingChallenges]
    congr 1

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_tail_castSucc_eq_of_le (i : Fin ℓ)
    (challenges : Fin i.succ → L) (k : ℕ)
    (h_old : k + ϑ ≤ ↑i.castSucc) (h_new : k + ϑ ≤ ↑i.succ) :
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (Fin.tail challenges) k (h := h_old) =
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.succ
      challenges k (h := h_new) := by
  unfold Compatibility.newestFirstFoldingChallenges getFoldingChallenges
  funext cId
  let idxOld : Fin i.castSucc := ⟨k + cId.val, by
    have hc : cId.val < ϑ := cId.isLt
    have h_old' : k + ϑ ≤ i.val := by
      simpa only [Fin.val_castSucc] using h_old
    omega⟩
  let idxNew : Fin i.succ := ⟨k + cId.val, by
    have hc : cId.val < ϑ := cId.isLt
    have h_new' : k + ϑ ≤ i.val + 1 := by
      simpa only [Fin.val_succ] using h_new
    omega⟩
  change foldOrderChallenges (ℓ := ℓ) (Fin.tail challenges) idxOld =
    foldOrderChallenges (ℓ := ℓ) challenges idxNew
  have hidx : idxNew = idxOld.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  unfold foldOrderChallenges
  have hrev : idxOld.castSucc.rev = idxOld.rev.succ := Fin.rev_castSucc idxOld
  exact (show Fin.tail challenges idxOld.rev = challenges idxOld.rev.succ from rfl).trans
    (congrArg challenges hrev).symm

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_older_castSucc_eq (i : Fin ℓ)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
    (h_old : ↑j * ϑ + ϑ ≤ ↑i.castSucc)
    (h_new : ↑j * ϑ + ϑ ≤ ↑i.succ) :
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) (↑j * ϑ)
      (h := h_old) =
  Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
      (h := h_new) := by
  rw [olderStmtChallenges_succ_castSucc]
  unfold Compatibility.newestFirstFoldingChallenges getFoldingChallenges
  funext cId
  have hle : j.val * ϑ + ϑ ≤ i.val := by
    simpa only [Fin.val_castSucc] using h_old
  let idxOld : Fin i.castSucc := ⟨j.val * ϑ + cId.val, by omega⟩
  let idxNew : Fin i.succ := ⟨j.val * ϑ + cId.val, by
    simp only [Fin.val_succ]
    omega⟩
  change foldOrderChallenges (ℓ := ℓ) (Fin.tail challenges) idxOld =
    foldOrderChallenges (ℓ := ℓ) challenges idxNew
  have hidx : idxNew = idxOld.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  unfold foldOrderChallenges
  have hrev : idxOld.castSucc.rev = idxOld.rev.succ := Fin.rev_castSucc idxOld
  exact (show Fin.tail challenges idxOld.rev = challenges idxOld.rev.succ from rfl).trans
    (congrArg challenges hrev).symm

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_tail_castSucc_eq (i : Fin ℓ)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
    (h_old : ↑j * ϑ + ϑ ≤ ↑i.castSucc)
    (h_new : ↑j * ϑ + ϑ ≤ ↑i.succ) :
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc
      (Fin.tail challenges) (↑j * ϑ) (h := h_old) =
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
      (h := h_new) := by
  rw [← olderStmtChallenges_succ_castSucc (i := i) (challenges := challenges)]
  exact getFoldingChallenges_older_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
    i j challenges h_old h_new

/-- Folding consistency for round i (where i is the oracleIdx) -/
def oracleFoldingConsistencyProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  (∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i),
    have h_k_bound := oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j)
    have h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := j)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩) (steps := ϑ)
      (destIdx := destIdx) (by rfl) (by
        dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f_i := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (f_i_plus_steps := getNextOracle 𝔽q β i oStmt j hj (destDomainIdx := destIdx)
        (h_destDomainIdx := by rfl))
      (challenges := Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges (k := j.val * ϑ)
        (h := h_k_next_le_i)))

omit [CharP L 2] in
lemma oracleFoldingConsistencyProp_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    oracleFoldingConsistencyProp 𝔽q β i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) oStmt ↔
    oracleFoldingConsistencyProp 𝔽q β i.succ challenges
      (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc =
      toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  constructor
  · intro h j hj
    let j' : Fin (toOutCodewordsCount ℓ ϑ i.castSucc) := ⟨j.val, by
      rw [h_oracle_size_eq]
      exact j.isLt⟩
    have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
      rw [h_oracle_size_eq]
      exact hj
    have h' := h j' hj'
    simp only [olderStmtChallenges_succ_castSucc] at h'
    have h_next_old :=
      oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j') (hj := hj')
    have h_next_new : ↑j' * ϑ + ϑ ≤ ↑i.succ := by
      exact Nat.le_trans h_next_old (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    rw [getFoldingChallenges_tail_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := i) (j := j') (challenges := challenges)
      (h_old := h_next_old) (h_new := h_next_new)] at h'
    simpa [oracleFoldingConsistencyProp, mapOStmtOutRelayStep, getNextOracle, j',
      h_oracle_size_eq, getFoldingChallenges_older_castSucc_eq,
      getFoldingChallenges_tail_castSucc_eq, getFoldingChallenges_proof_irrel] using h'
  · intro h j hj
    let j' : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by
      rw [← h_oracle_size_eq]
      exact j.isLt⟩
    have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
      change j.val + 1 < toOutCodewordsCount ℓ ϑ i.succ
      rw [← h_oracle_size_eq]
      exact hj
    have h' := h j' hj'
    have h_next_old :=
      oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j) (hj := hj)
    have h_next_new : ↑j * ϑ + ϑ ≤ ↑i.succ := by
      exact Nat.le_trans h_next_old (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
    simp only [j'] at h'
    rw [← getFoldingChallenges_tail_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := i) (j := j) (challenges := challenges)
      (h_old := h_next_old) (h_new := h_next_new)] at h'
    simpa [oracleFoldingConsistencyProp, mapOStmtOutRelayStep, getNextOracle, j',
      h_oracle_size_eq, olderStmtChallenges_succ_castSucc,
      getFoldingChallenges_older_castSucc_eq, getFoldingChallenges_tail_castSucc_eq,
      getFoldingChallenges_proof_irrel] using h'

def BBF_eq_multiplier (r : Fin ℓ → L) : MultilinearPoly L ℓ :=
  ⟨MvPolynomial.eqPolynomial r, by simp only [eqPolynomial_mem_restrictDegree]⟩

def BBF_SumcheckMultiplierParam : SumcheckMultiplierParam L ℓ (SumcheckBaseContext L ℓ) :=
  { multpoly := fun ctx => BBF_eq_multiplier ctx.t_eval_point
    -- Binary Basefold is the plain degree-2 case `H = P · t`: combinator `Q := X`, degree 1.
    combinator := fun _ => Polynomial.X
    degCombinator := 1
    combinator_natDegree_le := by intro _; exact Polynomial.natDegree_X_le }

namespace Compatibility

/-- Historical witness encoding: reversed Boolean variables and newest-first challenges.
The folding computation itself uses canonical `iteratedFold`. -/
def newestFirstCodeword {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ])
    (challenges : Fin i → L) : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ → L :=
  let P₀ : L⦃< 2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
  iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := i.val) (destIdx := ⟨i, by omega⟩)
    (h_destIdx := by simp only [Fin.val_zero, zero_add])
    (h_destIdx_le := by simp only; omega)
    (f := fun x => P₀.val.eval x.val)
    (r_challenges := foldOrderChallenges (ℓ := ℓ) challenges)

/-- The canonical fold primitive preserves the original historical encoding exactly. -/
theorem newestFirstCodeword_eq_legacy {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ])
    (challenges : Fin i → L) :
    newestFirstCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t challenges =
      let P₀ : L⦃< 2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := 0) (steps := i.val) (destIdx := ⟨i, by omega⟩)
        (h_destIdx := by simp only [Fin.val_zero, zero_add])
        (h_destIdx_le := by simp only; omega)
        (f := fun x => P₀.val.eval x.val)
        (r_challenges := foldOrderChallenges (ℓ := ℓ) challenges) := by
  simp only [newestFirstCodeword, iterated_fold_eq_canonical]

end Compatibility

section SumcheckContextIncluded_Relations
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

/-- This condition ensures that the witness polynomial `H` has the
correct structure `eq(...) * t(...)` -/
def witnessStructuralInvariant {i : Fin (ℓ + 1)} (stmt : Statement (L := L) Context i)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  wit.H = projectToMidSumcheckPoly ℓ wit.t (m:=mp.multpoly stmt.ctx) i stmt.challenges ∧
  wit.f = Compatibility.newestFirstCodeword 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t stmt.challenges

/-- Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean
hypercube of dimension `k` (embedded via `𝓑`). This is the protocol-level `(𝓑)` form consumed
throughout BinaryBasefold (Relations, ReductionLogic, Steps/*). -/
def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : MultiquadraticPoly L k) : Prop :=
  sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ k, H.val.eval x

/-- First oracle witness consistency: the witness polynomial t, when projected to level 0 and
    evaluated on the initial domain S^(0), must be close within unique decoding radius to f^(0) -/
def firstOracleWitnessConsistencyProp (t : MultilinearPoly L ℓ)
    (f₀ : sDomain 𝔽q β h_ℓ_add_R_rate 0 → L) : Prop :=
  let P₀ : L⦃< 2 ^ ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
  -- The constraint: P_0 evaluated on S^(0) is close within unique decoding radius to f^(0)
  -- API migration: `BBF_CodeDistance` now lives in `Code.lean` keyed on `𝔽q β (h_ℓ_add_R_rate)`
  -- and a `Fin r` index (no explicit `ℓ 𝓡`).
  2 * hammingDist (fun x => P₀.val.eval x.val) f₀ <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩

/-- The bad folding event of `fᵢ` exists RIGHT AFTER the V's challenge of sumcheck round `i+ϑ-1`,
this is the last point that `fᵢ` is the last oracle being sent so far and both
Statement & Witness are advanced to state `i+ϑ`, while oracle is still at state `i+ϑ-1`.
-/
noncomputable def foldingBadEventAtBlock
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx)) : Prop :=
  have h_ϑ: ϑ > 0 := by exact pos_of_neZero ϑ
  if hj: j.val * ϑ + ϑ ≤ stmtIdx then
    let f_k := oStmt j
    Binius.BinaryBasefold.foldingBadEvent (i := ⟨j.val * ϑ, by omega⟩) (steps := ϑ)
      (destIdx := ⟨j.val * ϑ + ϑ, by omega⟩)
      (h_destIdx := by rfl) (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
      (f_i := f_k) (r_challenges :=
        Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) stmtIdx challenges (k := j.val * ϑ) (h := hj))
  else True

attribute [irreducible] foldingBadEventAtBlock

open Classical in
def badEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
    (oStmt := oStmt) (challenges := challenges) j

/-- When `stmtIdx.val < ℓ`, the highest available oracle block `j = stmtIdx/ϑ` has
`j*ϑ + ϑ > stmtIdx`, so its per-block bad-folding guard fails and `foldingBadEventAtBlock`
returns `True`. Hence `badEventExistsProp` (an existential over blocks) holds unconditionally:
the most-recently-sent oracle has not yet been folded past the current statement index, so the
"bad event" disjunct is vacuously available. This is the structural reason a relay/fold round in
the interior of the protocol is always non-doomed via the bad-event branch. -/
lemma badEventExistsProp_of_lt (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (challenges : Fin stmtIdx → L) (h_lt : stmtIdx.val < ℓ) (h_eq : oracleIdx.val = stmtIdx.val) :
    badEventExistsProp 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      (oStmt := oStmt) (challenges := challenges) := by
  have hϑ : 0 < ϑ := pos_of_neZero ϑ
  refine ⟨⟨stmtIdx.val / ϑ, ?_⟩, ?_⟩
  · -- `stmtIdx/ϑ < toOutCodewordsCount oracleIdx`
    unfold toOutCodewordsCount
    rw [h_eq]
    simp only [h_lt, ↓reduceIte]; omega
  · unfold foldingBadEventAtBlock
    split
    · -- guard holds: `stmtIdx/ϑ * ϑ + ϑ ≤ stmtIdx` is impossible since `stmtIdx/ϑ*ϑ > stmtIdx - ϑ`
      rename_i hj
      exfalso
      have hdm := Nat.div_add_mod stmtIdx.val ϑ
      have hm := Nat.mod_lt stmtIdx.val hϑ
      rw [Nat.mul_comm] at hdm
      simp only [Fin.val_mk] at hj
      omega
    · trivial

-- then simplify the top-level def to use the helper
def nonDoomedFoldingProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    : Prop :=
  let oracleFoldingConsistency := oracleFoldingConsistencyProp 𝔽q β i (challenges := challenges)
    (oStmt := oStmt)
  let foldingBadEventExists := badEventExistsProp 𝔽q β i (challenges := challenges)
    (oStmt := oStmt)
  oracleFoldingConsistency ∨ foldingBadEventExists

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero 𝓡] in
lemma firstOracleWitnessConsistencyProp_relay_preserved (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) (wit : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    firstOracleWitnessConsistencyProp 𝔽q β wit.t (getFirstOracle 𝔽q β oStmt) =
    firstOracleWitnessConsistencyProp 𝔽q β wit.t
      (getFirstOracle 𝔽q β (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt)) := by congr

-- STATEMENT REPAIR (2026-06-04): added hypothesis `h_not_last : i.val + 1 < ℓ`.
-- Reason: the original `↔` is FALSE at the last relay round (`i.val + 1 = ℓ`). There the LHS
-- (`nonDoomedFoldingProp` at `i.castSucc`, with `i.castSucc.val = i.val < ℓ`) is UNCONDITIONALLY
-- True via the bad-event disjunct (`badEventExistsProp_of_lt`: the top oracle block's folding guard
-- fails, yielding `True`), but the RHS at `i.succ = Fin.last ℓ` has count `ℓ/ϑ` with NO top "+1"
-- block, so every block's guard `j*ϑ+ϑ ≤ ℓ` HOLDS and `badEventExistsProp` becomes a genuine
-- existential over real `foldingBadEvent`s while `oracleFoldingConsistency` is a genuine oracle
-- constraint — neither is unconditionally True, so `True ↔ RHS` does not hold in general. With
-- `i.val + 1 < ℓ` both indices are `< ℓ`, both sides are unconditionally True via the bad-event
-- branch, and the lemma is sound. The lemma has zero live users (only the sibling
-- `oracleWitnessConsistency_relay_preserved`, which does not use the bad-event disjunction, is
-- consumed in `Steps.lean`), so tightening the hypothesis is safe.
lemma nonDoomedFoldingProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (h_not_last : i.val + 1 < ℓ)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    :
    nonDoomedFoldingProp 𝔽q β i.castSucc
      (olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges) oStmt ↔
    nonDoomedFoldingProp 𝔽q β i.succ challenges (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  -- Both sides reduce to `True` via their bad-event disjunct, since both statement indices are
  -- `< ℓ`.
  constructor
  · intro _
    refine Or.inr ?_
    exact badEventExistsProp_of_lt 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
      (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) (challenges := challenges)
      (h_lt := by simp only [Fin.val_succ]; omega) (h_eq := rfl)
  · intro _
    refine Or.inr ?_
    exact badEventExistsProp_of_lt 𝔽q β (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
      (oStmt := oStmt)
      (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ)
        (oracleIdx := i.castSucc)
        (by simp only [Fin.val_succ, Fin.val_castSucc]; omega) challenges)
      (h_lt := by simp only [Fin.coe_castSucc]; omega) (h_eq := rfl)

def oracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : Fin (ℓ + 1))
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  ϑ (i := oracleIdx) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (mp := mp) (i:=stmtIdx) 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑)
    stmt.sumcheck_target wit.H
  let firstOracleConsistency: Prop := firstOracleWitnessConsistencyProp 𝔽q β
    wit.t (getFirstOracle 𝔽q β oStmt)
  let oracleFoldingConsistency: Prop := oracleFoldingConsistencyProp 𝔽q β oracleIdx
    (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      h_le stmt.challenges)
    (oStmt := oStmt)
  witnessStructuralInvariant ∧ sumCheckConsistency ∧ firstOracleConsistency ∧
    oracleFoldingConsistency

omit [CharP L 2] in
lemma oracleWitnessConsistency_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmt : Statement (L := L) Context i.succ)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β i.succ i.castSucc
      (le_succ ↑i.castSucc) stmt wit oStmt =
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β i.succ i.succ (by rfl) stmt wit
      (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  unfold oracleWitnessConsistency
  simp only
  -- conjuncts 1,2 (witnessStructuralInvariant, sumCheckConsistency) are identical;
  -- conjunct 3 (firstOracleConsistency) equal by the relay-preservation of the first oracle;
  -- conjunct 4 (oracleFoldingConsistency) equal by oracle/challenge reindexing.
  congr 1
  · -- sumcheckConsistency (identical) ∧ firstOracleConsistency ∧ oracleFoldingConsistency
    rw [firstOracleWitnessConsistencyProp_relay_preserved 𝔽q β i hNCR wit oStmt]
    -- now the two `firstOracle…` conjuncts are syntactically identical; isolate the folding props.
    congr 1  -- peel sumcheckConsistency (rfl)
    congr 1  -- peel firstOracleConsistency (now rfl)
    simpa [olderStmtChallenges_self] using
      propext (oracleFoldingConsistencyProp_relay_preserved 𝔽q β i hNCR
        stmt.challenges oStmt)

-- Per-block relay preservation: `foldingBadEventAtBlock` depends on the oracle index only through
-- `oStmt j` (its `f_i` input). The RHS block index is `Fin.cast h_size j`, so `j.val` is preserved
-- (`Fin.cast` is the identity on values) and `mapOStmtOutRelayStep … oStmt (Fin.cast h_size j)`
-- definitionally reduces to `oStmt j`. Hence the block predicate is literally the same on both
-- sides — no rewriting of the dependent `f_i` is needed. We unseal the irreducible block def. -/
unseal foldingBadEventAtBlock in
lemma foldingBadEventAtBlock_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (h_size : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) :
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (oStmt := oStmt) (challenges := challenges) j =
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
        (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) (challenges := challenges)
        (Fin.cast h_size j) :=
  rfl

/-- The relay step's oracle relabeling preserves the bad-event existential, when both sides are
evaluated against the *same* statement index `i.succ`. Both sides quantify the same per-block
folding guard `j*ϑ + ϑ ≤ i.succ` over equal block counts (`hNCR ⇒ count i.castSucc = count i.succ`)
on the identical oracle data (`mapOStmtOutRelayStep` is a pure reindex along that size equality),
so the existentials coincide. This is the bad-event analogue of
`oracleWitnessConsistency_relay_preserved`, and is what makes `foldStepRelOut` (with its repaired
`stmtIdx := i.succ` bad event) equal to its relay image `roundRelation i.succ` at *every* round,
including the last (`i.val + 1 = ℓ`). -/
lemma badEventExistsProp_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (challenges := challenges) (oStmt := oStmt) =
    badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.succ)
        (challenges := challenges) (oStmt := mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  have h_size : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  apply propext
  unfold badEventExistsProp
  -- reindex the existential block along the size equality `h_size`; the predicate is literally
  -- preserved by `foldingBadEventAtBlock_relay_preserved`.
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨Fin.cast h_size j,
      (foldingBadEventAtBlock_relay_preserved 𝔽q β i hNCR h_size challenges oStmt j) ▸ hj⟩
  · rintro ⟨j', hj⟩
    refine ⟨Fin.cast h_size.symm j', ?_⟩
    rw [foldingBadEventAtBlock_relay_preserved 𝔽q β i hNCR h_size challenges oStmt
      (Fin.cast h_size.symm j')]
    simpa using hj

/-- Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event
of the `i-th` oracle if any and enable it after the next V's challenge, i.e. one
round later. This is for the purpose of reasoning its RBR KS properly.
Formally, = (oracleIdx = stmtIdx)`.
-/
def masterKStateCore (stmtIdx : Fin (ℓ + 1))
    (oracleIdx : Fin (ℓ + 1))
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j)) :
    Prop :=
  let oracleWitnessConsistency: Prop := oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β
    stmtIdx oracleIdx h_le stmt wit oStmt
  let badEventExists := badEventExistsProp (ϑ := ϑ) 𝔽q β oracleIdx
    (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
      h_le stmt.challenges)
    (oStmt := oStmt)
  badEventExists ∨ oracleWitnessConsistency

def masterKStateProp (stmtIdx : Fin (ℓ + 1))
    (oracleIdx : Fin (ℓ + 1))
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx) j))
    (localChecks : Prop) : Prop :=
  localChecks ∧ masterKStateCore (mp := mp) (𝓑 := 𝓑) 𝔽q β
    (stmtIdx := stmtIdx) (oracleIdx := oracleIdx) (h_le := h_le) stmt wit oStmt

def roundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  masterKStateCore (mp := mp) (𝓑 := 𝓑) 𝔽q β
    (stmtIdx := i) (oracleIdx := i) (h_le := le_refl i) stmt wit oStmt

open Classical in
/-- A modified version of roundRelationProp (i+1).

STATEMENT REPAIR (2026-06-04): at *non-commitment* rounds the bad-event disjunct is evaluated at
the statement index `i.succ` (the relay-step / `roundRelation i.succ` form) rather than at the
oracle index `i.castSucc`.

Why a per-round branch. `foldStepRelOut i` is the relOut of the fold step and the relIn of whichever
single step consumes round `i` — the *commit* step when `isCommitmentRound ℓ ϑ i`, the *relay* step
otherwise (the two are mutually exclusive). These two consumers need *different* forms:

* Commit rounds (`ϑ ∣ i+1 ∧ i+1 ≠ ℓ`): `commitKState.toFun_empty` is `rfl` against
  `commitKStateProp 0 = masterKStateProp (stmtIdx := i.succ) (oracleIdx := i.castSucc)`, i.e. the
  bad event at `stmtIdx := oracleIdx := i.castSucc` (the "ignore the latest oracle's bad event one
  step behind" design). The commit step *changes* the oracle count, so the relay relabel does not
  apply; this weak form is the intended one.

* Non-commitment rounds (`¬ isCommitmentRound`, includes the last round `i+1 = ℓ`): the relay step
  is a 0-round protocol, so `relayKnowledgeStateFunction.toFun_empty` demands
  `relIn ↔ toFun 0 = relayKStateProp = roundRelation i.succ` (its relOut). With the weak form this
  `↔` is FALSE at the last round (`i+1 = ℓ`): the relIn bad event at `stmtIdx := i.castSucc`
  (guard `j*ϑ+ϑ ≤ i`) is vacuously `True` via the top block, but `roundRelation i.succ` evaluates
  the bad event at `stmtIdx := oracleIdx := i.succ` (guard `j*ϑ+ϑ ≤ ℓ`, satisfied by that top block)
  — a *genuine* existential. So `True ↔ (genuine bad event ∨ owc)` fails. Evaluating the relIn bad
  event at the *statement* index `i.succ` instead makes it coincide with the relay image of
  `roundRelation i.succ` at *every* non-commitment round, including the boundary — the oracle data
  agrees up to the relay relabel (`hNCR ⇒ count i.castSucc = count i.succ`); see
  `badEventExistsProp_relay_preserved` / `foldStepRelOut_relay_eq_roundRelation`.

The owc disjunct is unchanged (`oracleWitnessConsistency (stmtIdx := i.succ) (oracleIdx :=
i.castSucc)`), matching both consumers via `oracleWitnessConsistency_relay_preserved`. Only
`foldStepRelOut` (confined to `Basic.lean` + `Steps.lean`) is affected; the fold-step theorems that
mention it are by-name and their proofs are research-tier `sorry` stubs, so no proven content
regresses, and the commit path keeps its weak form. -/
def foldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let oracleWitnessConsistency : Prop :=
    oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β
      (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (h_le := Nat.le_of_lt (Fin.castSucc_lt_succ)) stmt wit oStmt
  let badEventExists : Prop :=
    if isCommitmentRound ℓ ϑ i then
      -- commit-round (weak) form: bad event at `stmtIdx := oracleIdx := i.castSucc`
      badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.castSucc) (oracleIdx := i.castSucc)
        (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := i.succ)
          (oracleIdx := i.castSucc)
          (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega) stmt.challenges)
        (oStmt := oStmt)
    else
      -- non-commitment (relay) form: bad event at the statement index `i.succ`
      badEventExistsProp (ϑ := ϑ) 𝔽q β (stmtIdx := i.succ) (oracleIdx := i.castSucc)
        (challenges := stmt.challenges) (oStmt := oStmt)
  badEventExists ∨ oracleWitnessConsistency

/-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
the consistency between the last oracle `ℓ - ϑ` and the final constant `c` -/
def finalNonDoomedFoldingProp {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  let f_ℓ: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨ℓ, by omega⟩ → L := fun x => stmt.finalConstant
  let j := mkLastOracleIndex ℓ ϑ (Fin.last ℓ) -- actually `j = ℓ / ϑ - 1`
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [mkLastOracleIndex_last]
    change (ℓ / ϑ - 1) * ϑ = ℓ - ϑ
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k := oStmt j
  have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
  let challenges : Fin ϑ → L :=
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := Fin.last ℓ) stmt.challenges (k := k)
      (h := by simp only [h_k_add_ϑ, Fin.val_last, le_refl])
  let finalOracleFoldingConsistency: Prop := by
    -- folding consistency between two adjacent oracles `j` & `j + ϑ`
    exact isCompliant (i := ⟨k, by rw [h_k]; omega⟩) (steps := ϑ)
      (destIdx := ⟨ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_mk]; omega)
      (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega) (f_i := f_k)
      (f_i_plus_steps := by simpa only [h_k_add_ϑ] using f_ℓ) (challenges := challenges)

  -- If oracleFoldingConsistency is true, then we can extract the original
    -- well-formed poly `t` and derive witnesses that satisfy the relations at any state
  let oracleFoldingConsistency: Prop :=
    (oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt))
    ∧ finalOracleFoldingConsistency

  let finalFoldingBadEvent : Prop :=
    Binius.BinaryBasefold.foldingBadEvent (i := ⟨k, by rw [h_k]; omega⟩)
      (steps := ϑ) (destIdx := ⟨ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_mk]; omega)
      (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega) (f_i := f_k)
      (r_challenges := challenges)

  -- All bad folding events are fully formed across the sum-check rounds,
    -- no new bad event at the final sumcheck step
  let foldingBadEventExists : Prop := badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
    (oStmt := oStmt) (challenges := stmt.challenges)

  oracleFoldingConsistency ∨ foldingBadEventExists

/-- Relation for final sumcheck step -/
def finalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  -- Final oracle consistency and bad events
  finalNonDoomedFoldingProp 𝔽q β
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)

end SumcheckContextIncluded_Relations
end SecurityRelations
end OracleReductionComponents

end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.getFoldingChallenges_tail_castSucc_eq
#print axioms Binius.BinaryBasefold.getFoldingChallenges_append_finalBlock
#print axioms Binius.BinaryBasefold.mkLastOracleIndex_eq_getLastOraclePositionIndex
#print axioms Binius.BinaryBasefold.snoc_oracle_new_heq_of_commit
#print axioms Binius.BinaryBasefold.take_snoc_oracle_eq_oStmtIn
#print axioms Binius.BinaryBasefold.oracleFoldingConsistencyProp_relay_preserved
#print axioms Binius.BinaryBasefold.badEventExistsProp_relay_preserved

#print axioms Binius.BinaryBasefold.Compatibility.newestFirstCodeword_eq_legacy
