/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.BitsOfIndex
import ArkLib.Data.Fin.Tuple.TakeDrop

/-! ## Binary Basefold relations and bad-event layer -/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
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
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section SecurityRelations
-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
-- The historical witness encoding is explicit in `Compatibility.newestFirstCodeword`.
section FoldStepLogic
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

-- API MIGRATION (issue #32 handoff (b)): the stale CompBinius-blob round-message type
-- `FoldMessage L` (with its `FoldMessage.eval`) is the degree-`≤ 2` sumcheck round univariate
-- on this branch — exactly the first message type of `pSpecFold = ⟨…, ![L⦃≤ 2⦄[X], L]⟩`. So
-- `FoldMessage L ↦ ↥L⦃≤ 2⦄[X]` and `FoldMessage.eval msg x ↦ msg.val.eval x`. The fold-step
-- prover/verifier kernels below are stated against that branch surface so that their downstream
-- consumers (`ReductionLogic.foldStepLogic`, `Steps/Fold.lean`) resolve.
def foldPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc ×
      (↥L⦃≤ 2⦄[X])
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc ×
      (↥L⦃≤ 2⦄[X]) × L

end FoldStepLogic

section SumcheckContextIncluded_Relations
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.

/-- Coefficient extraction of `polynomialFromNovelCoeffs` is exactly
`novelToMonomialCoeffs`. -/
lemma coeff_polynomialFromNovelCoeffs (m : ℕ) (h : m ≤ r) (a : Fin (2 ^ m) → L)
    (i : Fin (2 ^ m)) :
    (polynomialFromNovelCoeffs 𝔽q β m h a).coeff i.val =
      novelToMonomialCoeffs 𝔽q β m h a i := by
  unfold polynomialFromNovelCoeffs novelToMonomialCoeffs
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul]
  simp [Matrix.vecMul, dotProduct, changeOfBasisMatrix, toCoeffsVec, basisVectors]

/-- The novel coefficients recovered from the monomial coefficients of
`polynomialFromNovelCoeffs a` are `a` itself. -/
lemma monomialToNovelCoeffs_coeff_polynomialFromNovelCoeffs (m : ℕ) (h : m ≤ r)
    (a : Fin (2 ^ m) → L) :
    monomialToNovelCoeffs 𝔽q β m h
      (fun i => (polynomialFromNovelCoeffs 𝔽q β m h a).coeff i.val) = a := by
  have hc : (fun i : Fin (2 ^ m) =>
      (polynomialFromNovelCoeffs 𝔽q β m h a).coeff i.val) =
      novelToMonomialCoeffs 𝔽q β m h a := by
    funext i
    exact coeff_polynomialFromNovelCoeffs 𝔽q β m h a i
  rw [hc]
  exact novelToMonomial_monomialToNovel_inverse 𝔽q β m h a

lemma polynomialFromNovelCoeffsF₂_injective (m : ℕ) (h : m ≤ r) :
    Function.Injective (polynomialFromNovelCoeffsF₂ (L := L) 𝔽q β m h) := by
  intro a b hab
  funext i
  have hcoeffs := congrArg
    (fun P : L⦃<2 ^ m⦄[X] =>
      monomialToNovelCoeffs 𝔽q β m h (fun j => P.val.coeff j.val)) hab
  have ha := monomialToNovelCoeffs_coeff_polynomialFromNovelCoeffs
    (L := L) 𝔽q β m h a
  have hb := monomialToNovelCoeffs_coeff_polynomialFromNovelCoeffs
    (L := L) 𝔽q β m h b
  have hcoeffs' : a = b := by
    simpa [polynomialFromNovelCoeffsF₂, ha, hb] using hcoeffs
  exact congrFun hcoeffs' i

lemma firstOracleWitnessConsistencyProp_unique (t₁ t₂ : MultilinearPoly L ℓ)
    (f₀ : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁ f₀)
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₂ f₀) :
    t₁ = t₂ := by
  classical
  let c₁ : Fin (2 ^ ℓ) → L :=
    fun ω => t₁.val.eval (statementOrderBitsOfIndex (L := L) ω)
  let c₂ : Fin (2 ^ ℓ) → L :=
    fun ω => t₂.val.eval (statementOrderBitsOfIndex (L := L) ω)
  let P₁ : L⦃<2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) c₁
  let P₂ : L⦃<2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) c₂
  let g₁ : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L := fun x => P₁.val.eval x.val
  let g₂ : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L := fun x => P₂.val.eval x.val
  let C₀ : Set (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)
  have h₁' : 2 * hammingDist g₁ f₀ <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
    simpa [firstOracleWitnessConsistencyProp, c₁, P₁, g₁] using h₁
  have h₂' : 2 * hammingDist g₂ f₀ <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
    simpa [firstOracleWitnessConsistencyProp, c₂, P₂, g₂] using h₂
  have hg₁_mem : g₁ ∈ C₀ := by
    change polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := (0 : Fin r)) (P := P₁) ∈ C₀
    exact (getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (P := P₁)).property
  have hg₂_mem : g₂ ∈ C₀ := by
    change polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := (0 : Fin r)) (P := P₂) ∈ C₀
    exact (getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by simp) (P := P₂)).property
  have hg_dist_lt :
      hammingDist g₁ g₂ <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
    have htri : hammingDist g₁ g₂ ≤ hammingDist g₁ f₀ + hammingDist f₀ g₂ :=
      hammingDist_triangle g₁ f₀ g₂
    rw [hammingDist_comm g₂ f₀] at h₂'
    omega
  have hg_eq : g₁ = g₂ :=
    Code.eq_of_lt_dist (C := C₀) hg₁_mem hg₂_mem hg_dist_lt
  have hP_eq : P₁ = P₂ := by
    apply Subtype.ext
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (f := fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => (x.val : L))
      (hf := fun x y hxy => Subtype.ext hxy)
    · intro x
      exact congrFun hg_eq x
    · have hP₁deg : P₁.val.natDegree < 2 ^ ℓ :=
        natDegree_of_mem_degreeLT (L := L) (hn := Nat.two_pow_pos ℓ) P₁.property
      have hP₂deg : P₂.val.natDegree < 2 ^ ℓ :=
        natDegree_of_mem_degreeLT (L := L) (hn := Nat.two_pow_pos ℓ) P₂.property
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
        (h_i := by
          show ((0 : Fin r) : ℕ) < ℓ + 𝓡
          exact Nat.lt_add_right 𝓡 (Nat.pos_of_neZero ℓ)), hF₂.out]
      exact lt_of_lt_of_le (max_lt hP₁deg hP₂deg)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right ℓ 𝓡))
  have hc_eq : c₁ = c₂ :=
    polynomialFromNovelCoeffsF₂_injective (L := L) 𝔽q β ℓ (by omega) hP_eq
  apply Subtype.ext
  apply (MvPolynomial.is_multilinear_eq_iff_eq_evals_zeroOne
    t₁.val t₂.val t₁.property t₂.property).mpr
  funext w
  let k : Fin (2 ^ ℓ) := finFunctionFinEquiv (fun j : Fin ℓ => w (Fin.rev j))
  have hk := congrFun hc_eq k
  change t₁.val.eval (statementOrderBitsOfIndex (L := L) k) =
    t₂.val.eval (statementOrderBitsOfIndex (L := L) k) at hk
  unfold MvPolynomial.toEvalsZeroOne
  have hpoint :
      statementOrderBitsOfIndex (L := L) k = fun j : Fin ℓ => ((w j : Fin 2) : L) := by
    funext j
    simp [k, statementOrderBitsOfIndex, bitsOfIndex_eq_finFunctionFinEquiv_symm, Fin.rev_rev]
  simpa [hpoint] using hk

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
lemma foldingBadEventAtBlock_cons_castSucc_eq (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := i.castSucc) j)
    (challenges : Fin i.castSucc → L) (r_new : L)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc))
    (hj_le : j.val * ϑ + ϑ ≤ i.castSucc.val) :
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.succ)
      (oracleIdx := (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val)
      (oStmt := oStmt)
      (challenges := Fin.cons r_new challenges) j =
    foldingBadEventAtBlock 𝔽q β (stmtIdx := i.castSucc)
      (oracleIdx := (OracleFrontierIndex.mkFromStmtIdx i.castSucc).val)
      (oStmt := oStmt)
      (challenges := challenges) j := by
  unfold foldingBadEventAtBlock
  simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
    Fin.val_castSucc, OracleFrontierIndex.val_mkFromStmtIdx,
    Fin.val_succ]
  have h_guard_succ : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val + 1 := by
    simp only [Fin.val_castSucc] at ⊢ hj_le
    omega
  have h_guard_cast : oraclePositionToDomainIndex (positionIdx := j) + ϑ ≤ i.val := by
    simp only [Fin.val_castSucc] at ⊢ hj_le
    omega
  dsimp only [oraclePositionToDomainIndex] at h_guard_succ h_guard_cast
  simp only [h_guard_succ, h_guard_cast, ↓reduceDIte]
  congr 1
  unfold Compatibility.newestFirstFoldingChallenges getFoldingChallenges
  funext cId
  let idxOld : Fin i.castSucc := ⟨j.val * ϑ + cId.val, by
    have hle : j.val * ϑ + ϑ ≤ i.val := by
      simpa only [Fin.val_castSucc] using hj_le
    have hc : cId.val < ϑ := cId.isLt
    omega⟩
  let idxNew : Fin i.succ := ⟨j.val * ϑ + cId.val, by
    have hle : j.val * ϑ + ϑ ≤ i.val := by
      simpa only [Fin.val_castSucc] using hj_le
    have hc : cId.val < ϑ := cId.isLt
    simp only [Fin.val_succ]
    omega⟩
  change foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.succ)
      (Fin.cons r_new challenges) idxNew =
    foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc) challenges idxOld
  have hidx : idxNew = idxOld.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hfo := foldOrderChallenges_cons (ℓ := ℓ) (L := L) i challenges r_new
  exact (congrFun hfo idxOld.castSucc).trans
    (Fin.snoc_castSucc (n := i.val) (α := fun _ : Fin (i.val + 1) => L)
      (x := r_new) (p := foldOrderChallenges (ℓ := ℓ) (L := L) (i := i.castSucc)
        challenges) (i := idxOld))

-- `foldingBadEventAtBlock` (and its `[irreducible]` attribute) now live in `Basic.lean`.

open Classical in
def blockBadEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx.val)
    (oStmt := oStmt) (challenges := challenges) j

def incrementalBadEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val),
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
    let k : ℕ := min ϑ (stmtIdx.val - curOracleDomainIdx.val)
    have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := pos_of_neZero 𝓡
    let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]; omega⟩
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx) (k := k)
      (h_k_le := Nat.min_le_left ϑ (stmtIdx.val - curOracleDomainIdx.val))
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := rfl) (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j))
      (f_block_start := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (r_challenges := fun cId => foldOrderChallenges (ℓ := ℓ) challenges
        ⟨curOracleDomainIdx.val + cId.val, by
          have h_k_le_stmt : k ≤ stmtIdx.val - curOracleDomainIdx.val :=
            Nat.min_le_right ϑ (stmtIdx.val - curOracleDomainIdx.val)
          have h_cId_lt_k : cId.val < k := cId.isLt
          omega⟩)

def incrementalBadEventAtLast
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val)) :
    Prop :=
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) (positionIdx := j), by omega⟩
    let k : ℕ := min ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val)
    have h1 := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
      (i := (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := pos_of_neZero 𝓡
    let midIdx : Fin r := ⟨curOracleDomainIdx.val + k, by omega⟩
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
      omega⟩
    incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx) (k := k)
      (h_k_le := Nat.min_le_left ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val))
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := rfl) (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := (OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ)).val) (j := j))
      (f_block_start := by
        simpa [OracleStatement, oraclePositionToDomainIndex] using oStmt j)
      (r_challenges := fun cId => foldOrderChallenges (ℓ := ℓ) challenges
        ⟨curOracleDomainIdx.val + cId.val, by
          have h_k_le_stmt : k ≤ (Fin.last ℓ).val - curOracleDomainIdx.val :=
            Nat.min_le_right ϑ ((Fin.last ℓ).val - curOracleDomainIdx.val)
          have h_cId_lt_k : cId.val < k := cId.isLt
          omega⟩)

lemma badEventExistsProp_iff_incrementalBadEventExistsProp_last
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (challenges : Fin (Fin.last ℓ) → L) :
    blockBadEventExistsProp 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) ↔
    incrementalBadEventExistsProp 𝔽q β
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmt) (challenges := challenges) := by
  unfold blockBadEventExistsProp incrementalBadEventExistsProp
  apply exists_congr
  intro j
  unfold foldingBadEventAtBlock
  dsimp only [OracleFrontierIndex.val_mkFromStmtIdx, oraclePositionToDomainIndex]
  have h_le : j.val * ϑ + ϑ ≤ ℓ :=
    oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := j)
  have hk : min ϑ (ℓ - j.val * ϑ) = ϑ := by omega
  simp only [Fin.val_last, h_le, ↓reduceDIte, hk, incrementalFoldingBadEvent,
    NeZero.ne ϑ, ↓reduceDIte]
  rfl

/-- The bad sumcheck event, stated at the **polynomial** level.

Over `CharP L 2` with `|L| = 2`, two *distinct* degree-≤2 polynomials can share the same
evaluation function, so a function-level inequality (`h_i ≠ h_star` as maps `L → L`) is strictly
weaker than what the soundness argument produces (a polynomial inequality). We therefore state the
event on the polynomial subtype `↥L⦃≤ 2⦄[X]`, matching the polynomial inequality supplied by the
extractor (`h_hi_ne_extracted`) and the Schwartz–Zippel bound (`badPolyAgreement`). -/
def badSumcheckEventProp
    (r_i' : L) (h_i h_star : ↥L⦃≤ 2⦄[X]) :=
  h_i ≠ h_star ∧ Polynomial.eval r_i' h_i.val = Polynomial.eval r_i' h_star.val
section SingleStepRelationPreservationLemmas

section FoldStepPreservationLemmas
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

end FoldStepPreservationLemmas

section CommitStepPreservationLemmas

lemma incrementalBadEventExistsProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (challenges : Fin i.succ → L) :
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmt challenges ↔
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (mapOStmtOutRelayStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR oStmt) challenges := by
  have h_count : toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp [toOutCodewordsCount_succ_eq, hNCR]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count j, ?_⟩
    have hj' := hj
    simp only [incrementalBadEventExistsProp, mapOStmtOutRelayStep,
      OracleFrontierIndex.val_mkFromStmtIdx, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
      h_count] at hj' ⊢
    exact hj'
  · rintro ⟨j, hj⟩
    refine ⟨Fin.cast h_count.symm j, ?_⟩
    have hj' := hj
    simp only [incrementalBadEventExistsProp, mapOStmtOutRelayStep,
      OracleFrontierIndex.val_mkFromStmtIdx, OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
      h_count] at hj' ⊢
    exact hj'

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
set_option maxHeartbeats 4000000 in
lemma incrementalBadEventExistsProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (challenges : Fin i.succ → L) :
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdx i.succ)
      (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) challenges →
    incrementalBadEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
      oStmtIn challenges := by
  intro h_bad
  rcases h_bad with ⟨j, hj_bad⟩
  by_cases hj_lt : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · refine ⟨⟨j.val, hj_lt⟩, ?_⟩
    -- Both `hj_bad` and the goal are already past the `∃` head (the `rcases`/anonymous
    -- constructor exposed the bodies), so there is nothing left to unfold.
    dsimp [OracleFrontierIndex.val_mkFromStmtIdx,
      OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj_bad ⊢
    simpa [snoc_oracle, hj_lt, foldOrderChallenges, getFoldingChallenges_proof_irrel] using hj_bad
  · exfalso
    -- `hj_bad` is already past the `∃` head (see above).
    dsimp [OracleFrontierIndex.val_mkFromStmtIdx] at hj_bad
    have h_count_succ :
        toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
      simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
    have hj_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
      have hj_le : j.val ≤ toOutCodewordsCount ℓ ϑ i.castSucc := by
        -- (`.succ` vs `+ 1` and the `OracleFrontierIndex` coercion are defeq-only under
        -- rc2; restate `j.isLt` at the plain count so omega sees one atom.)
        have h1 : j.val < toOutCodewordsCount ℓ ϑ i.succ := j.isLt
        rw [h_count_succ] at h1
        omega
      have hj_ge : toOutCodewordsCount ℓ ϑ i.castSucc ≤ j.val := by
        simpa only [not_lt] using hj_lt
      omega
    have h_domain : j.val * ϑ = i.succ.val := by
      rw [hj_eq]
      exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
    have hk : min ϑ (i.succ.val - j.val * ϑ) = 0 := by
      rw [h_domain]
      simp
    simp [incrementalFoldingBadEvent, hk] at hj_bad
    exact hj_bad.1.2 (by rw [h_domain]; simp)

lemma oracleFoldingConsistencyProp_commit_step_backward (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (challenges : Fin i.succ.val → L)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩)) :
    oracleFoldingConsistencyProp 𝔽q β (i := i.succ) challenges
      (snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_destIdx := rfl)
        oStmtIn newOracle) →
    oracleFoldingConsistencyProp 𝔽q β (i := i.castSucc) (Fin.tail challenges) oStmtIn := by
  intro h j hj
  have h_count_succ :
      toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  let j' : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by
    rw [h_count_succ]
    omega⟩
  have hj' : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by
    dsimp [j']
    rw [h_count_succ]
    omega
  have h_old := h j' hj'
  have hj_lt : j'.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
    dsimp [j']
    exact j.isLt
  have hj_next_lt : j'.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    dsimp [j']
    exact hj
  -- `getNextOracle` must be opened so the `snoc_oracle` access at `j + 1` (strictly below
  -- the appended last position, by `hj_next_lt`) reduces to the original family's entry.
  have h_next_old : j.val * ϑ + ϑ ≤ i.castSucc :=
    oracle_block_k_next_le_i ℓ ϑ (i := i.castSucc) (j := j) hj
  have h_next_new : j.val * ϑ + ϑ ≤ i.succ := by
    exact Nat.le_trans h_next_old (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  have h_challenges :=
    getFoldingChallenges_tail_castSucc_eq (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := i) (j := j) (challenges := challenges) h_next_old h_next_new
  simp only [oracleFoldingConsistencyProp, getNextOracle, snoc_oracle, j', hj_lt, hj_next_lt,
    id_eq, ↓reduceDIte] at h_old ⊢
  rw [← h_challenges] at h_old
  simpa [getFoldingChallenges_proof_irrel] using h_old

end CommitStepPreservationLemmas

end SingleStepRelationPreservationLemmas
-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
def finalSumcheckStepOracleConsistencyProp {h_le : ϑ ≤ ℓ}
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
    (Fin.last ℓ) j) : Prop :=
  let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  have h_k_add_ϑ : k + ϑ = ℓ := by
    rw [h_k]
    exact Nat.sub_add_cancel h_le
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩ := by
    simpa [OracleStatement, oraclePositionToDomainIndex] using oStmtOut j
  let challenges : Fin ϑ → L :=
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
      stmtOut.challenges (k := k) (h := by simp only [h_k_add_ϑ, Fin.val_last, le_refl])
    let finalOracleFoldingConsistency: Prop := by
      exact isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩) (by rfl) (by simp only; omega) (f_i := f_k)
        (f_i_plus_steps := fun x => stmtOut.finalConstant) (challenges := challenges)
    oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (oStmt := oStmtOut)
      ∧ finalOracleFoldingConsistency

/-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
the consistency between the last oracle `ℓ - ϑ` and the final constant `c`.
This definition has form similar to masterKState where there is no localChecks.
-/
def finalSumcheckStepFoldingStateProp {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)))
  :
    Prop :=
  let stmtOut := input.1
  let oStmtOut := input.2
  let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
  let k := j.val * ϑ
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨oraclePositionToDomainIndex ℓ ϑ j, by omega⟩ := by
    simpa [OracleStatement, oraclePositionToDomainIndex] using oStmtOut j
  let challenges : Fin ϑ → L := fun cId => stmtOut.challenges ⟨k + cId, by
    simp only [Fin.val_last, k, j]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
  ⟩
  have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
  let oracleFoldingConsistency: Prop :=
    finalSumcheckStepOracleConsistencyProp 𝔽q β (h_le := h_le) (stmtOut := stmtOut)
      (oStmtOut := oStmtOut)
  let foldingBadEventExists : Prop := (blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
    (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
    (oStmt := oStmtOut) (challenges := stmtOut.challenges))
  oracleFoldingConsistency ∨ foldingBadEventExists

-- (moved to Basic.lean) declarations canonicalized in Basic: removed duplicates here.
def strictOracleFoldingConsistencyProp (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  -- API MIGRATION (issue #32 handoff (b)): the stale `CompPoly.CPolynomial` level-0 oracle
  -- (`computablePolynomialFromNovelCoeffsF₂` + `CPolynomial.eval`) is replaced by the canonical
  -- branch level-0 oracle built exactly as in `Compatibility.newestFirstCodeword` — the in-degree-bound
  -- `polynomialFromNovelCoeffsF₂` evaluated on `S⁽⁰⁾`. This keeps `f₀` definitionally the same as
  -- the historical encoding's base function and drops the (mid-refactor) CompPoly dependency here.
  let P₀ : L⦃< 2 ^ ℓ⦄[X] :=
    polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
  let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
    fun y => P₀.val.eval y.val
  ∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)),
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by
      have h_le := oracle_index_le_ℓ (i := i) (j := j); omega
    ⟩
    have h_k_next_le_i := oracle_block_k_le_i (i := i) (j := j);
      let fⱼ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
        simpa [OracleStatement, oraclePositionToDomainIndex, destIdx] using oStmt j
    let folded_func := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := j * ϑ) (destIdx := destIdx) (h_destIdx := by
        dsimp only [Fin.coe_ofNat_eq_mod, destIdx]; simp only [zero_mod, zero_add])
      (h_destIdx_le := by have h_le := oracle_index_le_ℓ (i := i) (j := j); omega)
      (f := f₀) (r_challenges := Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) i
        challenges (k := 0) (ϑ := j * ϑ) (h := by omega))
    fⱼ = folded_func

def strictOracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (i := oracleIdx.val) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (i:=stmtIdx) 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let strictOracleFoldingConsistency: Prop := strictOracleFoldingConsistencyProp 𝔽q β
    (t := wit.t) (i := oracleIdx.val)
    (challenges := olderStmtChallenges (ℓ := ℓ) (stmtIdx := stmtIdx)
      (oracleIdx := oracleIdx.val) (OracleFrontierIndex.val_le_i stmtIdx oracleIdx)
      stmt.challenges)
    (oStmt := oStmt)
  witnessStructuralInvariant ∧ strictOracleFoldingConsistency

def strictRoundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i)
    : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

def strictFoldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
    stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

def strictfinalSumcheckStepFoldingStateProp (t : MultilinearPoly L ℓ) {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  let strictOracleFoldingConsistency: Prop :=
    strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt)
  let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
  have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
  let k := lastDomainIdx.val
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, lastDomainIdx]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
  let curDomainIdx : Fin r := ⟨k, by omega⟩
  have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
    getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt)
  let finalChallenges : Fin ϑ → L :=
    Compatibility.newestFirstFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
      stmt.challenges k (h := by
        rw [h_k, Fin.val_last]
        have h_le : ϑ ≤ ℓ := by
          apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
        omega)
  let destDomainIdx : Fin r := ⟨k + ϑ, by omega⟩
  let strictFinalConstantConsistency: Prop :=
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := curDomainIdx) (steps := ϑ)
      (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega) (f := f_k)
      (r_challenges := finalChallenges) = fun x => stmt.finalConstant)
  strictOracleFoldingConsistency ∧ strictFinalConstantConsistency

def strictFinalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  ∃ (t : MultilinearPoly L ℓ), strictfinalSumcheckStepFoldingStateProp 𝔽q β (t := t)
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)

end SumcheckContextIncluded_Relations
end SecurityRelations

end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.firstOracleWitnessConsistencyProp_unique
#print axioms Binius.BinaryBasefold.foldingBadEventAtBlock_cons_castSucc_eq
#print axioms Binius.BinaryBasefold.badEventExistsProp_iff_incrementalBadEventExistsProp_last
#print axioms Binius.BinaryBasefold.incrementalBadEventExistsProp_relay_preserved
#print axioms Binius.BinaryBasefold.incrementalBadEventExistsProp_commit_step_backward
#print axioms Binius.BinaryBasefold.oracleFoldingConsistencyProp_commit_step_backward
