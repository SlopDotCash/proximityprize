/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch

/-!
# Berlekamp–Welch extraction correctness at the base level (`i = 0`)

This file proves the corrected base-level extraction statement and documents the
endianness mismatch that made the old unreversed formulation false for `ℓ ≥ 2`.

## The mismatch

`extractMLP` (Basic.lean) reconstructs the multilinear polynomial from the decoded
novel-basis coefficient vector via `Nat.binaryFinMapToNat`, which is **little-endian**:
the hypercube point `w` is sent to the coefficient index whose `j`-th bit is `w j`.
`firstOracleWitnessConsistencyProp` (Basic.lean) instead reads the coefficient at
index `ω` off the polynomial via `statementOrderBitsOfIndex ω`, whose `j`-th
coordinate is the `Fin.rev j`-th bit of `ω`.  The two conventions differ by the
bit-reversal permutation, so the polynomial extracted by `extractMLP` is the
*variable-reversed* (`revIndexMLP`) version of the polynomial whose codeword is
UDR-close to `f`.  Concretely (see `revIndexMLP_eq_self_of_residual` below), a
residual instance would force `revIndexMLP t = t` for every multilinear `t`, which
fails already for `t = MLE (w ↦ w 0)` once `ℓ ≥ 2`
(`extractMLPCorrectnessResidual_ell_eq_one`).

Additionally, the forward direction of the residual is false even modulo the
reversal: `extractMLP` runs the decoder at radius `e := Δ₀(f, C)` (the *actual*
distance of `f` from the code), so it can succeed on words far outside the unique
decoding radius (e.g. any `f` whose closest codeword is `0` at distance `> UDR`
takes the `‖f‖₀ ≤ e` early-return of `BerlekampWelch.decoder`).  The honest forward
statement therefore needs the `UDRClose` guard, which the backward direction
supplies for free.

## What is proved

* `extractMLP_zero_eq_some_revIndexMLP_iff` — the corrected two-sided
  characterization: `extractMLP 𝔽q β 0 f = some tpoly ∧ (UDR guard) ↔
  firstOracleWitnessConsistencyProp 𝔽q β (revIndexMLP tpoly) f`.
* `extractMLP_zero_eq_some_of_firstOracleWitnessConsistency` — backward direction
  (decoder completeness inside the UDR).
* `firstOracleWitnessConsistency_revIndexMLP_of_extractMLP_eq_some` — forward
  direction under the `UDRClose` guard.
* `firstOracleWitnessConsistencyProp_unique'` — the uniqueness consequence that
  `Relations.lean` actually consumes, proved without any residual instance.
* `revIndexMLP_eq_self_of_residual`, `extractMLPCorrectnessResidual_ell_eq_one` —
  the machine-checked obstructions showing the residual as stated forces `ℓ = 1`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

/-! ## Generic helpers -/

section GenericHelpers

/-- Hamming distance is invariant under precomposition with an equivalence of the
index type. -/
lemma hammingDist_comp_equiv {ι κ F : Type*} [Fintype ι] [Fintype κ] [DecidableEq F]
    (e : ι ≃ κ) (u v : κ → F) :
    hammingDist (u ∘ e) (v ∘ e) = hammingDist u v := by
  unfold hammingDist
  refine Finset.card_equiv e fun i => ?_
  simp

lemma getBit_le_one (k n : ℕ) : Nat.getBit k n ≤ 1 := by
  rcases Nat.getBit_eq_zero_or_one (k := k) (n := n) with h | h <;> omega

lemma binaryFinMapToNat_congr {n : ℕ} {m₁ m₂ : Fin n → ℕ} (h : m₁ = m₂)
    (h₁ : ∀ j, m₁ j ≤ 1) (h₂ : ∀ j, m₂ j ≤ 1) :
    Nat.binaryFinMapToNat m₁ h₁ = Nat.binaryFinMapToNat m₂ h₂ := by
  subst h; rfl

/-- `binaryFinMapToNat` inverts the bit decomposition of an index. -/
lemma binaryFinMapToNat_getBit_self {n : ℕ} (ω : Fin (2 ^ n)) :
    Nat.binaryFinMapToNat (fun j : Fin n => Nat.getBit j.val ω.val)
      (fun j => getBit_le_one j.val ω.val) = ω := by
  apply Fin.eq_of_val_eq
  apply Nat.eq_iff_eq_all_getBits.mpr
  intro k
  rw [Nat.getBit_of_binaryFinMapToNat]
  by_cases hk : k < n
  · simp [hk]
  · simp only [hk, ↓reduceDIte]
    have h := Nat.getBit_of_lt_two_pow (a := ω) (k := k)
    simp only [hk, ↓reduceIte] at h
    exact h.symm

/-- The boolean (`Fin 2`) digit vector of an index. -/
def bit2 {n : ℕ} (ω : Fin (2 ^ n)) (j : Fin n) : Fin 2 :=
  if Nat.getBit j.val ω.val = 1 then 1 else 0

lemma bit2_val {n : ℕ} (ω : Fin (2 ^ n)) (j : Fin n) :
    ((bit2 ω j : Fin 2) : ℕ) = Nat.getBit j.val ω.val := by
  unfold bit2
  rcases Nat.getBit_eq_zero_or_one (k := j.val) (n := ω.val) with h | h <;> simp [h]

lemma binaryFinMapToNat_bit2 {n : ℕ} (ω : Fin (2 ^ n))
    (hb : ∀ j : Fin n, ((bit2 ω j : Fin 2) : ℕ) ≤ 1) :
    Nat.binaryFinMapToNat (fun j : Fin n => ((bit2 ω j : Fin 2) : ℕ)) hb = ω := by
  rw [binaryFinMapToNat_congr (m₂ := fun j : Fin n => Nat.getBit j.val ω.val)
    (funext fun j => bit2_val ω j) hb (fun j => getBit_le_one j.val ω.val)]
  exact binaryFinMapToNat_getBit_self ω

/-- Case analysis on a `Fin 2` value, in field-coercion form. -/
lemma fin2_coe_eq_ite {L : Type} [Field L] (b : Fin 2) :
    ((b : Fin 2) : L) = if ((b : Fin 2) : ℕ) = 1 then (1 : L) else 0 := by
  fin_cases b <;> simp

end GenericHelpers

/-! ## Novel-basis coefficient round trips -/

section NovelRoundTrip

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]

/-- Reconstructing a low-degree polynomial from its monomial→novel converted
coefficients gives back the polynomial. -/
lemma polynomialFromNovelCoeffs_monomialToNovelCoeffs (m : ℕ) (h : m ≤ r)
    (P : L[X]) (hdeg : P.natDegree < 2 ^ m) :
    polynomialFromNovelCoeffs 𝔽q β m h
      (monomialToNovelCoeffs 𝔽q β m h (fun i => P.coeff i.val)) = P := by
  set a := monomialToNovelCoeffs 𝔽q β m h (fun i => P.coeff i.val) with ha
  have hQdeg : (polynomialFromNovelCoeffs 𝔽q β m h a).degree < (2 ^ m : ℕ) := by
    have hprop := (polynomialFromNovelCoeffsF₂ 𝔽q β m h a).property
    rw [Polynomial.mem_degreeLT] at hprop
    simpa using hprop
  apply Polynomial.ext
  intro n
  by_cases hn : n < 2 ^ m
  · have h1 := coeff_polynomialFromNovelCoeffs 𝔽q β m h a ⟨n, hn⟩
    rw [h1, ha, monomialToNovel_novelToMonomial_inverse 𝔽q β m h]
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hQdeg (by exact_mod_cast Nat.le_of_not_lt hn)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (Nat.le_of_not_lt hn))]

end NovelRoundTrip

/-! ## The reverse-variable-order multilinear polynomial and MLE bridges -/

section MLEBridge

variable {L : Type} [Field L] {ℓ : ℕ}

/-- The variable-reversal of a multilinear polynomial, as the MLE of its
`Fin.rev`-precomposed hypercube evaluations. -/
def revIndexMLP (t : MultilinearPoly L ℓ) : MultilinearPoly L ℓ :=
  ⟨MLE (fun w : Fin ℓ → Fin 2 => t.val.eval (fun j => ((w (Fin.rev j) : Fin 2) : L))),
    MLE_mem_restrictDegree _⟩

lemma revIndexMLP_eval_zeroOne (t : MultilinearPoly L ℓ) (w : Fin ℓ → Fin 2) :
    (revIndexMLP t).val.eval (fun j => ((w j : Fin 2) : L)) =
      t.val.eval (fun j => ((w (Fin.rev j) : Fin 2) : L)) := by
  unfold revIndexMLP
  exact MLE_eval_zeroOne w _

lemma revIndexMLP_involutive (t : MultilinearPoly L ℓ) :
    revIndexMLP (revIndexMLP t) = t := by
  apply Subtype.ext
  have hmle : MLE t.val.toEvalsZeroOne = t.val :=
    MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t.property
  calc (revIndexMLP (revIndexMLP t)).val
      = MLE (fun w : Fin ℓ → Fin 2 =>
          (revIndexMLP t).val.eval (fun j => ((w (Fin.rev j) : Fin 2) : L))) := rfl
    _ = MLE t.val.toEvalsZeroOne := by
        apply congrArg
        funext w
        rw [revIndexMLP_eval_zeroOne t (fun j => w (Fin.rev j))]
        unfold MvPolynomial.toEvalsZeroOne
        apply congrArg (fun x : Fin ℓ → L => MvPolynomial.eval x t.val)
        funext j
        simp [Fin.rev_rev]
    _ = t.val := hmle

lemma revIndexMLP_injective :
    Function.Injective (revIndexMLP (L := L) (ℓ := ℓ)) := by
  intro t₁ t₂ h
  have h2 := congrArg (revIndexMLP (L := L) (ℓ := ℓ)) h
  rwa [revIndexMLP_involutive, revIndexMLP_involutive] at h2

lemma statementOrderBitsOfIndex_eq_coe_bit2 (ω : Fin (2 ^ ℓ)) :
    (statementOrderBitsOfIndex (L := L) ω : Fin ℓ → L) =
      fun j => ((bit2 ω (Fin.rev j) : Fin 2) : L) := by
  funext j
  unfold statementOrderBitsOfIndex bitsOfIndex bit2
  rw [apply_ite (fun b : Fin 2 => ((b : Fin 2) : L))]
  simp

/-- **G1**: evaluating `revIndexMLP s` at a statement-order Boolean index recovers the
straight-order evaluation of `s`. -/
lemma revIndexMLP_eval_statementOrderBits (s : MultilinearPoly L ℓ) (ω : Fin (2 ^ ℓ)) :
    (revIndexMLP s).val.eval (statementOrderBitsOfIndex (L := L) ω) =
      s.val.eval (fun j => ((bit2 ω j : Fin 2) : L)) := by
  rw [statementOrderBitsOfIndex_eq_coe_bit2]
  have h := revIndexMLP_eval_zeroOne s (fun j => bit2 ω (Fin.rev j))
  rw [h]
  apply congrArg (fun x : Fin ℓ → L => MvPolynomial.eval x s.val)
  funext j
  simp [Fin.rev_rev]

/-- **G2**: the MLE reconstruction of indexed coefficients, evaluated at the straight
Boolean digits of `ω`, recovers the coefficient at `ω`. -/
lemma MLE_binaryFinMap_eval_bit2 (g : Fin (2 ^ ℓ) → L) (ω : Fin (2 ^ ℓ))
    (hb : ∀ (w : Fin ℓ → Fin 2) (j : Fin ℓ), ((w j : Fin 2) : ℕ) ≤ 1) :
    (MLE (fun w : Fin ℓ → Fin 2 =>
        g (Nat.binaryFinMapToNat (fun j => ((w j : Fin 2) : ℕ)) (hb w)))).eval
      (fun j => ((bit2 ω j : Fin 2) : L)) = g ω := by
  have h := MLE_eval_zeroOne (R := L) (bit2 ω)
    (fun w : Fin ℓ → Fin 2 =>
      g (Nat.binaryFinMapToNat (fun j => ((w j : Fin 2) : ℕ)) (hb w)))
  rw [h, binaryFinMapToNat_bit2]

/-- **F1**: rebuilding from statement-order coefficients of `t` yields
`revIndexMLP t`. -/
lemma MLE_binaryFinMap_statementOrder_eq_revIndexMLP (t : MultilinearPoly L ℓ)
    (hb : ∀ (w : Fin ℓ → Fin 2) (j : Fin ℓ), ((w j : Fin 2) : ℕ) ≤ 1) :
    MLE (fun w : Fin ℓ → Fin 2 =>
        t.val.eval (statementOrderBitsOfIndex (L := L)
          (Nat.binaryFinMapToNat (fun j => ((w j : Fin 2) : ℕ)) (hb w)))) =
      (revIndexMLP t).val := by
  symm
  apply eq_MLE_of_isMultilinear_of_eval_eq _ (revIndexMLP t).property
  intro w
  have h := revIndexMLP_eval_zeroOne t w
  have hcoe : ((w : Fin ℓ → Fin 2) : Fin ℓ → L) = fun j => ((w j : Fin 2) : L) := rfl
  rw [hcoe, h]
  apply congrArg (fun x : Fin ℓ → L => MvPolynomial.eval x t.val)
  funext j
  unfold statementOrderBitsOfIndex bitsOfIndex
  rw [Nat.getBit_of_binaryFinMapToNat]
  have hlt : (Fin.rev j).val < ℓ := (Fin.rev j).isLt
  simp only [hlt, ↓reduceDIte, Fin.eta]
  exact fin2_coe_eq_ite (w (Fin.rev j))

end MLEBridge

/-! ## The decoding pipeline, abstracted over the domain enumeration -/

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The MLE reconstruction step of `extractMLP` at level `0`. -/
def buildMLP (P : L[X]) : MultilinearPoly L ℓ :=
  have h_ℓ_le_r : ℓ ≤ r := by omega
  ⟨MLE (fun w : Fin ℓ → Fin 2 =>
      AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ h_ℓ_le_r (fun i => P.coeff i.val)
        (Nat.binaryFinMapToNat (m := fun j => ((w j : Fin 2) : ℕ))
          (fun j => Nat.le_of_lt_succ (w j).isLt))),
    MLE_mem_restrictDegree _⟩

/-- The decoding pipeline of `extractMLP` at level `0`, with the domain enumeration
abstracted into an arbitrary equivalence `E`. -/
def extractPipeline {N : ℕ} [NeZero N]
    (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N)
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L) :
    Option (MultilinearPoly L ℓ) :=
  let e : ℕ := (Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))).toNat
  match BerlekampWelch.decoder e (2 ^ ℓ) (fun j => (E.symm j).val) (fun j => f (E.symm j)) with
  | none => none
  | some P =>
    if P.natDegree ≥ 2 ^ ℓ then none
    else some (buildMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P)

lemma val_zero_lt_card : ((0 : Fin r) : ℕ) < ℓ + 𝓡 := by
  show (0 : ℕ) < ℓ + 𝓡
  have := Nat.pos_of_neZero ℓ
  omega

/-- The body equivalence used by `extractMLP` at `i = 0`. -/
def domainEquiv₀ :
    sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃
      Fin (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r))) := by
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
    (h_i := val_zero_lt_card (r := r) (ℓ := ℓ) (𝓡 := 𝓡)), hF₂.out]
  exact sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
    (h_i := val_zero_lt_card (r := r) (ℓ := ℓ) (𝓡 := 𝓡))

instance cardSDomain₀_neZero :
    NeZero (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r))) := by
  constructor
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
    (h_i := val_zero_lt_card (r := r) (ℓ := ℓ) (𝓡 := 𝓡)), hF₂.out]
  positivity

/-- `extractMLP` at level `0` **is** the abstract pipeline at the body equivalence. -/
lemma extractMLP_zero_eq_extractPipeline
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0) :
    extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f =
      extractPipeline 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (domainEquiv₀ 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) f := rfl

/-! ## Core arguments on the abstract pipeline -/

section Core

variable {N : ℕ} [NeZero N]

/-- The codeword of a low-degree polynomial belongs to `BBF_Code` at level `0`. -/
lemma polyEval_mem_BBF_Code₀ (P : L[X]) (hdeg : P.natDegree < 2 ^ ℓ) :
    (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) ∈
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
  unfold BBF_Code
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  refine ⟨P, ?_, ?_⟩
  · simp only [Fin.val_zero, tsub_zero]
    calc P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < ((2 ^ ℓ : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg
  · funext x
    simp [ReedSolomon.evalOnPoints]

/-- Distance transport along the pipeline enumeration. -/
lemma pipeline_dist_transport (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N)
    (u : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L) (P : L[X]) :
    hammingDist (fun j => u (E.symm j)) (P.eval ∘ fun j => (E.symm j).val) =
      hammingDist u (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) :=
  hammingDist_comp_equiv E.symm u
    (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val)

lemma pipeline_omegas_injective (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N) :
    Function.Injective
      (fun j : Fin N => ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L)) := by
  intro a b hab
  exact E.symm.injective (Subtype.ext hab)

lemma N_eq_card (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N) :
    N = 2 ^ (ℓ + 𝓡) := by
  have h := Fintype.card_congr E
  rw [Fintype.card_fin] at h
  rw [← h]
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := (0 : Fin r))
    (h_i := val_zero_lt_card (r := r) (ℓ := ℓ) (𝓡 := 𝓡)), hF₂.out]
  simp only [Fin.val_zero, tsub_zero]

lemma BBF_CodeDistance₀_eq :
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) =
      2 ^ (ℓ + 𝓡) - 2 ^ ℓ + 1 := by
  rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ)]
  simp only [Fin.val_zero, tsub_zero]

/-- **Backward direction, pipeline form.**  Inside the unique decoding radius the
Berlekamp–Welch decoder finds exactly the consistency-prop codeword, and the MLE
reconstruction returns the variable-reversed polynomial. -/
theorem extractPipeline_eq_some_of_consistency
    (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N)
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (t : MultilinearPoly L ℓ)
    (h : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t f) :
    extractPipeline 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) E f =
      some (revIndexMLP t) := by
  classical
  have h_ℓ_le_r : ℓ ≤ r := by omega
  -- the consistency codeword
  set c : Fin (2 ^ ℓ) → L :=
    fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω) with hc
  set P₀ : L⦃< 2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) c with hP₀
  set Pcw : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L :=
    fun x => P₀.val.eval x.val with hPcw
  have hcons : 2 * hammingDist Pcw f <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := h
  have hP₀deg : P₀.val.natDegree < 2 ^ ℓ := by
    have hprop := P₀.property
    rw [Polynomial.mem_degreeLT] at hprop
    by_cases hz : P₀.val = 0
    · simp [hz]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by exact_mod_cast hprop)
  have hPmem : Pcw ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :=
    polyEval_mem_BBF_Code₀ 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P₀.val hP₀deg
  -- realize the distance from the code
  haveI hne : Nonempty
      ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L)) : Type) :=
    ⟨⟨0, Submodule.zero_mem _⟩⟩
  obtain ⟨M, hM_mem, hM_dist⟩ := Code.exists_closest_codeword_of_Nonempty_Code
    (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L))) f
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) with hd
  have hd_eq : d = (hammingDist f M : ℕ∞) := hM_dist.symm
  have he_toNat : d.toNat = hammingDist f M := by rw [hd_eq]; simp
  -- the realized distance is at most the distance to the consistency codeword
  have hle : hammingDist f M ≤ hammingDist f Pcw := by
    have h1 : d ≤ (hammingDist f Pcw : ℕ∞) :=
      Code.distFromCode_le_dist_to_mem f Pcw hPmem
    rw [hd_eq] at h1
    exact_mod_cast h1
  -- inside the UDR the closest codeword IS the consistency codeword
  have hMP : M = Pcw := by
    by_contra hne'
    have hge : BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) ≤
        hammingDist M Pcw :=
      Code.pairDist_ge_code_mindist_of_ne hM_mem hPmem hne'
    have htri : hammingDist M Pcw ≤ hammingDist M f + hammingDist f Pcw :=
      hammingDist_triangle M f Pcw
    have hMf : hammingDist M f = hammingDist f M := hammingDist_comm M f
    have htri' : hammingDist M Pcw ≤ hammingDist f M + hammingDist f Pcw := by
      simpa [hMf] using htri
    have hcons' : 2 * hammingDist f Pcw <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
      simpa [hammingDist_comm Pcw f] using hcons
    omega
  have hwe : hammingDist f Pcw = d.toNat := by
    rw [he_toNat, hMP]
  -- decoder succeeds and returns exactly P₀
  have hNcard : N = 2 ^ (ℓ + 𝓡) :=
    N_eq_card 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) E
  have hdist_eq := BBF_CodeDistance₀_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ℓ := ℓ) (𝓡 := 𝓡)
  have hkN : 2 ^ ℓ ≤ N := by
    rw [hNcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUDRrad : 2 * d.toNat < N - 2 ^ ℓ + 1 := by
    have hcons_d : 2 * d.toNat <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
      have hcons' : 2 * hammingDist f Pcw <
          BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
        simpa [hammingDist_comm Pcw f] using hcons
      simpa [hwe] using hcons'
    simpa [hNcard, hdist_eq] using hcons_d
  have hdist_dec : hammingDist (fun j => f (E.symm j))
      (P₀.val.eval ∘ fun j =>
        ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L)) ≤ d.toNat := by
    have htrans := pipeline_dist_transport 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      E f P₀.val
    rw [htrans, ← hPcw, hwe]
  have hdec : BerlekampWelch.decoder d.toNat (2 ^ ℓ)
      (fun j => ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L))
      (fun j => f (E.symm j)) = some P₀.val :=
    BerlekampWelch.decoder_eq_some hUDRrad hkN
      (pipeline_omegas_injective 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) E)
      hP₀deg hdist_dec
  -- reduce the pipeline
  unfold extractPipeline
  rw [← hd] at *
  dsimp only
  change (match BerlekampWelch.decoder d.toNat (2 ^ ℓ)
      (fun j => ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L))
      (fun j => f (E.symm j)) with
    | none => none
    | some P => if P.natDegree ≥ 2 ^ ℓ then none
        else some (buildMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P)) =
      some (revIndexMLP t)
  simp [hdec, if_neg (Nat.not_le_of_gt hP₀deg)]
  -- identify the reconstruction with `revIndexMLP t`
  apply Subtype.ext
  show MLE _ = (revIndexMLP t).val
  have hcoeffs : AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ h_ℓ_le_r
      (fun i => P₀.val.coeff i.val) = c := by
    have hh := monomialToNovelCoeffs_coeff_polynomialFromNovelCoeffs 𝔽q β
      (m := ℓ) (h := h_ℓ_le_r) c
    rw [hP₀]
    exact hh
  rw [hcoeffs]
  exact MLE_binaryFinMap_statementOrder_eq_revIndexMLP t _

/-- **Forward direction, pipeline form** (with the `UDRClose` guard). -/
theorem consistency_of_extractPipeline_eq_some
    (E : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) ≃ Fin N)
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (tpoly : MultilinearPoly L ℓ)
    (hUDR : 2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞))
    (hex : extractPipeline 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) E f = some tpoly) :
    firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (revIndexMLP tpoly) f := by
  classical
  have h_ℓ_le_r : ℓ ≤ r := by omega
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) with hd
  have hd_ne_top : d ≠ ⊤ := by
    intro htop
    rw [htop] at hUDR
    simp at hUDR
  have hUDRnat : 2 * d.toNat <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
    lift d to ℕ using hd_ne_top with dn hdn
    rw [ENat.toNat_coe]
    exact_mod_cast hUDR
  -- open the pipeline
  unfold extractPipeline at hex
  rw [← hd] at hex
  dsimp only at hex
  change (match BerlekampWelch.decoder d.toNat (2 ^ ℓ)
      (fun j => ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L))
      (fun j => f (E.symm j)) with
    | none => none
    | some P => if P.natDegree ≥ 2 ^ ℓ then none
        else some (buildMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P)) =
      some tpoly at hex
  rcases hdec : BerlekampWelch.decoder d.toNat (2 ^ ℓ)
      (fun j => ((E.symm j : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) : L))
      (fun j => f (E.symm j)) with _ | P
  · simp [hdec] at hex
  · simp [hdec] at hex
    have hPdeg : P.natDegree < 2 ^ ℓ := hex.1
    have htp : tpoly = buildMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P :=
      hex.2.symm
    -- decoded distance bound, transported back to the domain
    have hdist := BerlekampWelch.hammingDist_le_of_decoder_eq_some hdec
    have hdist' : hammingDist f
        (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) ≤ d.toNat := by
      have htrans := pipeline_dist_transport 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        E f P
      rw [← htrans]
      exact hdist
    -- the consistency coefficients of `revIndexMLP tpoly` are the decoded novel coeffs
    set cP : Fin (2 ^ ℓ) → L :=
      AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ h_ℓ_le_r (fun i => P.coeff i.val) with hcP
    have hcoeff_eq : (fun ω => (revIndexMLP tpoly).val.eval
        (statementOrderBitsOfIndex (L := L) ω)) = cP := by
      funext ω
      rw [revIndexMLP_eval_statementOrderBits]
      rw [htp]
      rw [show (buildMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) P).val =
          MLE (fun w : Fin ℓ → Fin 2 =>
            cP (Nat.binaryFinMapToNat (m := fun j => ((w j : Fin 2) : ℕ))
              (fun j => Nat.le_of_lt_succ (w j).isLt))) from rfl]
      exact MLE_binaryFinMap_eval_bit2 cP ω _
    have hpoly_eq : (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
        (fun ω => (revIndexMLP tpoly).val.eval
          (statementOrderBitsOfIndex (L := L) ω))).val = P := by
      have hbase : polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ_le_r cP = P := by
        rw [hcP]
        exact polynomialFromNovelCoeffs_monomialToNovelCoeffs 𝔽q β ℓ h_ℓ_le_r P
          hPdeg
      calc (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
          (fun ω => (revIndexMLP tpoly).val.eval
            (statementOrderBitsOfIndex (L := L) ω))).val
          = polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ_le_r
            (fun ω => (revIndexMLP tpoly).val.eval
              (statementOrderBitsOfIndex (L := L) ω)) := rfl
        _ = polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ_le_r cP := by rw [hcoeff_eq]
        _ = P := hbase
    -- conclude
    show 2 * hammingDist _ f <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩
    rw [hpoly_eq]
    have hcomm : hammingDist
        (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) f =
        hammingDist f
          (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) :=
      hammingDist_comm _ _
    have hgoal : 2 * hammingDist
        (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.eval x.val) f <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
      omega
    exact hgoal

end Core

/-! ## Main theorems -/

section Main

/-- Consistency forces UDR-closeness of `f` (the guard is free in the backward
direction). -/
lemma UDRClose_of_firstOracleWitnessConsistency
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (t : MultilinearPoly L ℓ)
    (h : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t f) :
    2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞) := by
  classical
  set c : Fin (2 ^ ℓ) → L :=
    fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω) with hc
  set P₀ : L⦃< 2 ^ ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) c with hP₀
  set Pcw : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L :=
    fun x => P₀.val.eval x.val with hPcw
  have hcons : 2 * hammingDist Pcw f <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := h
  have hP₀deg : P₀.val.natDegree < 2 ^ ℓ := by
    have hprop := P₀.property
    rw [Polynomial.mem_degreeLT] at hprop
    by_cases hz : P₀.val = 0
    · simp [hz]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by exact_mod_cast hprop)
  have hPmem : Pcw ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :=
    polyEval_mem_BBF_Code₀ 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) P₀.val hP₀deg
  have hle : Code.distFromCode (u := f)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) ≤
      (hammingDist f Pcw : ℕ∞) :=
    Code.distFromCode_le_dist_to_mem
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
      (u := f) (v := Pcw) (hv := hPmem)
  calc 2 * (Code.distFromCode (u := f)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)))
      ≤ 2 * (hammingDist f Pcw : ℕ∞) := mul_le_mul_left' hle 2
    _ = ((2 * hammingDist f Pcw : ℕ) : ℕ∞) := by push_cast; ring
    _ < (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞) := by
        rw [hammingDist_comm]
        exact_mod_cast hcons

/-- **Backward direction** of the corrected residual: consistency of `t` with `f`
forces `extractMLP` to succeed — with output `revIndexMLP t`, *not* `t`. -/
theorem extractMLP_zero_eq_some_of_firstOracleWitnessConsistency
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (t : MultilinearPoly L ℓ)
    (h : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t f) :
    extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some (revIndexMLP t) := by
  rw [extractMLP_zero_eq_extractPipeline]
  exact extractPipeline_eq_some_of_consistency 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) _ f t h

/-- **Forward direction** of the corrected residual, under the (necessary)
`UDRClose` guard. -/
theorem firstOracleWitnessConsistency_revIndexMLP_of_extractMLP_eq_some
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (tpoly : MultilinearPoly L ℓ)
    (hUDR : 2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞))
    (hex : extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some tpoly) :
    firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (revIndexMLP tpoly) f := by
  rw [extractMLP_zero_eq_extractPipeline] at hex
  exact consistency_of_extractPipeline_eq_some 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) _ f tpoly hUDR hex

/-- **The corrected two-sided characterization** of `extractMLP` at the base level.
The output is the *variable-reversed* multilinear polynomial, and the forward direction
additionally requires the `UDRClose` guard. -/
theorem extractMLP_zero_eq_some_revIndexMLP_iff
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (tpoly : MultilinearPoly L ℓ) :
    (extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some tpoly ∧
      2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞)) ↔
    firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (revIndexMLP tpoly) f := by
  constructor
  · rintro ⟨hex, hUDR⟩
    exact firstOracleWitnessConsistency_revIndexMLP_of_extractMLP_eq_some 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f tpoly hUDR hex
  · intro h
    refine ⟨?_, UDRClose_of_firstOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f (revIndexMLP tpoly) h⟩
    have hsome := extractMLP_zero_eq_some_of_firstOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f (revIndexMLP tpoly) h
    rwa [revIndexMLP_involutive] at hsome

/-- The uniqueness consequence consumed by `Relations.lean`
(`firstOracleWitnessConsistencyProp_unique`), proved here **without** any residual
instance. -/
theorem firstOracleWitnessConsistencyProp_unique'
    (t₁ t₂ : MultilinearPoly L ℓ)
    (f₀ : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁ f₀)
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₂ f₀) :
    t₁ = t₂ := by
  have e₁ := extractMLP_zero_eq_some_of_firstOracleWitnessConsistency 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f₀ t₁ h₁
  have e₂ := extractMLP_zero_eq_some_of_firstOracleWitnessConsistency 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f₀ t₂ h₂
  rw [e₁] at e₂
  exact revIndexMLP_injective (Option.some.inj e₂)

/-!
The deleted extraction hypothesis would force every multilinear polynomial to equal its
variable-reversal. The corrected theorem above is the replacement: extraction success identifies
the reversed witness under the UDR guard, and the old unreversed statement should not be
reintroduced.
-/

/-- **Existence of a consistency witness inside the UDR.** Every word that is UDR-close to the
level-`0` code admits a multilinear consistency witness: rebuild the close codeword's polynomial
in the novel basis and reindex its coefficients into statement order. -/
lemma exists_firstOracleWitnessConsistency_of_UDRClose
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (hUDR : 2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞)) :
    ∃ t : MultilinearPoly L ℓ,
      firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t f := by
  classical
  have h_ℓ_le_r : ℓ ≤ r := by omega
  -- 1. The closest codeword realizes the distance.
  haveI hne : Nonempty
      ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L)) : Type) :=
    ⟨⟨0, Submodule.zero_mem _⟩⟩
  obtain ⟨M, hM_mem, hM_dist⟩ := Code.exists_closest_codeword_of_Nonempty_Code
    (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L))) f
  have hM_close : 2 * hammingDist M f <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
    have h2 : 2 * (hammingDist f M : ℕ∞) <
        (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞) := by
      rw [← hM_dist] at hUDR
      exact_mod_cast hUDR
    have h3 : 2 * hammingDist f M <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := by
      exact_mod_cast h2
    simpa [hammingDist_comm M f] using h3
  -- 2. The codeword is the evaluation of a low-degree polynomial.
  obtain ⟨P, hP_eval⟩ := exists_BBF_poly_of_codeword 𝔽q β (0 : Fin r) ⟨M, hM_mem⟩
  have hPdeg : P.val.natDegree < 2 ^ ℓ := by
    have hprop := P.property
    rw [Polynomial.mem_degreeLT] at hprop
    by_cases hz : P.val = 0
    · simp only [hz, Polynomial.natDegree_zero]
      positivity
    · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (by
        simpa using hprop)
      simpa using this
  -- 3. Statement-order coefficients of the close polynomial.
  set c : Fin (2 ^ ℓ) → L :=
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ h_ℓ_le_r (fun i => P.val.coeff i.val) with hc
  have hb : ∀ (w : Fin ℓ → Fin 2) (j : Fin ℓ), ((w j : Fin 2) : ℕ) ≤ 1 := fun w j =>
    Nat.lt_succ_iff.mp (w j).isLt
  set s : MultilinearPoly L ℓ :=
    ⟨MLE (fun w : Fin ℓ → Fin 2 =>
        c (Nat.binaryFinMapToNat (fun j => ((w j : Fin 2) : ℕ)) (hb w))),
      MLE_mem_restrictDegree _⟩ with hs
  refine ⟨revIndexMLP s, ?_⟩
  -- 4. The statement-order evaluations of `revIndexMLP s` are exactly `c`.
  have heval : (fun ω => (revIndexMLP s).val.eval (statementOrderBitsOfIndex (L := L) ω)) = c := by
    funext ω
    rw [revIndexMLP_eval_statementOrderBits]
    exact MLE_binaryFinMap_eval_bit2 (ℓ := ℓ) c ω hb
  -- 5. Hence the consistency polynomial is `P` itself, and `f` is close to its codeword.
  show 2 * hammingDist
      (fun x => (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => (revIndexMLP s).val.eval (statementOrderBitsOfIndex ω))).val.eval x.val) f <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, by omega⟩
  have hP₀ : (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
      (fun ω => (revIndexMLP s).val.eval (statementOrderBitsOfIndex ω))).val = P.val := by
    have hround := polynomialFromNovelCoeffs_monomialToNovelCoeffs 𝔽q β
      (m := ℓ) (h := h_ℓ_le_r) P.val hPdeg
    calc (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
        (fun ω => (revIndexMLP s).val.eval (statementOrderBitsOfIndex ω))).val
        = (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r) c).val := by
          rw [heval]
      _ = P.val := hround
  have hMfun : (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) => P.val.eval x.val) = M := by
    funext x
    have := congrFun hP_eval x
    simpa [polyToOracleFunc] using this
  have hPcw_eq_M : (fun x : sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) =>
      (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega : ℓ ≤ r)
        (fun ω => (revIndexMLP s).val.eval (statementOrderBitsOfIndex ω))).val.eval x.val) = M := by
    funext x
    rw [hP₀]
    exact congrFun hMfun x
  rw [hPcw_eq_M]
  exact hM_close

/-- **Decoder success inside the UDR** (existence form): if `f` is UDR-close to the level-`0`
code, `extractMLP` succeeds. -/
lemma extractMLP_zero_isSome_of_UDRClose
    (f : OracleFunction (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (𝓡 := 𝓡) 0)
    (hUDR : 2 * Code.distFromCode (u := f)
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞)) :
    ∃ tpoly : MultilinearPoly L ℓ,
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some tpoly := by
  obtain ⟨t, ht⟩ := exists_firstOracleWitnessConsistency_of_UDRClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f hUDR
  exact ⟨revIndexMLP t,
    extractMLP_zero_eq_some_of_firstOracleWitnessConsistency 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f t ht⟩

end Main

end

end Binius.BinaryBasefold
