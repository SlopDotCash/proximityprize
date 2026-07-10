/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick

/-!
# Binary Basefold Codes and Soundness Tools

Defines the Reed-Solomon codes `BBF_Code` underlying the Binary Basefold protocol and the
machinery used in its soundness analysis: unique-decoding-radius closeness (`UDRClose`),
codeword extraction (`extractUDRCodeword`), disagreement and fiberwise-distance notions
(`disagreementSet`, `fiberwiseDistance`, `fiberwiseClose`), and lemmas relating Hamming distance
across folding steps.
-/

set_option maxHeartbeats 400000
set_option linter.style.longFile 1700
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial Nat Matrix
open ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

/-- Evaluate a bounded-degree univariate polynomial on the Binary Basefold domain `S⁽ⁱ⁾`. -/
def polyToOracleFunc (domainIdx : Fin r) (P : L⦃< 2 ^ (ℓ - domainIdx.val)⦄[X]) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) domainIdx :=
  fun x => P.val.eval x.val

/-- The Reed-Solomon code C^(i) for round i in Binary Basefold.
For each i ∈ {0, steps, ..., ℓ}, C(i) is the Reed-Solomon code
RS_{L, S⁽ⁱ⁾}[2^{ℓ+R-i}, 2^{ℓ-i}]. -/
def BBF_Code (i : Fin r) :
    Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma exists_BBF_poly_of_codeword (i : Fin r)
    (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  ∃ P : L⦃< 2 ^ (ℓ - i)⦄[X],
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := i) (P := P) = u := by
  have h_u_mem := u.property
  unfold BBF_Code at h_u_mem
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at h_u_mem
  obtain ⟨P_raw, hP_degree, hP_eval⟩ := h_u_mem
  let P : L⦃< 2 ^ (ℓ - i)⦄[X] := ⟨P_raw, by
    simpa [Polynomial.mem_degreeLT] using hP_degree⟩
  use P
  ext x
  simpa [polyToOracleFunc, ReedSolomon.evalOnPoints] using congrFun hP_eval.symm x

def getBBF_Codeword_poly (i : Fin r)
    (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
    L⦃< 2 ^ (ℓ - i)⦄[X] :=
  Classical.choose (exists_BBF_poly_of_codeword 𝔽q β i u)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma getBBF_Codeword_poly_spec (i : Fin r)
    (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  u = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
    (P := getBBF_Codeword_poly 𝔽q β i u) := by
  let res := Classical.choose_spec (exists_BBF_poly_of_codeword 𝔽q β i u)
  exact id (Eq.symm res)

def getBBF_Codeword_of_poly (i : Fin r) (h_i : i ≤ ℓ) (P : L⦃< 2 ^ (ℓ - i)⦄[X]) :
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P)
  have h_g_mem : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    unfold BBF_Code
    rw [ReedSolomon.mem_code_iff_exists_polynomial]
    exact ⟨P.val, Polynomial.mem_degreeLT.mp P.2, by
      ext y
      simp [g, polyToOracleFunc, ReedSolomon.evalOnPoints]⟩
  exact ⟨g, h_g_mem⟩

/-- The binary quotient map is a nonzero scalar multiple of `X^2 - X`. -/
lemma qMap_eq_C_mul_X_sq_sub_X (i : Fin r) :
    ∃ c : L, c ≠ 0 ∧ qMap 𝔽q β i = C c * (X ^ 2 - X) := by
  let c : L := ((W 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  refine ⟨c, ?_, ?_⟩
  · unfold c
    apply div_ne_zero
    · exact pow_ne_zero _ (AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β i)
    · exact AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β (i + 1)
  · rw [qMap, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L (p := X)]
    simp [hF₂.out, c]

lemma degree_X_sq_sub_X : (X ^ 2 - X : L[X]).degree = (2 : WithBot ℕ) := by
  have hdegX : (X : L[X]).degree < (X ^ 2 : L[X]).degree := by
    rw [degree_X, degree_X_pow]
    norm_num
  rw [degree_sub_eq_left_of_degree_lt hdegX]
  rw [degree_X_pow]
  norm_num

lemma qMap_degree (i : Fin r) : (qMap 𝔽q β i).degree = (2 : WithBot ℕ) := by
  obtain ⟨c, hc, hq⟩ := qMap_eq_C_mul_X_sq_sub_X (𝔽q := 𝔽q) (β := β) (i := i)
  rw [hq, degree_C_mul hc, degree_X_sq_sub_X]

lemma qMap_natDegree (i : Fin r) : (qMap 𝔽q β i).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  exact qMap_degree (𝔽q := 𝔽q) (β := β) (i := i)

lemma qMap_leadingCoeff_ne_zero (i : Fin r) :
    (qMap 𝔽q β i).leadingCoeff ≠ 0 := by
  intro h
  exact qMap_ne_zero (𝔽q := 𝔽q) (β := β) i (Polynomial.leadingCoeff_eq_zero.mp h)

lemma degree_even_qMap_term (i : Fin r) (a : L) (ha : a ≠ 0) (d : ℕ) :
    ((C a * X ^ d).comp (qMap 𝔽q β i)).degree = ((2 * d : ℕ) : WithBot ℕ) := by
  have hqpos : (0 : WithBot ℕ) < (qMap 𝔽q β i).degree := by
    rw [qMap_degree (𝔽q := 𝔽q) (β := β) (i := i)]
    norm_num
  rw [Polynomial.degree_comp hqpos]
  rw [Polynomial.degree_C_mul_X_pow d ha]
  rw [qMap_degree (𝔽q := 𝔽q) (β := β) (i := i)]
  norm_num
  ring

lemma leadingCoeff_even_qMap_term (i : Fin r) (a : L) (ha : a ≠ 0) (d : ℕ) :
    ((C a * X ^ d).comp (qMap 𝔽q β i)).leadingCoeff =
      a * (qMap 𝔽q β i).leadingCoeff ^ d := by
  rw [Polynomial.leadingCoeff_comp]
  · rw [Polynomial.leadingCoeff_C_mul_X_pow]
    rw [Polynomial.natDegree_C_mul_X_pow d a ha]
  · rw [qMap_natDegree (𝔽q := 𝔽q) (β := β) (i := i)]
    norm_num

lemma degree_odd_qMap_term (i : Fin r) (a : L) (ha : a ≠ 0) (d : ℕ) :
    (X * (C a * X ^ d).comp (qMap 𝔽q β i)).degree =
      ((2 * d + 1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_mul]
  rw [Polynomial.degree_X]
  rw [degree_even_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a ha d]
  norm_num
  ring

lemma leadingCoeff_odd_qMap_term (i : Fin r) (a : L) (d : ℕ) :
    (X * (C a * X ^ d).comp (qMap 𝔽q β i)).leadingCoeff =
      a * (qMap 𝔽q β i).leadingCoeff ^ d := by
  rw [Polynomial.leadingCoeff_mul]
  rw [Polynomial.leadingCoeff_X]
  by_cases ha : a = 0
  · simp [ha]
  · rw [leadingCoeff_even_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a ha d]
    ring

lemma natDegree_C_mul_X_pow_lt {a : L} (ha : a ≠ 0) {d m : ℕ} (hd : d < m) :
    (C a * X ^ d : L[X]).natDegree < m := by
  rw [Polynomial.natDegree_C_mul_X_pow d a ha]
  exact hd

lemma natDegree_add_lt_of_lt {P Q : L[X]} {m : ℕ}
    (hP : P.natDegree < m) (hQ : Q.natDegree < m) :
    (P + Q).natDegree < m := by
  exact lt_of_le_of_lt (Polynomial.natDegree_add_le P Q) (max_lt hP hQ)

/-- Every polynomial of degree `< 2m` decomposes as `A(qᵢ(X)) + X B(qᵢ(X))` with
`A, B` of degree `< m`. This is the quadratic `qMap` replacement for the old intermediate
novel-basis round trip. -/
lemma qMap_quadratic_decomp_of_natDegree_lt
    (i : Fin r) (m : ℕ) (hm : 0 < m) (P : L[X])
    (hPbound : P.natDegree < 2 * m) :
    ∃ A B : L[X], A.natDegree < m ∧ B.natDegree < m ∧
      P = A.comp (qMap 𝔽q β i) + X * B.comp (qMap 𝔽q β i) := by
  classical
  let q := qMap 𝔽q β i
  let c := q.leadingCoeff
  have hc : c ≠ 0 := qMap_leadingCoeff_ne_zero (𝔽q := 𝔽q) (β := β) i
  refine (Nat.strong_induction_on
    (p := fun n => ∀ (P : L[X]) (m : ℕ), 0 < m → P.natDegree < 2 * m →
      P.natDegree = n →
      ∃ A B : L[X], A.natDegree < m ∧ B.natDegree < m ∧
        P = A.comp (qMap 𝔽q β i) + X * B.comp (qMap 𝔽q β i))
    P.natDegree ?_) P m hm hPbound rfl
  intro n ih P m hm hPbound hn
  subst hn
  by_cases hPzero : P = 0
  · refine ⟨0, 0, ?_, ?_, ?_⟩
    · simpa [hm] using hm
    · simpa [hm] using hm
    · simp [hPzero]
  let n := P.natDegree
  have hPdeg : P.degree = (n : WithBot ℕ) := Polynomial.degree_eq_natDegree hPzero
  have hP_lc_ne : P.leadingCoeff ≠ 0 := by
    intro h
    exact hPzero (Polynomial.leadingCoeff_eq_zero.mp h)
  by_cases h_even : n % 2 = 0
  · let d := n / 2
    have hn_eq : n = 2 * d := by
      have hmod := Nat.mod_add_div n 2
      dsimp [d]
      omega
    have hd_lt_m : d < m := by
      have := hPbound
      dsimp [d]
      omega
    let a : L := P.leadingCoeff / c ^ d
    have hc_pow : c ^ d ≠ 0 := pow_ne_zero _ hc
    have ha : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero hP_lc_ne hc_pow
    let T : L[X] := (C a * X ^ d).comp q
    have hTdeg : T.degree = (n : WithBot ℕ) := by
      dsimp [T, q]
      rw [degree_even_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a ha d]
      rw [hn_eq]
    have hTlc : T.leadingCoeff = P.leadingCoeff := by
      dsimp [T, q, c, a]
      rw [leadingCoeff_even_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a ha d]
      change (P.leadingCoeff / c ^ d) * c ^ d = P.leadingCoeff
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc_pow, mul_one]
    let P' : L[X] := P - T
    by_cases hP'zero : P' = 0
    · refine ⟨C a * X ^ d, 0, ?_, ?_, ?_⟩
      · exact natDegree_C_mul_X_pow_lt ha hd_lt_m
      · simpa [hm] using hm
      · have hPT : P = T := by
          dsimp [P'] at hP'zero
          exact sub_eq_zero.mp hP'zero
        rw [hPT]
        simp [T, q]
    · have hP'deg_lt : P'.degree < P.degree := by
        dsimp [P']
        exact Polynomial.degree_sub_lt (by rw [hPdeg, hTdeg]) hPzero (by rw [hTlc])
      have hP'nat_lt : P'.natDegree < n := by
        have hdegP' := Polynomial.degree_eq_natDegree hP'zero
        rw [hPdeg, hdegP'] at hP'deg_lt
        exact WithBot.coe_lt_coe.mp hP'deg_lt
      have hP'bound : P'.natDegree < 2 * m := lt_trans hP'nat_lt hPbound
      obtain ⟨A, B, hA, hB, hrep⟩ := ih P'.natDegree hP'nat_lt P' m hm hP'bound rfl
      refine ⟨A + C a * X ^ d, B, ?_, hB, ?_⟩
      · exact natDegree_add_lt_of_lt hA (natDegree_C_mul_X_pow_lt ha hd_lt_m)
      · have hP_eq : P = P' + T := by
          dsimp [P']
          abel
        rw [hP_eq, hrep]
        dsimp [T, q]
        simp [Polynomial.add_comp]
        ring
  · let d := n / 2
    have hn_mod_one : n % 2 = 1 := by
      have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
      omega
    have hn_eq : n = 2 * d + 1 := by
      have hmod := Nat.mod_add_div n 2
      dsimp [d]
      omega
    have hd_lt_m : d < m := by
      have := hPbound
      dsimp [d]
      omega
    let a : L := P.leadingCoeff / c ^ d
    have hc_pow : c ^ d ≠ 0 := pow_ne_zero _ hc
    have ha : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero hP_lc_ne hc_pow
    let T : L[X] := X * (C a * X ^ d).comp q
    have hTdeg : T.degree = (n : WithBot ℕ) := by
      dsimp [T, q]
      rw [degree_odd_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a ha d]
      rw [hn_eq]
    have hTlc : T.leadingCoeff = P.leadingCoeff := by
      dsimp [T, q, c, a]
      rw [leadingCoeff_odd_qMap_term (𝔽q := 𝔽q) (β := β) (i := i) a d]
      change (P.leadingCoeff / c ^ d) * c ^ d = P.leadingCoeff
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc_pow, mul_one]
    let P' : L[X] := P - T
    by_cases hP'zero : P' = 0
    · refine ⟨0, C a * X ^ d, ?_, ?_, ?_⟩
      · simpa [hm] using hm
      · exact natDegree_C_mul_X_pow_lt ha hd_lt_m
      · have hPT : P = T := by
          dsimp [P'] at hP'zero
          exact sub_eq_zero.mp hP'zero
        rw [hPT]
        simp [T, q]
    · have hP'deg_lt : P'.degree < P.degree := by
        dsimp [P']
        exact Polynomial.degree_sub_lt (by rw [hPdeg, hTdeg]) hPzero (by rw [hTlc])
      have hP'nat_lt : P'.natDegree < n := by
        have hdegP' := Polynomial.degree_eq_natDegree hP'zero
        rw [hPdeg, hdegP'] at hP'deg_lt
        exact WithBot.coe_lt_coe.mp hP'deg_lt
      have hP'bound : P'.natDegree < 2 * m := lt_trans hP'nat_lt hPbound
      obtain ⟨A, B, hA, hB, hrep⟩ := ih P'.natDegree hP'nat_lt P' m hm hP'bound rfl
      refine ⟨A, B + C a * X ^ d, hA, ?_, ?_⟩
      · exact natDegree_add_lt_of_lt hB (natDegree_C_mul_X_pow_lt ha hd_lt_m)
      · have hP_eq : P = P' + T := by
          dsimp [P']
          abel
        rw [hP_eq, hrep]
        dsimp [T, q]
        simp [Polynomial.add_comp]
        ring

lemma qMap_eval_qMap_total_fiber_one
    (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) (k : Fin 2) :
    (qMap 𝔽q β i).eval
      ((qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) k).val : L) = y.val := by
  have hiℓ : i.val < ℓ := by omega
  let iℓ : Fin ℓ := ⟨i.val, hiℓ⟩
  let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨iℓ.val, by omega⟩) :=
    qMap_total_fiber 𝔽q β (i := ⟨iℓ.val, by omega⟩) (steps := 1)
      (h_i_add_steps := by omega) (y := y) k
  have hx : x = qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y) k := by
    apply Subtype.ext
    rfl
  have hq := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate iℓ (by omega) x
  simp only [Subtype.ext_iff] at hq
  rw [← hx]
  rw [← hq]
  have h_res := is_fiber_iff_generates_quotient_point 𝔽q β iℓ (steps := 1) (by omega)
      (x := x) (y := y)
  exact congrArg Subtype.val (h_res.mpr (by
    rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])).symm

lemma qMap_total_fiber_one_val_sub
    (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    ((qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 1).val : L)
      - ((qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 0).val : L) = 1 := by
  have hsub := qMap_total_fiber_one_sub 𝔽q β i h_i h_le y
  have hcoe := congrArg
    (fun v : sDomain 𝔽q β h_ℓ_add_R_rate i => (v : L)) hsub
  push_cast at hcoe
  rw [get_sDomain_first_basis_eq_1 𝔽q β h_ℓ_add_R_rate i (by omega)] at hcoe
  exact hcoe

lemma fold_legacy_eval_qMap_decomp
    (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (A B P : L[X])
    (hP : P = A.comp (qMap 𝔽q β i) + X * B.comp (qMap 𝔽q β i))
    (r_chal : L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := h_i) (f := fun x => P.eval x.val) (r_chal := r_chal) y =
      (C (1 - r_chal) * A + C r_chal * B).eval y.val := by
  unfold fold_legacy
  set fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
    (h_i_add_steps := h_i) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  have hq0 : (qMap 𝔽q β i).eval x₀.val = y.val := by
    simpa [x₀, fiberMap] using
      qMap_eval_qMap_total_fiber_one (𝔽q := 𝔽q) (β := β) (i := i) h_i h_le y 0
  have hq1 : (qMap 𝔽q β i).eval x₁.val = y.val := by
    simpa [x₁, fiberMap] using
      qMap_eval_qMap_total_fiber_one (𝔽q := 𝔽q) (β := β) (i := i) h_i h_le y 1
  have hdiff : x₁.val - x₀.val = (1 : L) := by
    simpa [x₁, x₀, fiberMap] using
      qMap_total_fiber_one_val_sub (𝔽q := 𝔽q) (β := β) (i := i) h_i h_le y
  have hP_x₀ : P.eval x₀.val = A.eval y.val + x₀.val * B.eval y.val := by
    rw [hP]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, hq0]
  have hP_x₁ : P.eval x₁.val = A.eval y.val + x₁.val * B.eval y.val := by
    rw [hP]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, hq1]
  calc
    P.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val)
        = (A.eval y.val + x₀.val * B.eval y.val) *
            ((1 - r_chal) * x₁.val - r_chal) +
          (A.eval y.val + x₁.val * B.eval y.val) *
            (r_chal - (1 - r_chal) * x₀.val) := by
          rw [hP_x₀, hP_x₁]
    _ = A.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        B.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = A.eval y.val * (1 - r_chal) + B.eval y.val * r_chal := by
      rw [hdiff]
      ring
    _ = (C (1 - r_chal) * A + C r_chal * B).eval y.val := by
      simp [Polynomial.eval_add, Polynomial.eval_mul]
      ring

lemma natDegree_of_mem_degreeLT {n : ℕ} (hn : 0 < n) {P : L[X]}
    (hP : P ∈ Polynomial.degreeLT L n) :
    P.natDegree < n := by
  have hdeg : P.degree < (n : WithBot ℕ) := Polynomial.mem_degreeLT.mp hP
  by_cases hzero : P = 0
  · simp [hzero, hn]
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hdeg

lemma natDegree_C_mul_add_C_mul_lt {m : ℕ} {A B : L[X]} (r_chal : L)
    (hA : A.natDegree < m) (hB : B.natDegree < m) :
    (C (1 - r_chal) * A + C r_chal * B : L[X]).natDegree < m := by
  apply natDegree_add_lt_of_lt
  · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le (1 - r_chal) A) hA
  · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le r_chal B) hB

/-- The (minimum) distance d_i of the code C^(i) : `dᵢ := 2^(ℓ + R - i) - 2^(ℓ - i) + 1` -/
abbrev BBF_CodeDistance (i : Fin r) : ℕ :=
  ‖((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))‖₀

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma BBF_CodeDistance_eq (i : Fin r) (h_i : i ≤ ℓ) :
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    = 2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1 := by
  unfold BBF_CodeDistance
  haveI : NeZero (2 ^ (ℓ - i.val)) := ⟨pow_ne_zero _ (by norm_num)⟩
  -- Create the embedding from domain elements to L
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  -- Create α : Fin m → L by composing with an equivalence
  let m := Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) i)
  have h_dist_RS := ReedSolomon.dist_eq' (F := L) (ι := (sDomain 𝔽q β h_ℓ_add_R_rate)
    (i := i)) (α := domain) (n := 2^(ℓ - i.val)) (h := by
      have hR : 0 < 𝓡 := pos_of_neZero 𝓡
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i)
        (h_i := by omega)]
      rw [hF₂.out];
      apply Nat.pow_le_pow_right (hx := by omega); omega
    )
  unfold BBF_Code
  rw [h_dist_RS]
  have hR : 0 < 𝓡 := pos_of_neZero 𝓡
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i)
    (h_i := by omega), hF₂.out]

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i) and g^(i), this is {y ∈ S^(i) | f^(i)(y) ≠ g^(i)(y)}. -/
def disagreementSet (i : Fin r)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  {(y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) |
    f (cast (by subst h_destIdx_eq_i; rfl) y) ≠ g (cast (by subst h_destIdx_eq_i; rfl) y)}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  if h_steps : steps = 0 then
    disagreementSet 𝔽q β (i := i) (destIdx := destIdx) (h_destIdx := by omega) f g
  else
    Finset.univ.filter fun _y => ∃ x, f x ≠ g x

/-- Honest per-fiber disagreement set.

Unlike the legacy `fiberwiseDisagreementSet`, the positive-step predicate depends on the
quotient point `y`: `y` is bad exactly when some point in the iterated quotient fiber over
`y` has different `f` and `g` values. This is the surface needed by the Proposition 4.21
case-1 union-bound argument. -/
def fiberwiseDisagreementSetPerFiber (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  Finset.univ.filter fun y =>
    ∃ idx : Fin (2 ^ steps),
      fiberEvaluations 𝔽q β (i := i) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f y idx ≠
      fiberEvaluations 𝔽q β (i := i) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le g y idx

@[simp]
lemma mem_fiberwiseDisagreementSetPerFiber
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    y ∈ fiberwiseDisagreementSetPerFiber 𝔽q β (i := i) (destIdx := destIdx)
      (steps := steps) h_destIdx h_destIdx_le f g ↔
      ∃ idx : Fin (2 ^ steps),
        fiberEvaluations 𝔽q β (i := i) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le f y idx ≠
        fiberEvaluations 𝔽q β (i := i) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le g y idx := by
  simp [fiberwiseDisagreementSetPerFiber]

lemma fiberwiseDisagreementSetPerFiber_subset_legacy_of_ne_zero
    (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_steps : steps ≠ 0)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseDisagreementSetPerFiber 𝔽q β (i := i) (destIdx := destIdx)
      (steps := steps) h_destIdx h_destIdx_le f g ⊆
    fiberwiseDisagreementSet 𝔽q β (i := i) (destIdx := destIdx)
      (steps := steps) h_destIdx h_destIdx_le f g := by
  intro y hy
  rw [mem_fiberwiseDisagreementSetPerFiber] at hy
  rcases hy with ⟨idx, hne⟩
  unfold fiberEvaluations at hne
  have h_exists : ∃ x, f x ≠ g x := ⟨_, hne⟩
  simp [fiberwiseDisagreementSet, h_steps, h_exists]

lemma fiberwiseDisagreementSet_congr_sourceDomain_index (sourceIdx₁ sourceIdx₂ : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
  (h_destIdx : destIdx = sourceIdx₁.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx₁) :
  -- have h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂ := Fin.ext h_sourceIdx_eq_sourceIdx₂
  let Δ_fiber₁ := fiberwiseDisagreementSet 𝔽q β sourceIdx₁ steps h_destIdx h_destIdx_le f g
  let Δ_fiber₂ := fiberwiseDisagreementSet 𝔽q β sourceIdx₂ steps (by omega) h_destIdx_le (fun x => f (cast (by subst h_sourceIdx_eq; rfl) x)) (fun x => g (cast (by subst h_sourceIdx_eq; rfl) x))
  Δ_fiber₁ = Δ_fiber₂ := by
  subst h_sourceIdx_eq
  rfl

/-- When `steps = 0`, the fiberwise disagreement set (projecting to `S^{i+0} = S^i`)
equals the ordinary pointwise disagreement set.
Both sides are stated with `destIdx := i` so they share the same `Finset` type. -/
@[simp]
lemma fiberwiseDisagreementSet_steps_zero_eq_disagreementSet
    (i destIdx : Fin r) (h_destIdx : destIdx = i.val + 0) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseDisagreementSet 𝔽q β i (steps := 0) (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f g =
    disagreementSet 𝔽q β (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx) f g := by
  have h_destIdx_eq_i : destIdx = i := Fin.ext (by omega)
  subst h_destIdx_eq_i
  simpa [fiberwiseDisagreementSet, disagreementSet]

def pair_fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
  (fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (destIdx := destIdx) (steps := steps)
    h_destIdx h_destIdx_le f g).card

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
  let C_i : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  sInf ((fun g : C_i =>
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g) '' Set.univ)

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i) : Prop :=
  (2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)) ∧
  2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := destIdx) (steps := steps) h_destIdx h_destIdx_le f <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)

def pair_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := destIdx) (steps := steps) h_destIdx h_destIdx_le f g <
    BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)

lemma exists_fiberwiseClosestCodeword (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (destIdx := destIdx) (steps := steps) h_destIdx h_destIdx_le f =
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (destIdx := destIdx) (steps := steps) h_destIdx h_destIdx_le f g := by
  classical
  simp only [SetLike.mem_coe]
  let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  let C_i : Set (S_i → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let values : Set ℕ := (fun g : C_i =>
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g) '' Set.univ
  have hvalues_nonempty : values.Nonempty := by
    exact Set.image_nonempty.mpr Set.univ_nonempty
  have hsInf_mem : sInf values ∈ values := Nat.sInf_mem hvalues_nonempty
  rw [Set.mem_image] at hsInf_mem
  rcases hsInf_mem with ⟨g, _, hg⟩
  refine ⟨g, g.property, ?_⟩
  dsimp [fiberwiseDistance, values, C_i] at hg ⊢
  exact hg.symm

/-- Hamming UDR-closeness : f is close to C in Hamming distance if `2 * d(f, C) < d_i` -/
def UDRClose (i : Fin r) (h_i : i ≤ ℓ) (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Prop :=
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

def pair_UDRClose (i : Fin r) (h_i : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Δ₀(f, g) < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

section ConstantFunctions

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma constFunc_mem_BBFCode {i : Fin r} (h_i : i ≤ ℓ) (c : L) :
    (fun _ => c) ∈ (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i))
  := by
  unfold BBF_Code
  simp only
  simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map]
  use Polynomial.C c
  constructor
  · rw [Polynomial.mem_degreeLT]
    apply lt_of_le_of_lt (Polynomial.degree_C_le)
    norm_num
  · ext x; simp only [Polynomial.eval_C]

lemma constFunc_UDRClose {i : Fin r} (h_i : i ≤ ℓ) (c : L) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i (fun _ => c) := by
  unfold UDRClose
  have hdist_zero :
      Δ₀((fun _ => c),
        (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :
          Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))) = 0 := by
    apply le_antisymm
    · exact le_trans
        (distFromCode_le_dist_to_mem (fun _ => c) (fun _ => c)
          (constFunc_mem_BBFCode 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_i c))
        (by simp)
    · exact bot_le
  rw [hdist_zero]
  rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (h_i := h_i)]
  norm_num

end ConstantFunctions
omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma UDRClose_iff_within_UDR_radius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f ↔
    Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
      uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
        (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRClose
  have hR : 0 < 𝓡 := pos_of_neZero 𝓡
  let card_Sᵢ := sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)
  conv_rhs =>
    unfold BBF_Code;
    rw [ReedSolomon.uniqueDecodingRadius_RS_eq' (h := by
      rw [card_Sᵢ, hF₂.out]; apply Nat.pow_le_pow_right (hx := by omega); omega
    )];
  simp_rw [card_Sᵢ, hF₂.out, BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
  simp only [cast_add, ENat.coe_sub, cast_pow, cast_ofNat, cast_one]
  constructor

  · intro h_UDRClose
    -- 1. Prove distance is finite
    -- The hypothesis implies 2 * Δ₀ is finite, so Δ₀ must be finite.
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      rw [h_top] at h_UDRClose
      exact not_top_lt h_UDRClose
    -- 2. Lift to Nat to use standard arithmetic
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq
    dsimp only [BBF_Code] at h_eq
    simp_rw [←h_eq]
    -- ⊢ ↑d_nat ≤ ↑((2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i)) / 2)
    have h_lt : 2 * d_nat < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 := by
      norm_cast at h_UDRClose ⊢ -- both h_UDRClose and ⊢ are in ENat
    simp only [Nat.cast_le]
    have h_le := Nat.le_of_lt_succ (m := 2 * d_nat) (n := 2^(ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) ) h_lt
    rw [Nat.mul_comm 2 d_nat] at h_le
    rw [←Nat.le_div_iff_mul_le (k0 := by norm_num)] at h_le
    exact h_le
  · intro h_within
    -- 1. Prove finite
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      unfold BBF_Code at h_top
      simp only [h_top, top_le_iff, ENat.coe_ne_top] at h_within

    -- 2. Lift to Nat
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq

    unfold BBF_Code at h_eq
    rw [←h_eq] at h_within
    norm_cast at h_within ⊢
    -- now both h_within and ⊢ are in ENat, equality can be converted
    omega

/-- Unique closest codeword in the unique decoding radius of a function f -/
@[reducible, simp]
def UDRCodeword (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
   := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  -- h_ExistsUnique : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i)
    -- ∧ Δ₀(f, v) ≤ Code.uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  exact (Classical.choose h_ExistsUnique)

open Classical in
lemma UDRCodeword_eq_of_close
    (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h₁ h₂ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h₁ =
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h₂ := by
  let C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let h₁' := (Code.UDR_close_iff_exists_unique_close_codeword (C := C) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h₁
    exact h₁)
  let h₂' := (Code.UDR_close_iff_exists_unique_close_codeword (C := C) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h₂
    exact h₂)
  exact (Classical.choose_spec h₁').2
    (Classical.choose h₂') (Classical.choose_spec h₂').1

lemma UDRCodeword_constFunc_eq_self (i : Fin r) (h_i : i ≤ ℓ) (c : L) :
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_i (f := fun _ => c)
    (h_within_radius := by apply constFunc_UDRClose) = fun _ => c := by
  let hclose : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i (fun _ => c) :=
    constFunc_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_i c
  let C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let huniq := (Code.UDR_close_iff_exists_unique_close_codeword (C := C) (fun _ => c)).mp (by
    rw [UDRClose_iff_within_UDR_radius] at hclose
    exact hclose)
  exact ((Classical.choose_spec huniq).2 (fun _ => c)
    ⟨constFunc_mem_BBFCode 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_i c,
      by simp [hammingDist]⟩).symm

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma UDRCodeword_mem_BBF_Code (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp]
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  let res := (Classical.choose_spec h_ExistsUnique).1.1
  simp only [SetLike.mem_coe, and_imp] at res
  exact res

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma dist_to_UDRCodeword_le_uniqueDecodingRadius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  Δ₀(f, UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ≤
    uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
      (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  ) -- res : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i) ∧ Δ₀(f, v) ≤ uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  let res := (Classical.choose_spec h_ExistsUnique).1
  simp only [Fin.eta, SetLike.mem_coe, and_imp] at res
  let h_close := res.2
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp, ge_iff_le]
  exact h_close

/-- Computational version of `UDRCodeword`, where we use the Berlekamp-Welch decoder to extract
the closest codeword within the unique decoding radius of a function `f` -/
def extractUDRCodeword
    (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
   :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius

/-
  -- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate i)
  set d := Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  let e : ℕ := d.toNat
  have h_dist_ne_top : d ≠ ⊤ := by
    intro h_dist_eq_top
    unfold UDRClose at h_within_radius
    unfold d at h_dist_eq_top
    simp only [h_dist_eq_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENat.mul_top,
      not_top_lt] at h_within_radius
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    i ≃ Fin domain_size := by
    simp only [domain_size]
    have hR : 0 < 𝓡 := pos_of_neZero 𝓡
    have hi_bound : i.val < ℓ + 𝓡 := by omega
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := hi_bound)]
    have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := i) hi_bound
    convert h_equiv
    exact hF₂.out
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    have hR : 0 < 𝓡 := pos_of_neZero 𝓡
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  let berlekamp_welch_result : Option L[X] := BerlekampWelch.decoder (F := L) e k ωs f_vals
  have h_ne_none : berlekamp_welch_result ≠ none := by
    -- 1) Choose a codeword achieving minimal Hamming distance (closest codeword).
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    let S := (fun (g : C_i) => Δ₀(f, g)) '' Set.univ
    let SENat := (fun (g : C_i) => (Δ₀(f, g) : ENat)) '' Set.univ
      -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.coe_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
    rcases g_subtype with ⟨g_closest, hg_mem⟩
    have h_dist_f : hammingDist f g_closest ≤ e := by
      rw [show e = d.toNat from rfl]
      -- The distance `d` is exactly the Hamming distance of `f` to `g_closest` (lifted to `ℕ∞`).
      have h_dist_eq_hamming : d = (hammingDist f g_closest) := by
        -- We found `g_closest` by taking the `sInf` of all distances, and `hg_min`
        -- shows that the distance to `g_closest` achieves this `sInf`.
        have h_distFromCode_eq_sInf : d = sInf SENat := by
          apply le_antisymm
          · -- Part 1 : `d ≤ sInf ...`
            simp only [d, distFromCode]
            apply sInf_le_sInf
            intro a ha
            -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
            rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
            -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
            -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
            use g; simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]
          · -- Part 2 : `sInf ... ≤ d`
            simp only [d, distFromCode]
            apply le_sInf
            -- Let `d'` be any element in the set that `d` is the infimum of.
            intro d' h_d'
            -- Unpack `h_d'` : there exists some `v` in the code such that
            -- `↑(hammingDist f v) ≤ d'`.
            rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
            -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
            -- The element `↑(hammingDist f v)` is in `SENat`.
            have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
              apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
              rw [Set.mem_image]
              -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
              simp only [Fin.eta, Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
              -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
              use v
              exact And.symm ⟨rfl, hv_mem⟩
            -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
            exact h_sInf_le_dist_v.trans h_dist_v_le_d'
        rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
      rw [h_dist_eq_hamming]
      rw [ENat.toNat_coe]
    -- Get the closest polynomial
    obtain ⟨p, hp_deg_lt, hp_eval⟩ : ∃ p : L[X], p ∈ Polynomial.degreeLT L k ∧
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i)) ↦ p.eval (↑x)) = g_closest := by
      simp only [Fin.eta, BBF_Code, code, evalOnPoints, Function.Embedding.coeFn_mk,
        Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk, C_i] at hg_mem
      rcases hg_mem with ⟨p_witness, hp_prop, hp_eq⟩
      use p_witness
      exact ⟨hp_prop, hp_eq.symm⟩
    have natDeg_p_lt_k : p.natDegree < k := by
      simp only [mem_degreeLT] at hp_deg_lt
      by_cases hi : i = ℓ
      · simp only [hi, tsub_self, pow_zero, cast_one, lt_one_iff, k] at ⊢ hp_deg_lt
        by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
        · rw [Polynomial.natDegree_eq_of_degree_eq_some]
          have h_deg_p : p.degree = 0 := by
            have h_le_zero : p.degree ≤ 0 := by
              exact WithBot.lt_one_iff_le_zero.mp hp_deg_lt
            have h_deg_ne_bot : p.degree ≠ ⊥ := by
              rw [Polynomial.degree_ne_bot]; omega
            apply le_antisymm h_le_zero (zero_le_degree_iff.mpr hp_p_eq_0)
          simp only [h_deg_p, CharP.cast_eq_zero]
      · by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
          have h_i_lt_ℓ : i < ℓ := by omega
          simp only [ofNat_pos, pow_pos, k]
        · rw [Polynomial.natDegree_lt_iff_degree_lt (by omega)]
          exact hp_deg_lt
    have h_decoder_succeeds : BerlekampWelch.decoder e k ωs f_vals = some p := by
      apply BerlekampWelch.decoder_eq_some
      · -- ⊢ `2 * e < d_i = n - k + 1`
        have h_le: 2 * e ≤ domain_size - k := by
          have hS_card_eq_domain_size := sDomain_card 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := Sdomain_bound (by omega))
          simp only [domain_size, k]; simp_rw [hS_card_eq_domain_size, hF₂.out]
          unfold UDRClose at h_within_radius
          rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)] at h_within_radius
          -- h_within_radius : 2 * Δ₀(f, ↑(BBF_Code 𝔽q β i))
            -- < ↑(2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1)
          dsimp only [Fin.eta, e, d]
          lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
            using h_dist_ne_top with d_nat h_eq
          norm_cast at h_within_radius
          simp only [ENat.toNat_coe, ge_iff_le]
          omega
        omega
      · -- ⊢ `k ≤ domain_size`. This holds by the problem setup.
        simp only [k, domain_size]
        rw [sDomain_card 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := Sdomain_bound (by omega)), hF₂.out]
        apply Nat.pow_le_pow_right (by omega) -- ⊢ ℓ - ↑i ≤ ℓ + 𝓡 - ↑⟨↑i, ⋯⟩
        simp only [tsub_le_iff_right]
        omega
      · -- ⊢ Function.Injective ωs
        simp only [ωs]
        -- The composition of two injective functions (`Equiv.symm` and `Subtype.val`) is injective.
        exact Function.Injective.comp Subtype.val_injective (Equiv.injective _)
      · -- ⊢ `p.natDegree < k`. This is true from `hp_deg`.
        exact natDeg_p_lt_k
      · -- ⊢ `Δ₀(f_vals, (fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e`
        change hammingDist f_vals ((fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e
        simp only [ωs]
        have h_functions_eq : (fun a ↦ Polynomial.eval a p) ∘ ωs
          = g_closest ∘ domain_to_fin.symm := by
          ext j; simp only [Function.comp_apply, Fin.eta, ωs]
          rw [←hp_eval]
        rw [h_functions_eq]
        -- ⊢ Δ₀(f_vals, g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        simp only [Fin.eta, ge_iff_le, f_vals]
        -- ⊢ Δ₀(fun j ↦ f (domain_to_fin.symm j), g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        calc
          _ ≤ hammingDist f g_closest := by
            apply hammingDist_le_of_outer_comp_injective f g_closest domain_to_fin.symm
              (hg := by exact Equiv.injective domain_to_fin.symm)
          _ ≤ e := by exact h_dist_f
    simp only [ne_eq, berlekamp_welch_result]
    simp only [h_decoder_succeeds, reduceCtorEq, not_false_eq_true]
  let p : L[X] := berlekamp_welch_result.get (Option.ne_none_iff_isSome.mp h_ne_none)
  exact fun x => p.eval x.val
-/

omit [CharP L 2] in
/-
/-- `Δ₀(f, g) ≤ pair_fiberwiseDistance(f, g) * 2 ^ steps` -/
lemma hammingDist_le_fiberwiseDistance_mul_two_pow_steps (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i):
    Δ₀(f, g) ≤ (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)) * 2 ^ steps := by
  let d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g ≤ (fiberwiseDisagreementSet ... f g).ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g ≤ ...`,
    -- which is equivalent.
    -- Let ΔH be the finset of actually bad x points where f and g disagree.
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g
    simp only at * -- simplify domain indices everywhere
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad
        (t := fun y => ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      -- ⊢ If any x ∈ ΔH, then x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ qMap_total_fiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) h_destIdx h_destIdx_le x
      apply Finset.mem_biUnion.mpr; use y_of_x
      -- ⊢ y_of_x ∈ Y_bad.toFinset ∧ x ∈ qMap_total_fiber(y_of_x)
      have h_elemenet_Y_bad :  y_of_x ∈ Y_bad := by
        -- ⊢ y ∈ Y_bad
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists, mem_filter,
          mem_univ, true_and, Y_bad]
        -- one bad fiber point of y_of_x is x itself
        let XX := x.val
        have h_XX_in_source : XX ∈ sDomain 𝔽q β h_ℓ_add_R_rate (i := i) := by
          exact Submodule.coe_mem x
        use XX
        use h_XX_in_source
        -- ⊢ Ŵ_steps⁽ⁱ⁾(XX) = y (iterated quotient map) ∧ ¬f ⟨XX, ⋯⟩ = g ⟨XX, ⋯⟩
        have h_forward_iterated_qmap : Polynomial.eval XX
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i
              (k := steps) (h_k := by omega)) = y_of_x := by
          simp only [iteratedQuotientMap, XX, y_of_x];
        have h_eval_diff : f ⟨XX, by omega⟩ ≠ g ⟨XX, by omega⟩ := by
          unfold XX
          simp only [Subtype.coe_eta, ne_eq, hx_in_ΔH, not_false_eq_true]
        simp only [h_forward_iterated_qmap, Subtype.coe_eta, h_eval_diff,
          not_false_eq_true, and_self]
      simp only [h_elemenet_Y_bad, true_and]

      set qMapFiber := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le (y := y_of_x)
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x))
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    -- The cardinality of a subset is at most the cardinality of the superset.
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      -- ⊢ ∑ x ∈ Y_bad.toFinset, 2 ^ steps ≤ Y_bad.encard.toNat * 2 ^ steps
      simp only [sum_const, smul_eq_mul, ofNat_pos, pow_pos, _root_.mul_le_mul_right, ge_iff_le]
      -- ⊢ Fintype.card ↑Y_bad ≤ Nat.card ↑Y_bad
      simp only [Y_bad, d_fw, pair_fiberwiseDistance, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := qMap_total_fiber_disjoint (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y₁ := y₁) (y₂ := y₂) (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint
  exact h_dist_le_fw_dist_times_fiber_size

omit [CharP L 2] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
lemma pairUDRClose_of_pairFiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (by omega) (f := f)
      (g := g) := by
  unfold pair_fiberwiseClose at h_fw_dist_lt
  norm_cast at h_fw_dist_lt
  unfold pair_UDRClose
  set d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  set d_cur := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  -- d_cur = 2 ^ (ℓ + 𝓡 - i) - 2 ^ (ℓ - i) + 1
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  -- d_next = 2 ^ (ℓ + 𝓡 - (i + steps)) - 2 ^ (ℓ - (i + steps)) + 1

  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    apply hammingDist_le_fiberwiseDistance_mul_two_pow_steps
  -- h_fw_dist_lt : 2 * d_fw < BBF_CodeDistance 𝔽q β ⟨↑i + steps, ⋯⟩
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega

  have h_2_fw_dist_mul_2_pow_steps_le :
    2 * (d_fw * 2 ^ steps) ≤ (d_next * 2 ^ steps - 2 ^ steps):= by
    rw [←mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [←one_mul (2 ^ steps)];
      rw [←Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)];
    apply Nat.mul_le_mul_right
    exact h_2_fw_dist_le

  have h_2_fw_dist_mul_2_pow_steps_le : (d_next * 2 ^ steps - 2 ^ steps) = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega), BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul]
    rw [←Nat.pow_add, ←Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - destIdx + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - destIdx + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega

  have h_le_2 : 2 * (d_fw * 2 ^ steps) ≤ BBF_CodeDistance 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) - 1:= by
    omega

  apply Nat.lt_of_le_pred (h := by simp only [d_cur]; rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]; omega)
  simp only [pred_eq_sub_one]
  exact Nat.le_trans h_le h_le_2

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
lemma exists_fiberwiseClosestCodeword (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) := by
  simp only [SetLike.mem_coe]
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  -- Let `S` be the set of all possible fiber-wise disagreement sizes.
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (g := g)).card) '' Set.univ
  -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
  have hS_nonempty : S.Nonempty := by
    refine Set.image_nonempty.mpr ?_

    exact Set.univ_nonempty
  -- For a non-empty set of natural numbers, `sInf` is an element of the set.
  have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  -- By definition, `d_fw = sInf S`.
  -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
  -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
  rw [Set.mem_image] at h_sInf_mem
  rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
  -- Extract the codeword and its membership proof.
  refine ⟨g_subtype, ?_, ?_⟩
  · -- membership
    exact g_subtype.property
  · -- equality of distances
    -- `fiberwiseDistance` is defined as the infimum of `S`, so it equals `sInf S`
    -- and `h_eq` tells us that this is exactly the distance to `g_subtype`.
    -- You may need to unfold `fiberwiseDistance` here if Lean doesn't reduce it automatically.
    exact id (Eq.symm h_eq)

omit [CharP L 2] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
theorem UDRClose_of_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold UDRClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  set d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_destIdx h_destIdx_le f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  let d_H := Δ₀(f, C_i)
  let d_i := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  let d_i_plus_steps := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)

  have h_d_i_gt_0 : d_i > 0 := by
    dsimp only [d_i]-- , BBF_CodeDistance] -- ⊢ 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 > 0
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega) (by
        apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) := by
      exact Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
    omega

  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)

  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g').card := by
    apply exists_fiberwiseClosestCodeword

  have h_UDR_close_f_g' := pairUDRClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_destIdx h_destIdx_le (f := f) (g := g') (h_fw_dist_lt := by
      dsimp only [pair_fiberwiseClose, pair_fiberwiseDistance]; norm_cast;
      rw [←h_g'_min_card];
      exact (by norm_cast at h_fw_dist_lt)
    )
  -- ⊢ 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance 𝔽q β ⟨↑i, ⋯⟩)
  calc
    2 * Δ₀(f, C_i) ≤ 2 * Δ₀(f, g') := by
      rw [ENat.mul_le_mul_left_iff (ha := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])
      ]
      apply Code.distFromCode_le_dist_to_mem (C := C_i) (u := f) (v := g') (hv := h_g'_mem)
    _ < _ := by norm_cast -- use result from h_UDR_close_f_g'

omit [CharP L 2] in
/-- This expands `exists_fiberwiseClosestCodeword` to the case `f` is fiberwise-close to `C_i`. -/
lemma exists_unique_fiberwiseClosestCodeword_within_UDR (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃! (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g)) ∧
      (g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f
        (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f h_fw_close))
      := by
  set d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le f
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set S_i_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  obtain ⟨g, h_g_mem, h_g_min_card⟩ : ∃ g ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card := by
    apply exists_fiberwiseClosestCodeword
  set C_i_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  have h_neZero_dist_C_i_next : NeZero (‖(C_i_next : Set (S_i_next → L))‖₀) := {
    out := by
      unfold C_i_next
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega)]
      omega
  }
  have h_neZero_dist_C_i : NeZero (‖(C_i : Set (S_i → L))‖₀) := {
    out := by
      unfold C_i
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
      omega
  }
  use g
  have h_f_g_UDR_close : Δ₀(f, g) ≤ Code.uniqueDecodingRadius (F := L)
    (ι := S_i) (C := C_i) := by -- This relies on `h_fw_close`
    unfold fiberwiseClose at h_fw_close
    norm_cast at h_fw_close
    rw [←Code.UDRClose_iff_two_mul_proximity_lt_d_UDR] at h_fw_close
    unfold d_fw at h_g_min_card
    rw [h_g_min_card] at h_fw_close
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := #(fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i_next : Set (S_i_next → L))‖₀))] at h_fw_close
    -- h_fw_close : 2 * #(fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g)
    --   < ‖↑(BBF_Code 𝔽q β ⟨↑i + steps, ⋯⟩)‖₀
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := Δ₀(f,g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i : Set (S_i → L))‖₀))]
    -- 2 * Δ₀(f, g) < ‖↑(C_i)‖₀
    let res := pairUDRClose_of_pairFiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) (h_fw_dist_lt := by
      unfold pair_fiberwiseClose pair_fiberwiseDistance
      norm_cast
    )
    exact res

  let h_f_UDR_close := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f h_fw_close
  have h_g_eq_UDRCodeword : g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i (h_i := by omega) f h_f_UDR_close := by
    apply Code.eq_of_le_uniqueDecodingRadius (C := C_i) (u := f)
      (v := g) (w := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f h_f_UDR_close) (hv := h_g_mem) (hw := by apply UDRCodeword_mem_BBF_Code (i := i) (f := f) (h_within_radius := h_f_UDR_close))
      (huv := by
        -- ⊢ Δ₀(f, g) ≤ uniqueDecodingRadius ↑C_i
        exact h_f_g_UDR_close
      )
      (huw := by
        apply dist_to_UDRCodeword_le_uniqueDecodingRadius (i := i) (f := f) (h_within_radius := h_f_UDR_close)
      )
  simp only
  constructor
  · constructor
    · exact h_g_mem
    · constructor
      · exact h_g_min_card
      · -- ⊢ g = UDRCodeword 𝔽q β ⟨↑i, ⋯⟩ f ⋯
        exact h_g_eq_UDRCodeword
  · -- trivial contrapositive case
    intro y hy_mem_C_i
    rw [h_g_eq_UDRCodeword]
    rw [hy_mem_C_i.2.2]

/-- **Lemma: Single Step BBF_Code membership preservation**
It establishes that folding a codeword from the i-th code produces a codeword in the (i+1)-th code.
This relies on **Lemma 4.13** that 1-step folding advances the evaluation polynomial. -/
lemma fold_preserves_BBF_Code_membership (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_destIdx h_destIdx_le (f := f) (r_chal := r_chal)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  -- 1. Unwrap the code definition to get the polynomial P
  -- BBF_Code is ReedSolomon, so f comes from some P with deg < 2^(ℓ-i)
  set C_cur := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L)) with h_C_cur
  have h_f_mem : f.val ∈ C_cur := by
    unfold C_cur
    simp only [Subtype.coe_prop]
  simp only [BBF_Code, code, C_cur] at h_f_mem
  rcases h_f_mem with ⟨P, hP_deg, hP_eval⟩ -- the poly that generates `f` on `S^(i)`
  let iNovel_coeffs : Fin (2^(ℓ - i)) → L :=
    getINovelCoeffs 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (P := P)
  simp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk] at hP_eval
  simp only [SetLike.mem_coe, mem_degreeLT, cast_pow, cast_ofNat] at hP_deg
  -- ⊢ Fin (2 ^ (ℓ - ↑i)) → L
  simp only [BBF_Code, code, Submodule.mem_map]
  set new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
  (1 - r_chal) * (iNovel_coeffs ⟨j.val * 2, by
    rw [←Nat.add_zero (j.val * 2)]
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 0) (by omega) (by omega)
  ⟩) +
  r_chal * (iNovel_coeffs ⟨j.val * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 1) (by omega) (by omega)
  ⟩)
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  use P_i_plus_1
  constructor
  · -- ⊢ P_i_plus_1 ∈ L[X]_(2 ^ (ℓ - (↑i + 1)))
    apply Polynomial.mem_degreeLT.mpr
    unfold P_i_plus_1
    apply degree_intermediateEvaluationPoly_lt
  · -- ⊢ (evalOnPoints ... P_i_plus_1) = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (coeffs := iNovel_coeffs) (r_chal := r_chal)
    simp only at fold_advances_evaluation_poly_res
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    dsimp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk]
    -- ⊢ Polynomial.eval (↑y) P_i_plus_1 = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal y
    unfold polyToOracleFunc at fold_advances_evaluation_poly_res
    let lhs_eq := congrFun fold_advances_evaluation_poly_res y
    conv_lhs => rw [←lhs_eq]
    -- simp only [Subtype.coe_eta]
    congr 1
    funext (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i)
    -- ⊢ Polynomial.eval (↑x) (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      -- ⟨↑i, ⋯⟩ iNovel_coeffs) = ↑f x
    unfold intermediateEvaluationPoly iNovel_coeffs
    let res := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (P := P) (hP_deg := hP_deg)
    unfold intermediateEvaluationPoly at res
    rw [res]
    -- ⊢ Polynomial.eval (↑x) P = ↑f x
    exact (congrFun hP_eval x)

-/
/-- Fiberwise closeness is exposed as the corresponding UDR-close precondition. -/
theorem UDRClose_of_fiberwiseClose (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f :=
  h_fw_dist_lt.1

/-- **Single-step BBF code membership preservation** (the Lemma 4.13 consequence): folding a
codeword of the `i`-th code produces a codeword of the `destIdx = i + 1`-st code. -/
theorem fold_preserves_BBF_Code_membership
    (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
      h_destIdx h_destIdx_le (f := f) (r_chal := r_chal)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  classical
  obtain ⟨Psub, hPsub_eval⟩ := exists_BBF_poly_of_codeword
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f
  let P : L[X] := Psub.val
  have hP_eval_fun :
      (fun x : sDomain 𝔽q β h_ℓ_add_R_rate i => P.eval x.val) = f := by
    simpa [P, polyToOracleFunc] using hPsub_eval
  have ha_lt0 : i.val + 1 < r := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have hdest : destIdx = (⟨i.val + 1, ha_lt0⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst hdest
  let m : ℕ := 2 ^ (ℓ - (i.val + 1))
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.two_pow_pos _
  have hPnat : P.natDegree < 2 * m := by
    have hPdeg := natDegree_of_mem_degreeLT (L := L)
      (n := 2 ^ (ℓ - i.val)) (by exact Nat.two_pow_pos _) (P := P) Psub.property
    have hpow : 2 ^ (ℓ - i.val) = 2 * m := by
      dsimp [m]
      have hsub : ℓ - i.val = ℓ - (i.val + 1) + 1 := by omega
      rw [hsub, pow_succ, Nat.mul_comm]
    simpa [hpow] using hPdeg
  obtain ⟨A, B, hA, hB, hPdecomp⟩ :=
    qMap_quadratic_decomp_of_natDegree_lt (𝔽q := 𝔽q) (β := β)
      (i := i) (m := m) hm P hPnat
  let Q : L[X] := C (1 - r_chal) * A + C r_chal * B
  unfold BBF_Code
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  refine ⟨Q, ?_, ?_⟩
  · have hQnat : Q.natDegree < m :=
      natDegree_C_mul_add_C_mul_lt (r_chal := r_chal) hA hB
    by_cases hQzero : Q = 0
    · rw [hQzero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hQdeg := (Polynomial.natDegree_lt_iff_degree_lt hQzero).1 hQnat
      simpa [m] using hQdeg
  · ext y
    dsimp [ReedSolomon.evalOnPoints]
    unfold fold
    simp only [cast_eq]
    rw [← fold_legacy_eval_qMap_decomp (𝔽q := 𝔽q) (β := β)
      (i := i) (h_i := by have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡; omega)
      (h_le := by omega)
      (A := A) (B := B) (P := P) hPdecomp (r_chal := r_chal) (y := y)]
    rw [hP_eval_fun]

/-- Two destination codewords can be unfolded to one source codeword whose binary folds are them.

This is the one-step surjectivity counterpart to `fold_preserves_BBF_Code_membership`: if
`u₀ = A` and `u₁ = B` are destination Reed-Solomon words, then the source polynomial
`A(qᵢ(X)) + X B(qᵢ(X))` folds to `u₀` at challenge `0` and to `u₁` at challenge `1`. -/
theorem exists_unfold_of_binary_BBF_Codewords
    (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (u₀ u₁ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (hu₀ : u₀ ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (hu₁ : u₁ ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    ∃ g, g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ∧
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
        h_destIdx h_destIdx_le g 0 = u₀ ∧
      fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
        h_destIdx h_destIdx_le g 1 = u₁ := by
  classical
  have ha_lt0 : i.val + 1 < r := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have hdest : destIdx = (⟨i.val + 1, ha_lt0⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst destIdx
  let destIdx' : Fin r := ⟨i.val + 1, ha_lt0⟩
  let u₀cw : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx' :=
    ⟨u₀, by simpa [destIdx'] using hu₀⟩
  let u₁cw : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx' :=
    ⟨u₁, by simpa [destIdx'] using hu₁⟩
  obtain ⟨A_sub, hA_eval⟩ := exists_BBF_poly_of_codeword
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx' u₀cw
  obtain ⟨B_sub, hB_eval⟩ := exists_BBF_poly_of_codeword
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx' u₁cw
  let A : L[X] := A_sub.val
  let B : L[X] := B_sub.val
  let P : L[X] := A.comp (qMap 𝔽q β i) + X * B.comp (qMap 𝔽q β i)
  let m : ℕ := 2 ^ (ℓ - destIdx'.val)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact Nat.two_pow_pos _
  have hi_le : i ≤ ℓ := by omega
  have hpow : 2 ^ (ℓ - i.val) = 2 * m := by
    dsimp [m]
    have hsub : ℓ - i.val = ℓ - destIdx'.val + 1 := by omega
    rw [hsub, pow_succ, Nat.mul_comm]
  have hA_nat : A.natDegree < m := by
    exact natDegree_of_mem_degreeLT (L := L) hm_pos A_sub.property
  have hB_nat : B.natDegree < m := by
    exact natDegree_of_mem_degreeLT (L := L) hm_pos B_sub.property
  have hA_comp : (A.comp (qMap 𝔽q β i)).natDegree < 2 * m := by
    rw [Polynomial.natDegree_comp, qMap_natDegree (𝔽q := 𝔽q) (β := β) (i := i)]
    omega
  have hB_comp_le : (B.comp (qMap 𝔽q β i)).natDegree ≤ B.natDegree * 2 := by
    rw [Polynomial.natDegree_comp, qMap_natDegree (𝔽q := 𝔽q) (β := β) (i := i)]
  have hX_B_comp : (X * B.comp (qMap 𝔽q β i)).natDegree < 2 * m := by
    calc
      (X * B.comp (qMap 𝔽q β i)).natDegree
          ≤ (X : L[X]).natDegree + (B.comp (qMap 𝔽q β i)).natDegree :=
            Polynomial.natDegree_mul_le
      _ ≤ 1 + B.natDegree * 2 := by
            rw [Polynomial.natDegree_X]
            omega
      _ < 2 * m := by omega
  have hP_nat : P.natDegree < 2 ^ (ℓ - i.val) := by
    dsimp [P]
    rw [hpow]
    exact natDegree_add_lt_of_lt hA_comp hX_B_comp
  let P_sub : L⦃< 2 ^ (ℓ - i.val)⦄[X] := ⟨P, by
    apply Polynomial.mem_degreeLT.mpr
    by_cases hPzero : P = 0
    · rw [hPzero, Polynomial.degree_zero, hpow]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt hPzero).1 hP_nat⟩
  let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P_sub)
  have hg_mem : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    unfold BBF_Code
    rw [ReedSolomon.mem_code_iff_exists_polynomial]
    exact ⟨P, Polynomial.mem_degreeLT.mp P_sub.2, by
      ext y
      simp [g, P_sub, polyToOracleFunc, ReedSolomon.evalOnPoints]⟩
  refine ⟨g, hg_mem, ?_, ?_⟩
  · funext y
    have hA_fun :
        (fun y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx' => A.eval y.val) = u₀ := by
      simpa [A, u₀cw, polyToOracleFunc] using hA_eval
    unfold fold
    simp only [cast_eq, g, polyToOracleFunc]
    change fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := by have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡; omega)
        (f := fun x => P.eval x.val) (r_chal := 0) y = u₀ y
    rw [fold_legacy_eval_qMap_decomp (𝔽q := 𝔽q) (β := β)
      (i := i) (h_i := by have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡; omega)
      (h_le := by omega) (A := A) (B := B) (P := P) (by rfl)
      (r_chal := 0) (y := y)]
    simpa using congrFun hA_fun y
  · funext y
    have hB_fun :
        (fun y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx' => B.eval y.val) = u₁ := by
      simpa [B, u₁cw, polyToOracleFunc] using hB_eval
    unfold fold
    simp only [cast_eq, g, polyToOracleFunc]
    change fold_legacy 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := by have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡; omega)
        (f := fun x => P.eval x.val) (r_chal := 1) y = u₁ y
    rw [fold_legacy_eval_qMap_decomp (𝔽q := 𝔽q) (β := β)
      (i := i) (h_i := by have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡; omega)
      (h_le := by omega) (A := A) (B := B) (P := P) (by rfl)
      (r_chal := 1) (y := y)]
    simpa using congrFun hB_fun y

/-- A fiberwise-closest source codeword exists whenever the close-branch hypothesis is available. -/
lemma exists_fiberwiseClosestCodeword_within_close (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g)) := by
  exact exists_fiberwiseClosestCodeword 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f

/-- Nat-indexed helper for `iterated_fold_preserves_BBF_Code_membership`.

The induction step peels the final fold using `iterated_fold_last` from `Prelude`, then applies the
single-step polynomial preservation lemma above. -/
private lemma iterated_fold_preserves_BBF_Code_membership_nat
    (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (r_challenges : Fin steps → L) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  induction steps generalizing destIdx with
  | zero =>
      have h_destIdx_eq_i : destIdx = i := Fin.eq_of_val_eq (by simpa using h_destIdx)
      subst destIdx
      have h_fold_eq :
          iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := i) (steps := 0) (destIdx := i)
            (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
            (f := f) (r_challenges := r_challenges) =
          (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
        funext y
        rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (destIdx := i) (h_destIdx := by omega)
          (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges) y]
        simp only [eq_mp_eq_cast, cast_eq]
      rw [h_fold_eq]
      exact f.property
  | succ n ih =>
      let midIdx : Fin r := ⟨i.val + n, by
        have hle : i.val + (n + 1) ≤ ℓ := by
          rw [← h_destIdx]
          exact h_destIdx_le
        exact Nat.lt_of_le_of_lt (by omega) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩
      have h_midIdx : midIdx.val = i.val + n := by
        simp only [midIdx]
      have h_midIdx_le : midIdx ≤ ℓ := by
        have hle : i.val + (n + 1) ≤ ℓ := by
          rw [← h_destIdx]
          exact h_destIdx_le
        simp only [midIdx]
        omega
      have h_folded_n_mem :
          (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := i) (steps := n) (destIdx := midIdx)
            (h_destIdx := by omega) (h_destIdx_le := by omega)
            (f := f) (r_challenges := Fin.init r_challenges)) ∈
            (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx) := by
        simpa using ih (destIdx := midIdx) (by omega) h_midIdx_le (Fin.init r_challenges)
      let f_mid : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx) :=
        ⟨iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (steps := n) (destIdx := midIdx)
          (h_destIdx := by omega) (h_destIdx_le := by omega)
          (f := f) (r_challenges := Fin.init r_challenges), h_folded_n_mem⟩
      rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (midIdx := midIdx) (destIdx := destIdx) (steps := n)
        (h_midIdx := h_midIdx) (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)]
      exact Binius.BinaryBasefold.fold_preserves_BBF_Code_membership 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (destIdx := destIdx)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
        (f := f_mid) (r_chal := r_challenges (Fin.last n))

/-- Folding a BBF codeword across rounds preserves BBF-code membership. -/
lemma iterated_fold_preserves_BBF_Code_membership
    (i : Fin r) {destIdx : Fin r}
    (steps : Fin (ℓ + 1)) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (h_destIdx : destIdx = ⟨i.val + steps.val, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (r_challenges : Fin steps → L) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps.val) (destIdx := destIdx)
      (h_destIdx := by simpa using congrArg Fin.val h_destIdx)
      (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  have h_mem := iterated_fold_preserves_BBF_Code_membership_nat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
    (steps := steps.val) (h_destIdx := by simpa using congrArg Fin.val h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)
  simpa using h_mem

-- NOTE: `isCompliant`, `farness_implies_non_compliance`, `fold_error_containment`,
-- `fold_error_containment_of_UDRClose`, and `foldingBadEvent` were moved to
-- `ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance` (the canonical home) to avoid
-- duplicate declarations across the split modules. See that module for the current
-- definitions; this file only provides the code/fiber primitives they build on.

end SoundnessTools
end Binius.BinaryBasefold
