/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.FinalConstantWeld

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

/-- Two single-step folds at both binary challenges pin the two fiber values:
the butterfly system has determinant `x₁ − x₀ ≠ 0`. -/
lemma fold_legacy_binary_inj (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (F G : sDomain 𝔽q β h_ℓ_add_R_rate i → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩)
    (h0 : fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := F) (r_chal := (0 : L)) y =
          fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := G) (r_chal := (0 : L)) y)
    (h1 : fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := F) (r_chal := (1 : L)) y =
          fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := G) (r_chal := (1 : L)) y)
    (c : Fin 2) :
    F (qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) c) =
    G (qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) c) := by
  have hsub := qMap_total_fiber_one_sub 𝔽q β i h_i h_le y
  -- name the fiber points and values
  set x₀ := qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 0
    with hx₀
  set x₁ := qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 1
    with hx₁
  have hd : (↑x₁ : L) - (↑x₀ : L) ≠ 0 := by
    rw [← AddSubgroupClass.coe_sub, hsub]
    have hb := (sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega)).ne_zero
      ⟨0, by omega⟩
    exact fun hc => hb (by exact_mod_cast Subtype.ext hc)
  unfold fold_legacy at h0 h1
  simp only [one_mul, zero_mul, sub_zero, mul_zero, zero_sub, sub_self] at h0 h1
  -- h0 : F x₀ * x₁ - ... the exact normal forms will be fixed at compile time
  set a := F x₀ - G x₀ with ha
  set b := F x₁ - G x₁ with hb
  have hsys1 : a * x₁.val - b * x₀.val = 0 := by
    simp only [a, b]
    ring_nf
    ring_nf at h0
    linear_combination h0
  have hsys2 : b - a = 0 := by
    simp only [a, b]
    ring_nf
    ring_nf at h1
    linear_combination h1
  have hab : b = a := sub_eq_zero.mp hsys2
  have hzero : a * ((↑x₁ : L) - ↑x₀) = 0 := by
    rw [hab] at hsys1
    linear_combination hsys1
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hd
  have hb0 : b = 0 := by rw [hab]; exact ha0
  -- conclude per c
  fin_cases c
  · exact sub_eq_zero.mp ha0
  · exact sub_eq_zero.mp hb0

end
end Binius.BinaryBasefold

namespace Binius.BinaryBasefold
noncomputable section
open Finset AdditiveNTT Polynomial Nat

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Low bits of an index with a high bit attached. -/
lemma bitsOfIndex_combine_castSucc {s : ℕ} (jl : Fin (2 ^ s)) (c : Fin 2)
    (h : c.val * 2 ^ s + jl.val < 2 ^ (s + 1)) (b : Fin s) :
    bitsOfIndex (L := L) (⟨c.val * 2 ^ s + jl.val, h⟩ : Fin (2 ^ (s + 1))) b.castSucc =
    bitsOfIndex (L := L) jl b := by
  unfold bitsOfIndex
  simp only [Fin.coe_castSucc, Nat.getBit_eq_testBit,
    testBit_low_of_mul_two_pow_add c.val jl.val b.val jl.isLt b.isLt]

/-- The top bit of an index with a high bit attached. -/
lemma bitsOfIndex_combine_last {s : ℕ} (jl : Fin (2 ^ s)) (c : Fin 2)
    (h : c.val * 2 ^ s + jl.val < 2 ^ (s + 1)) :
    bitsOfIndex (L := L) (⟨c.val * 2 ^ s + jl.val, h⟩ : Fin (2 ^ (s + 1))) (Fin.last s) =
    if c.val = 1 then (1 : L) else 0 := by
  unfold bitsOfIndex
  have htop : (c.val * 2 ^ s + jl.val).testBit s = c.val.testBit 0 := by
    have := testBit_high_of_mul_two_pow_add c.val jl.val 0 jl.isLt
    simpa using this
  simp only [Fin.val_last, Nat.getBit_eq_testBit, htop, Nat.testBit_zero]
  have hc := c.isLt
  interval_cases h' : c.val <;> simp


set_option maxHeartbeats 8000000 in
/-- **Per-fiber disagreement is visible in the binary-fold rows** (M_y injectivity, induction
form): if all `2^s` binary-challenge iterated folds of `f` and `g` agree at `y`, then `f` and
`g` agree on the entire iterated-quotient fiber of `y`. -/
lemma fiber_agree_of_binary_folds_agree (s : ℕ) (iv : ℕ) (hiv : iv < r)
    (h_s : s < ℓ + 1) (h_is : iv + s < ℓ + 𝓡) (h_le : iv + s ≤ ℓ)
    (f g : sDomain 𝔽q β h_ℓ_add_R_rate ⟨iv, hiv⟩ → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨iv + s, Nat.lt_trans h_is h_ℓ_add_R_rate⟩)
    (hrows : ∀ j : Fin (2 ^ s),
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
        (steps := ⟨s, h_s⟩) (h_i_add_steps := h_is) f (bitsOfIndex (L := L) j) y =
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
        (steps := ⟨s, h_s⟩) (h_i_add_steps := h_is) g (bitsOfIndex (L := L) j) y)
    (idx : Fin (2 ^ s)) :
    f (qMap_total_fiber 𝔽q β (i := ⟨iv, hiv⟩) (steps := s)
        (h_i_add_steps := h_is) (y := y) idx) =
    g (qMap_total_fiber 𝔽q β (i := ⟨iv, hiv⟩) (steps := s)
        (h_i_add_steps := h_is) (y := y) idx) := by
  induction s with
  | zero =>
    have h0 := hrows 0
    conv at h0 =>
      lhs
      unfold iterated_fold_steps
      rw [Fin.dfoldl_zero]
    conv at h0 =>
      rhs
      unfold iterated_fold_steps
      rw [Fin.dfoldl_zero]
    exact h0
  | succ n ih =>
    have h_s' : n < ℓ + 1 := by omega
    have h_is' : iv + n < ℓ + 𝓡 := by omega
    have h_le' : iv + n ≤ ℓ := by omega
    have h_i1 : (⟨iv + n, by omega⟩ : Fin r).val + 1 < ℓ + 𝓡 := by
      show iv + n + 1 < ℓ + 𝓡
      omega
    -- the lifted point one level below the top
    set y' : sDomain 𝔽q β h_ℓ_add_R_rate
        ⟨(⟨iv + n, by omega⟩ : Fin r).val + 1, by
          show iv + n + 1 < r
          omega⟩ :=
      ⟨y.val, by
        have := y.property
        simpa only [Nat.add_assoc] using this⟩ with hy'def
    -- binary-pair rows pin the n-step folds on the two single-step preimages of y
    have hAgree : ∀ (jl : Fin (2 ^ n)) (c : Fin 2),
        iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
          (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') f (bitsOfIndex (L := L) jl)
          (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
            (h_i_add_steps := h_i1) (y := y') c) =
        iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
          (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') g (bitsOfIndex (L := L) jl)
          (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
            (h_i_add_steps := h_i1) (y := y') c) := by
      intro jl c
      have hbound : ∀ cv : Fin 2, cv.val * 2 ^ n + jl.val < 2 ^ (n + 1) := by
        intro cv
        have h1 := cv.isLt
        have h2 := jl.isLt
        calc cv.val * 2 ^ n + jl.val
            < cv.val * 2 ^ n + 2 ^ n := by omega
          _ = (cv.val + 1) * 2 ^ n := by ring
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
      -- specialize the rows at the two combined indices
      have hrow : ∀ cv : Fin 2,
          fold_legacy 𝔽q β (i := ⟨iv + n, by omega⟩) (h_i := h_i1)
            (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨iv, hiv⟩) (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') f
              (bitsOfIndex (L := L) jl))
            (r_chal := if cv.val = 1 then (1 : L) else 0) y' =
          fold_legacy 𝔽q β (i := ⟨iv + n, by omega⟩) (h_i := h_i1)
            (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨iv, hiv⟩) (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') g
              (bitsOfIndex (L := L) jl))
            (r_chal := if cv.val = 1 then (1 : L) else 0) y' := by
        intro cv
        have hr := hrows ⟨cv.val * 2 ^ n + jl.val, hbound cv⟩
        rw [iterated_fold_succ_last_gen 𝔽q β (i := ⟨iv, hiv⟩) (n := n)
            (h_steps := h_s) (h_i_add_steps := h_is) (f := f),
          iterated_fold_succ_last_gen 𝔽q β (i := ⟨iv, hiv⟩) (n := n)
            (h_steps := h_s) (h_i_add_steps := h_is) (f := g)] at hr
        have hinit : (fun b : Fin n => bitsOfIndex (L := L)
            (⟨cv.val * 2 ^ n + jl.val, hbound cv⟩ : Fin (2 ^ (n + 1))) b.castSucc) =
            bitsOfIndex (L := L) jl :=
          funext (bitsOfIndex_combine_castSucc jl cv (hbound cv))
        rw [hinit, bitsOfIndex_combine_last jl cv (hbound cv)] at hr
        exact hr
      have h0 := hrow 0
      have h1 := hrow 1
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, if_false, if_true] at h0 h1
      exact fold_legacy_binary_inj 𝔽q β ⟨iv + n, by omega⟩ h_i1
        (by show iv + n + 1 ≤ ℓ; omega) _ _ y' h0 h1 c
    -- peel the fiber index and conclude with the IH at the selected preimage
    have hpeel := qMap_total_fiber_succ_peel_last 𝔽q β
      (i := (⟨iv, by omega⟩ : Fin ℓ)) (n := n)
      (h_i_add_steps := by show iv + (n + 1) ≤ ℓ; omega)
      (y' := y) (idx := idx)
    rw [hpeel]
    exact ih h_s' h_is' h_le'
      (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
        (h_i_add_steps := h_i1) (y := y')
        ⟨idx.val / 2 ^ n, by
          have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩)
      (fun jl => hAgree jl _)
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

end
end Binius.BinaryBasefold
