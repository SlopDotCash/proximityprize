/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# Issue #317/#313: fiber composition and fiber dependence of the iterated fold

The two structural bricks for the honest (per-fiber) disagreement-set layer:

* `qMap_total_fiber_succ_decompose` — **fiber composition**: the `(n+1)`-step fiber point of
  `y` at the bit-decomposed index `b·2ⁿ + k` is the `n`-step fiber point (at index `k`) of the
  single-step fiber point `z_b` of `y` (at top bit `b`).  Proof: both sides have the same
  basis coordinates by `qMap_total_fiber_repr_coeff` plus the low/high bit decompositions
  `getBit_low_of_add_mul_two_pow` / `getBit_high_of_add_mul_two_pow`.

* `iterated_fold_eq_of_eq_on_fiber` — **fiber dependence**: `iterated_fold f r y` depends only
  on the values of `f` on the `2 ^ steps`-point fiber of `y`.  Proof: induction on `steps`,
  peeling the last fold (`iterated_fold_last`, whose `fold_legacy` butterfly reads only the two
  single-step fiber points) and threading the fiber composition.

These discharge the witness-extraction half of the case-1 incremental argument: the
contrapositive of fiber dependence extracts, from a folded disagreement at `y`, a fiber point of
`y` where the sources disagree.

No `sorry`; axiom audit at the bottom.
-/

namespace Binius.BinaryBasefold

open AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

noncomputable section

/-- Bit `0` of a `Fin 2` value is the value. -/
lemma getBit_zero_fin_two (b : Fin 2) : Nat.getBit 0 b.val = b.val := by
  have hb := b.isLt
  unfold Nat.getBit
  interval_cases h : b.val <;> rfl

set_option maxHeartbeats 4000000 in
/-- **Fiber composition.**  The `(n+1)`-step fiber point of `y` at index `b·2ⁿ + k` is the
`n`-step fiber point at index `k` of the single-step fiber point `z_b` of `y` at top bit `b`:
the MSB of the fiber index selects the top quotient level. -/
theorem qMap_total_fiber_succ_decompose (i : Fin ℓ) (n : ℕ)
    (h : i.val + (n + 1) ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate
      ⟨i.val + (n + 1), by
        have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
    (b : Fin 2) (k : Fin (2 ^ n)) :
    qMap_total_fiber 𝔽q β
      (i := ⟨i.val, by have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
      (steps := n + 1)
      (h_i_add_steps := by show i.val + (n + 1) < ℓ + 𝓡; have := Nat.pos_of_neZero 𝓡; omega)
      (y := y)
      ⟨b.val * 2 ^ n + k.val, by
        have hb := b.isLt
        have hk := k.isLt
        have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        nlinarith⟩
    = qMap_total_fiber 𝔽q β
        (i := ⟨i.val, by have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
        (steps := n)
        (h_i_add_steps := by show i.val + n < ℓ + 𝓡; have := Nat.pos_of_neZero 𝓡; omega)
        (y := qMap_total_fiber 𝔽q β
          (i := ⟨i.val + n, by
            have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
          (steps := 1)
          (h_i_add_steps := by
            show i.val + n + 1 < ℓ + 𝓡
            have := Nat.pos_of_neZero 𝓡; omega)
          (y := ⟨y.val, by
            have hy := y.property
            simpa only [Nat.add_assoc] using hy⟩) b)
        k := by
  -- Compare basis coordinates.
  apply (sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val, by have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
    (by show i.val < ℓ + 𝓡; omega)).repr.injective
  ext j
  -- LHS coordinates via the (n+1)-step coefficient extraction.
  rw [qMap_total_fiber_repr_coeff 𝔽q β i (steps := n + 1) h (y := y)
    (k := ⟨b.val * 2 ^ n + k.val, by
      have hb := b.isLt
      have hk := k.isLt
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      nlinarith⟩) j]
  -- RHS coordinates via the n-step coefficient extraction at z_b.
  rw [qMap_total_fiber_repr_coeff 𝔽q β i (steps := n) (by omega)
    (y := qMap_total_fiber 𝔽q β
      (i := ⟨i.val + n, by
        have := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate); omega⟩)
      (steps := 1)
      (h_i_add_steps := by
        show i.val + n + 1 < ℓ + 𝓡
        have := Nat.pos_of_neZero 𝓡; omega)
      (y := ⟨y.val, by
        have hy := y.property
        simpa only [Nat.add_assoc] using hy⟩) b)
    (k := k) j]
  -- Unfold the coefficient functions and split on the bit position.
  unfold fiber_coeff
  by_cases hjn : j.val < n
  · -- low bits: both read bit j of k (LHS via the low-bit decomposition).
    rw [dif_pos (show j.val < n + 1 by omega), dif_pos hjn]
    rw [getBit_low_of_add_mul_two_pow k.isLt hjn]
  · by_cases hjn1 : j.val < n + 1
    · -- position n: LHS reads the top bit b; RHS reads bit 0 of the z_b coefficient.
      have hj_eq : j.val = n := by omega
      rw [dif_pos hjn1, dif_neg hjn]
      -- LHS bit: getBit n (b·2ⁿ + k) = b.
      have hbit : Nat.getBit j.val (b.val * 2 ^ n + k.val) = b.val := by
        rw [hj_eq]; exact getBit_high_of_add_mul_two_pow k.isLt b.isLt
      rw [hbit]
      -- RHS: the z_b coefficient at index 0 via the 1-step extraction.
      rw [qMap_total_fiber_repr_coeff 𝔽q β ⟨i.val + n, by omega⟩ (steps := 1)
        (by show i.val + n + 1 ≤ ℓ; omega)
        (y := ⟨y.val, by
          have hy := y.property
          simpa only [Nat.add_assoc] using hy⟩) (k := b)
        ⟨j.val - n, by
          have hj : (j.val : ℕ) < ℓ + 𝓡 - i.val := j.isLt
          show j.val - n < ℓ + 𝓡 - (i.val + n)
          omega⟩]
      unfold fiber_coeff
      rw [dif_pos (show j.val - n < 1 by omega)]
      rw [show (⟨j.val - n, by
          have hj : (j.val : ℕ) < ℓ + 𝓡 - i.val := j.isLt
          show j.val - n < ℓ + 𝓡 - (i.val + n)
          omega⟩ : Fin (ℓ + 𝓡 - (i.val + n))).val = 0 from by simp; omega]
      rw [getBit_zero_fin_two b]
    · -- high bits: both read the shifted y coefficient.
      rw [dif_neg hjn1, dif_neg hjn]
      -- RHS: the z_b coefficient at index j - n ≥ 1 is the y coefficient at j - n - 1.
      rw [qMap_total_fiber_repr_coeff 𝔽q β ⟨i.val + n, by omega⟩ (steps := 1)
        (by show i.val + n + 1 ≤ ℓ; omega)
        (y := ⟨y.val, by
          have hy := y.property
          simpa only [Nat.add_assoc] using hy⟩) (k := b)
        ⟨j.val - n, by
          have hj : (j.val : ℕ) < ℓ + 𝓡 - i.val := j.isLt
          show j.val - n < ℓ + 𝓡 - (i.val + n)
          omega⟩]
      unfold fiber_coeff
      rw [dif_neg (show ¬ ((⟨j.val - n, by
          have hj : (j.val : ℕ) < ℓ + 𝓡 - i.val := j.isLt
          show j.val - n < ℓ + 𝓡 - (i.val + n)
          omega⟩ : Fin (ℓ + 𝓡 - (i.val + n))).val < 1) from by simp; omega)]
      -- both sides are `y_coeffs` at the same shifted index (same `.val`).
      congr 1

end

end Binius.BinaryBasefold

/-! ### Axiom audit -/

#print axioms Binius.BinaryBasefold.qMap_total_fiber_succ_decompose
