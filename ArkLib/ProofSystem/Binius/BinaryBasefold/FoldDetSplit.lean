/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick

/-!
# #317: prove `FoldMatrixDetNeZeroResidual`.

Strategy:
* `detSplitFactor`: det of the 2×2-block matrix
  `fromBlocks (xb • M) ((-xa) • N) ((-1) • M) N = (xb - xa)^m * det M * det N`
  via the factorization `fromBlocks (xb•1) ((-xa)•1) ((-1)•1) 1 * fromBlocks M 0 0 N`.
* `det_submatrix_equiv_ne_zero`: reindexing rows/cols by two (possibly different)
  equivs changes det only by a permutation sign (a unit), preserving nonvanishing.
* `qMap_total_fiber_one_step_ne`: the two single-step fiber points differ
  (their 0-th basis coefficients are the bits 0 ≠ 1 of the fiber index).
* `foldMatrixNat_succ_eq_submatrix`: the recursion is exactly the block matrix
  `fromBlocks (x₁•M₀) ((-x₀)•M₁) ((-1)•M₀) M₁` reindexed by the low-bit row split
  and the high-bit column split.
* Induction ⇒ `foldMatrixNat` has nonzero det ⇒ the `FoldMatrixDetNeZeroResidual`
  instance.
-/

namespace Binius.BinaryBasefold.DetNeZero

open Matrix Binius.BinaryBasefold

/-! ### Generic matrix bricks (no Binius dependencies) -/

section MatrixBricks

variable {L : Type} [Field L]

/-- Row split of `Fin (2^(n+1))` by the LOW bit: `a ↦ (a % 2, a / 2)`,
`inl` for low bit `0`, `inr` for low bit `1`. -/
def rowSplit (n : ℕ) : Fin (2 ^ (n + 1)) ≃ (Fin (2 ^ n) ⊕ Fin (2 ^ n)) where
  toFun a :=
    if a.val % 2 = 0 then
      Sum.inl ⟨a.val / 2, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := a.isLt; omega⟩
    else
      Sum.inr ⟨a.val / 2, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := a.isLt; omega⟩
  invFun p :=
    match p with
    | Sum.inl q => ⟨2 * q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
    | Sum.inr q => ⟨2 * q.val + 1, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
  left_inv a := by
    by_cases h : a.val % 2 = 0 <;> simp only [h, if_true, if_false] <;>
      · apply Fin.ext
        simp only [Fin.val_mk]
        omega
  right_inv p := by
    rcases p with q | q
    · simp only [Nat.mul_mod_right, if_true]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · have h : (2 * q.val + 1) % 2 = 1 := by omega
      simp only [h, one_ne_zero, if_false]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- Column split of `Fin (2^(n+1))` by the HIGH bit: `b ↦ (b / 2^n, b % 2^n)`,
`inl` for high bit `0`, `inr` for high bit `1`. -/
def colSplit (n : ℕ) : Fin (2 ^ (n + 1)) ≃ (Fin (2 ^ n) ⊕ Fin (2 ^ n)) where
  toFun b :=
    if h : b.val < 2 ^ n then Sum.inl ⟨b.val, h⟩
    else Sum.inr ⟨b.val - 2 ^ n, by
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      have := b.isLt; omega⟩
  invFun p :=
    match p with
    | Sum.inl q => ⟨q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
    | Sum.inr q => ⟨2 ^ n + q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
  left_inv b := by
    by_cases h : b.val < 2 ^ n
    · simp only [h, dif_pos]
    · simp only [h, dif_neg, not_false_iff]
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  right_inv p := by
    rcases p with q | q
    · simp only [Fin.val_mk, q.isLt, dif_pos]
    · have h : ¬ (2 ^ n + q.val < 2 ^ n) := by omega
      simp only [Fin.val_mk, h, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- `det (fromBlocks (xb•M) ((-xa)•N) ((-1)•M) N) = (xb - xa)^m * det M * det N`. -/
lemma detSplitFactor {m : ℕ} (xa xb : L) (M N : Matrix (Fin m) (Fin m) L) :
    (Matrix.fromBlocks (xb • M) ((-xa) • N) ((-1 : L) • M) N).det
      = (xb - xa) ^ m * M.det * N.det := by
  have hfact : Matrix.fromBlocks (xb • M) ((-xa) • N) ((-1 : L) • M) N =
      (Matrix.fromBlocks (xb • (1 : Matrix (Fin m) (Fin m) L)) ((-xa) • 1) ((-1 : L) • 1) 1) *
      (Matrix.fromBlocks M 0 0 N) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      smul_zero, add_zero, zero_add, Matrix.mul_one]
  rw [hfact, Matrix.det_mul, Matrix.det_fromBlocks_one₂₂, Matrix.det_fromBlocks_zero₁₂]
  have hscal : (xb • (1 : Matrix (Fin m) (Fin m) L)) - ((-xa) • 1) * ((-1 : L) • 1) =
      (xb - xa) • 1 := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_mul_neg, mul_one, sub_smul]
  rw [hscal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, mul_assoc]

/-- Reindexing rows and columns by two (possibly different) equivalences preserves
nonvanishing of the determinant: the two reindexings differ by a column permutation,
whose sign is a unit. -/
lemma det_submatrix_equiv_ne_zero {m n : Type*} [DecidableEq m] [DecidableEq n]
    [Fintype m] [Fintype n] (e₁ e₂ : n ≃ m) (M : Matrix m m L) (h : M.det ≠ 0) :
    (M.submatrix e₁ e₂).det ≠ 0 := by
  have hsub : M.submatrix e₁ e₂ =
      (M.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext a b
    simp [Matrix.submatrix_apply]
  rw [hsub, Matrix.det_permute' (e₂.trans e₁.symm) (M.submatrix e₁ e₁),
    Matrix.det_submatrix_equiv_self]
  apply mul_ne_zero _ h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₂.trans e₁.symm)) with hs | hs <;>
    simp [hs]

end MatrixBricks

/-! ### The welding: `foldMatrixNat (n+1)` as a reindexed 2×2 block matrix, and the induction -/

section Weld

open AdditiveNTT

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The two single-step `qMap` preimages of `y` used by the `foldMatrixNat` recursion at
`steps = n + 1`: the fiber of `y` (lifted to the legacy `(i + n) + 1` index) under the last
quotient level. -/
def foldZ (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + (n + 1), by omega⟩) :
    Fin 2 → (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + n, by omega⟩ :=
  qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega)
    (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
set_option maxHeartbeats 16000000 in
/-- **The welding identity** (issue #317): one step of the `foldMatrixNat` recursion is exactly
the 2×2 block matrix `fromBlocks (x₁ • M₀) ((-x₀) • M₁) ((-1) • M₀) M₁` reindexed by the
low-bit row split and the high-bit column split, where `x_c = foldZ … c` are the two
single-step preimages of `y` and `M_c = foldMatrixNat … n (foldZ … c)`.

(The generous heartbeat budget is for the four per-entry `rfl`s: the defeq check pays a
proof-irrelevance comparison through the `sDomain` subtype lifts; see the issue notes.) -/
lemma foldMatrixNat_succ_eq (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + (n + 1), by omega⟩) :
    foldMatrixNat 𝔽q β i (n + 1) h y =
      (Matrix.fromBlocks
        ((↑(foldZ 𝔽q β i n h y 1) : L) •
          foldMatrixNat 𝔽q β i n (by omega) (foldZ 𝔽q β i n h y 0))
        ((-(↑(foldZ 𝔽q β i n h y 0) : L)) •
          foldMatrixNat 𝔽q β i n (by omega) (foldZ 𝔽q β i n h y 1))
        ((-1 : L) •
          foldMatrixNat 𝔽q β i n (by omega) (foldZ 𝔽q β i n h y 0))
        (foldMatrixNat 𝔽q β i n (by omega) (foldZ 𝔽q β i n h y 1))).submatrix
        (rowSplit n) (colSplit n) := by
  ext a b
  rw [Matrix.submatrix_apply]
  simp only [foldMatrixNat]
  unfold foldZ
  have hblt : b.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq b.isLt (by rw [pow_succ])
  by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val < 2 ^ n
  · -- low row bit 0, high column bit 0: the `x₁ • M₀` block
    have hdiv : b.val / 2 ^ n = 0 := Nat.div_eq_of_lt hb
    have ea : ∀ pf : a.val % 2 < 2, (⟨a.val % 2, pf⟩ : Fin 2) = 0 :=
      fun _ => Fin.ext (by simpa using ha)
    have ec : ∀ pf : b.val / 2 ^ n < 2, (⟨b.val / 2 ^ n, pf⟩ : Fin 2) = 0 :=
      fun _ => Fin.ext (by simpa using hdiv)
    have ebl : ∀ pf : b.val % 2 ^ n < 2 ^ n,
        (⟨b.val % 2 ^ n, pf⟩ : Fin (2 ^ n)) = ⟨b.val, hb⟩ :=
      fun _ => Fin.ext (by simpa using Nat.mod_eq_of_lt hb)
    rw [ea, ec, ebl]
    simp only [rowSplit, colSplit, Equiv.coe_fn_mk]
    rw [if_pos ha, dif_pos hb, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul]
    rfl
  · -- low row bit 0, high column bit 1: the `(-x₀) • M₁` block
    have hdiv : b.val / 2 ^ n = 1 :=
      Nat.div_eq_of_lt_le (by simpa using Nat.le_of_not_lt hb) (by omega)
    have hmod : b.val % 2 ^ n = b.val - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hb)]
      exact Nat.mod_eq_of_lt (by omega)
    have ea : ∀ pf : a.val % 2 < 2, (⟨a.val % 2, pf⟩ : Fin 2) = 0 :=
      fun _ => Fin.ext (by simpa using ha)
    have ec : ∀ pf : b.val / 2 ^ n < 2, (⟨b.val / 2 ^ n, pf⟩ : Fin 2) = 1 :=
      fun _ => Fin.ext (by simpa using hdiv)
    have ebl : ∀ pf : b.val % 2 ^ n < 2 ^ n,
        (⟨b.val % 2 ^ n, pf⟩ : Fin (2 ^ n)) = ⟨b.val - 2 ^ n, by omega⟩ :=
      fun _ => Fin.ext (by simpa using hmod)
    rw [ea, ec, ebl]
    simp only [rowSplit, colSplit, Equiv.coe_fn_mk]
    rw [if_pos ha, dif_neg hb, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, smul_eq_mul]
    rfl
  · -- low row bit 1, high column bit 0: the `(-1) • M₀` block
    have ha1 : a.val % 2 = 1 := by omega
    have hdiv : b.val / 2 ^ n = 0 := Nat.div_eq_of_lt hb
    have ea : ∀ pf : a.val % 2 < 2, (⟨a.val % 2, pf⟩ : Fin 2) = 1 :=
      fun _ => Fin.ext (by simpa using ha1)
    have ec : ∀ pf : b.val / 2 ^ n < 2, (⟨b.val / 2 ^ n, pf⟩ : Fin 2) = 0 :=
      fun _ => Fin.ext (by simpa using hdiv)
    have ebl : ∀ pf : b.val % 2 ^ n < 2 ^ n,
        (⟨b.val % 2 ^ n, pf⟩ : Fin (2 ^ n)) = ⟨b.val, hb⟩ :=
      fun _ => Fin.ext (by simpa using Nat.mod_eq_of_lt hb)
    rw [ea, ec, ebl]
    simp only [rowSplit, colSplit, Equiv.coe_fn_mk]
    rw [if_neg ha, dif_pos hb, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
    rfl
  · -- low row bit 1, high column bit 1: the plain `M₁` block
    have ha1 : a.val % 2 = 1 := by omega
    have hdiv : b.val / 2 ^ n = 1 :=
      Nat.div_eq_of_lt_le (by simpa using Nat.le_of_not_lt hb) (by omega)
    have hmod : b.val % 2 ^ n = b.val - 2 ^ n := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hb)]
      exact Nat.mod_eq_of_lt (by omega)
    have ea : ∀ pf : a.val % 2 < 2, (⟨a.val % 2, pf⟩ : Fin 2) = 1 :=
      fun _ => Fin.ext (by simpa using ha1)
    have ec : ∀ pf : b.val / 2 ^ n < 2, (⟨b.val / 2 ^ n, pf⟩ : Fin 2) = 1 :=
      fun _ => Fin.ext (by simpa using hdiv)
    have ebl : ∀ pf : b.val % 2 ^ n < 2 ^ n,
        (⟨b.val % 2 ^ n, pf⟩ : Fin (2 ^ n)) = ⟨b.val - 2 ^ n, by omega⟩ :=
      fun _ => Fin.ext (by simpa using hmod)
    rw [ea, ec, ebl]
    simp only [rowSplit, colSplit, Equiv.coe_fn_mk]
    rw [if_neg ha, dif_neg hb, Matrix.fromBlocks_apply₂₂]
    refine Eq.trans ?_ (one_mul _)
    rfl

set_option maxHeartbeats 4000000 in
/-- **Fiber separation in `L`**: the two single-step preimages of `y` differ in `L` by the
nonzero coerced basis vector, so `x₁ − x₀ ≠ 0`. -/
lemma foldZ_sub_ne_zero (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (hle : i.val + (n + 1) ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + (n + 1), by omega⟩) :
    (↑(foldZ 𝔽q β i n h y 1) : L) - (↑(foldZ 𝔽q β i n h y 0) : L) ≠ 0 := by
  have hsub : foldZ 𝔽q β i n h y 1 - foldZ 𝔽q β i n h y 0
      = sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i.val + n, by omega⟩
          (by show i.val + n < ℓ + 𝓡; omega)
          ⟨0, by show 0 < ℓ + 𝓡 - (i.val + n); omega⟩ := by
    unfold foldZ
    exact qMap_total_fiber_one_sub 𝔽q β ⟨i.val + n, by omega⟩
      (h_i := by show i.val + n + 1 < ℓ + 𝓡; omega)
      (h_le := by show i.val + n + 1 ≤ ℓ; omega)
      (y := ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩)
  rw [← AddSubgroupClass.coe_sub, hsub]
  have hb := (sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i.val + n, by omega⟩
    (by show i.val + n < ℓ + 𝓡; omega)).ne_zero
    ⟨0, by show 0 < ℓ + 𝓡 - (i.val + n); omega⟩
  exact fun hc => hb (by exact_mod_cast Subtype.ext hc)

set_option maxHeartbeats 4000000 in
/-- **The induction** (issue #317): every `foldMatrixNat` within the `≤ ℓ` range has nonzero
determinant — by `foldMatrixNat_succ_eq`, `det_submatrix_equiv_ne_zero`, `detSplitFactor`,
and the fiber-separation brick at each level. -/
theorem foldMatrixNat_det_ne_zero (i : Fin r) (steps : ℕ)
    (h : i.val + steps < ℓ + 𝓡) (hle : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :
    (foldMatrixNat 𝔽q β i steps h y).det ≠ 0 := by
  induction steps with
  | zero =>
    haveI : Unique (Fin (2 ^ 0)) :=
      ⟨⟨⟨0, by norm_num⟩⟩, fun a => Fin.ext (by
        have := a.isLt
        norm_num at this
        omega)⟩
    rw [Matrix.det_unique]
    simp only [foldMatrixNat]
    exact one_ne_zero
  | succ n ih =>
    rw [foldMatrixNat_succ_eq 𝔽q β i n h y]
    refine det_submatrix_equiv_ne_zero (rowSplit n) (colSplit n) _ ?_
    rw [detSplitFactor]
    exact mul_ne_zero
      (mul_ne_zero
        (pow_ne_zero _ (foldZ_sub_ne_zero 𝔽q β i n h hle y))
        (ih (by omega) (by omega) (foldZ 𝔽q β i n h y 0)))
      (ih (by omega) (by omega) (foldZ 𝔽q β i n h y 1))

end

end Weld

end Binius.BinaryBasefold.DetNeZero
