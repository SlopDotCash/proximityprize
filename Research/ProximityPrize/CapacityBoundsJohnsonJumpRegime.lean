/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.CapacityBounds
import Mathlib.FieldTheory.Finite.Basic

/-!
# The T4.18 Johnson-jump statement needs `ε < 1` and a large field

[BCHKS25, Thm 1.6 / Cor 1.7] (ABF26 Theorem 4.18) is proved for a small constant `ε > 0` and
"for `q` large enough" (§5: `q = 2^m`, `b = ⌈(1+ε)m/2⌉`, `a = b + 2`, an `a`-dimensional
`F₂`-subspace `V ⊆ F_q`, `n = |V| = 2^a`, `k = 2^{b-2}`).  This file checks that
`CodingTheory.rs_epsCA_johnson_jump_bchks25` is false without those guards, so the residual
`bchks25_rs_epsCA_johnson_jump_residual` has to carry them, and that the block-length window
of the statement contains the paper's `n`.

* `rs_epsCA_johnson_jump_bchks25_sixteen_le_card`: `δ_min = 15/16` means
  `16 · minDist = 15 · n`, so `16 ∣ n ≤ |F|`.
* `rs_epsCA_johnson_jump_bchks25_false_zmod_two`: hence the statement is false over `𝔽₂`
  (and every field with fewer than 16 elements) for every `ε > 0`.
* `rs_epsCA_johnson_jump_bchks25_false_of_one_lt`: for `ε > 1` the window forces `n > |F|`,
  so the statement is false over every characteristic-2 field.
* `johnson_jump_unguarded_false`: the unguarded reading (every characteristic-2 field, every
  `ε > 0`) is false.
* `bchks25_johnson_jump_blocklength_bounds`: the paper's `n = 2^{⌈(1+ε)m/2⌉ + 2}` satisfies
  `4 · q^{(1+ε)/2} ≤ n < 8 · q^{(1+ε)/2}`, so it lies in the window
  `[q^{(1+ε)/2}, 8 · q^{(1+ε)/2}]` and above `q^{(1+ε)/2} + 1`.
-/

namespace CodingTheory

open NNReal

namespace BCHKS25JohnsonJumpRegime

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Any T4.18 witness over `F` forces `16 ≤ |F|`. -/
theorem rs_epsCA_johnson_jump_bchks25_sixteen_le_card
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε) (h : rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε) :
    16 ≤ Fintype.card FC := by
  obtain ⟨ιC, hF, hN, hD, ⟨W⟩⟩ := exists_rsJohnsonJumpWitness_of_bchks25 ε hε h
  exact W.sixteen_le_card_field

/-- Over a characteristic-2 field with fewer than 16 elements there is no T4.18 witness. -/
theorem rs_epsCA_johnson_jump_bchks25_false_of_card_lt
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (hq : Fintype.card FC < 16) (ε : ℝ≥0) (hε : 0 < ε) :
    ¬ rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε := fun h =>
  absurd (rs_epsCA_johnson_jump_bchks25_sixteen_le_card ε hε h) (by omega)

/-- Over `𝔽₂` the T4.18 statement is false for every `ε > 0`. -/
theorem rs_epsCA_johnson_jump_bchks25_false_zmod_two (ε : ℝ≥0) (hε : 0 < ε) :
    ¬ rs_epsCA_johnson_jump_bchks25 (FC := ZMod 2) ε hε :=
  rs_epsCA_johnson_jump_bchks25_false_of_card_lt (by simp [ZMod.card]) ε hε

/-- For `ε > 1` the T4.18 statement is false over every characteristic-2 field: the window
asks for `|F|^{(1+ε)/2} ≤ n`, but `n ≤ |F| < |F|^{(1+ε)/2}`. -/
theorem rs_epsCA_johnson_jump_bchks25_false_of_one_lt
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2]
    (ε : ℝ≥0) (hε : 0 < ε) (h1 : 1 < (ε : ℝ)) :
    ¬ rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε := fun h => by
  rcases h with ⟨ιC, hF, hN, hD, domain, k, hlo, -, -, -⟩
  have hle : (Fintype.card ιC : ℝ) ≤ Fintype.card FC := by
    exact_mod_cast Fintype.card_le_of_embedding domain
  have hq : (1 : ℝ) < Fintype.card FC := by exact_mod_cast Fintype.one_lt_card
  have hpow : (Fintype.card FC : ℝ) ^ (1 : ℝ) < (Fintype.card FC : ℝ) ^ (((1 : ℝ) + ε) / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
  rw [Real.rpow_one] at hpow
  linarith

/-- The unguarded reading of T4.18 (every characteristic-2 field, every `ε > 0`) is false. -/
theorem johnson_jump_unguarded_false :
    ¬ (∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
        ∀ (ε : ℝ≥0) (hε : 0 < ε), rs_epsCA_johnson_jump_bchks25 (FC := FC) ε hε) :=
  fun h => rs_epsCA_johnson_jump_bchks25_false_zmod_two 1 one_pos (h (FC := ZMod 2) 1 one_pos)

/-- The BCHKS25 §5 block length `n = 2^{⌈(1+ε)m/2⌉ + 2}` over `q = 2^m` satisfies
`4 · q^{(1+ε)/2} ≤ n < 8 · q^{(1+ε)/2}`.  So it lies in the T4.18 window
`[q^{(1+ε)/2}, 8 · q^{(1+ε)/2}]`, and above `q^{(1+ε)/2} + 1`. -/
theorem bchks25_johnson_jump_blocklength_bounds (m : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    4 * ((2 : ℝ) ^ m) ^ ((1 + ε) / 2) ≤ (2 : ℝ) ^ (⌈(1 + ε) * m / 2⌉₊ + 2) ∧
      (2 : ℝ) ^ (⌈(1 + ε) * m / 2⌉₊ + 2) < 8 * ((2 : ℝ) ^ m) ^ ((1 + ε) / 2) ∧
      ((2 : ℝ) ^ m) ^ ((1 + ε) / 2) + 1 < (2 : ℝ) ^ (⌈(1 + ε) * m / 2⌉₊ + 2) := by
  set e : ℝ := (1 + ε) * m / 2 with he
  have he0 : 0 ≤ e := by positivity
  have hx : ((2 : ℝ) ^ m) ^ ((1 + ε) / 2) = (2 : ℝ) ^ e := by
    rw [← Real.rpow_natCast_mul (by norm_num)]
    congr 1
    rw [he]
    ring
  rw [hx]
  set c : ℕ := ⌈e⌉₊
  have hc_lo : e ≤ (c : ℝ) := Nat.le_ceil e
  have hc_hi : (c : ℝ) < e + 1 := Nat.ceil_lt_add_one he0
  have h2c : (2 : ℝ) ^ (c + 2) = 4 * (2 : ℝ) ^ (c : ℝ) := by
    rw [Real.rpow_natCast, pow_add]
    ring
  have hlo : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ (c : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hc_lo
  have hhi : (2 : ℝ) ^ (c : ℝ) < (2 : ℝ) ^ (e + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hc_hi
  rw [Real.rpow_add (by norm_num), Real.rpow_one] at hhi
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ e := Real.one_le_rpow (by norm_num) he0
  rw [h2c]
  refine ⟨by linarith, by linarith, by linarith⟩

end BCHKS25JohnsonJumpRegime

end CodingTheory

#print axioms CodingTheory.BCHKS25JohnsonJumpRegime.rs_epsCA_johnson_jump_bchks25_sixteen_le_card
#print axioms CodingTheory.BCHKS25JohnsonJumpRegime.rs_epsCA_johnson_jump_bchks25_false_zmod_two
#print axioms CodingTheory.BCHKS25JohnsonJumpRegime.rs_epsCA_johnson_jump_bchks25_false_of_one_lt
#print axioms CodingTheory.BCHKS25JohnsonJumpRegime.johnson_jump_unguarded_false
#print axioms CodingTheory.BCHKS25JohnsonJumpRegime.bchks25_johnson_jump_blocklength_bounds
