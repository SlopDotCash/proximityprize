/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.NamedCharacterBlocks
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Rank of a circulant from the first nonzero local coefficient of its symbol -/

open Polynomial Module
namespace ProximityGap.DyadicCharacterCirculant

variable {F : Type*} [Field F]

/-- Multiplication by the kernel polynomial in the cyclic polynomial representation. -/
noncomputable def convolution (modulus kernel : F[X]) :
    AdjoinRoot modulus →ₗ[F] AdjoinRoot modulus :=
  Algebra.lmul F (AdjoinRoot modulus) (AdjoinRoot.mk modulus kernel)

/-- The range has codimension d if the symbol is a degree-d power of a linear
factor times a polynomial coprime to the modulus. -/
theorem local_rank (a : F) (n d : ℕ) (hd : d ≤ n) (U : F[X])
    (hu : IsCoprime U (X-C a)) :
    finrank F (LinearMap.range (convolution ((X-C a)^n) ((X-C a)^d * U))) + d = n := by
  classical
  let T : F[X] := X-C a
  have hm : T.Monic := monic_X_sub_C a
  have hpow : T^d ∣ T^n := pow_dvd_pow T hd
  let π := AdjoinRoot.algHomOfDvd F (T^n) (T^d) hpow
  have hπ (f : F[X]) : π (AdjoinRoot.mk (T^n) f) = AdjoinRoot.mk (T^d) f := by
    induction f using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial i b =>
      rw [← C_mul_X_pow_eq_monomial]
      simp [π, AdjoinRoot.algHomOfDvd]
  have surj : Function.Surjective π.toLinearMap := by
    intro x
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    exact ⟨AdjoinRoot.mk (T^n) f, hπ f⟩
  have ker : LinearMap.range (convolution (T^n) (T^d*U)) = LinearMap.ker π.toLinearMap := by
    ext x
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    constructor
    · rintro ⟨v, he⟩
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective v
      rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, ← he]
      change π (AdjoinRoot.mk (T^n) (T^d*U) * AdjoinRoot.mk (T^n) g) = 0
      rw [map_mul, hπ, hπ, map_mul, AdjoinRoot.mk_self, zero_mul, zero_mul]
    · intro hx
      rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, hπ, AdjoinRoot.mk_eq_zero] at hx
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨u, w, he⟩ := (hu.pow_right : IsCoprime U (T^n))
      have hone : AdjoinRoot.mk (T^n) u * AdjoinRoot.mk (T^n) U = 1 := by
        have hh := congrArg (AdjoinRoot.mk (T^n)) he
        simpa [T, map_add, map_mul, AdjoinRoot.mk_self] using hh
      refine ⟨AdjoinRoot.mk (T^n) u * AdjoinRoot.mk (T^n) v, ?_⟩
      change AdjoinRoot.mk (T^n) (T^d * U) * _ = AdjoinRoot.mk (T^n) (T^d * v)
      rw [map_mul, map_mul]
      calc
        _ = AdjoinRoot.mk (T^n) (T^d) * (AdjoinRoot.mk (T^n) u * AdjoinRoot.mk (T^n) U) *
              AdjoinRoot.mk (T^n) v := by ring
        _ = _ := by rw [hone, mul_one]
  let := (AdjoinRoot.powerBasis' (hm.pow n)).finite
  let := (AdjoinRoot.powerBasis' (hm.pow d)).finite
  have dim (j : ℕ) : finrank F (AdjoinRoot (T^j)) = j := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis' (hm.pow j))]
    change (T^j).natDegree = j
    simp [T]
  have hrank := π.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj, finrank_top, dim, dim] at hrank
  change finrank F (LinearMap.range (convolution (T^n) (T^d*U))) + d = n
  rw [ker, add_comm, hrank]

/-- Polynomial of eight residue classes of cyclic kernel coefficients, in
their ordinary exponent order. -/
noncomputable def symbol {m : ℕ} (bits : Fin 8 → Fin m → ZMod 2) : (ZMod 2)[X] :=
  ∑ r : Fin 8, X^(r : ℕ) * ∑ i : Fin m, C (bits r i) * (X^8)^(i : ℕ)

/-- Summing the coefficients in each residue class reduces the symbol modulo X⁸−1. -/
theorem block_reduction {m : ℕ} (bits : Fin 8 → Fin m → ZMod 2) :
    (X^8-1 : (ZMod 2)[X]) ∣ symbol bits - ∑ r : Fin 8, X^(r : ℕ) * C (∑ i, bits r i) := by
  let f : (ZMod 2)[X] := X^8-1
  change f ∣ _
  apply AdjoinRoot.mk_eq_zero.mp
  have hroot : AdjoinRoot.mk f (X^8) = 1 := by
    apply sub_eq_zero.mp
    simpa [f, map_sub, map_one] using (AdjoinRoot.mk_self : AdjoinRoot.mk f f = 0)
  have hp (i : ℕ) : AdjoinRoot.mk f ((X^8)^i) = 1 := by rw [map_pow, hroot, one_pow]
  simp only [symbol, map_sub, map_sum, map_mul, hp, mul_one, sub_self]

/-- The named block signature determines the exact rank on the production cyclic algebra. -/
theorem rank_from_blocks {m : ℕ} (j : ℕ) (hd : 6 ≤ 2^j) (bits : Fin 8 → Fin m → ZMod 2)
    (hb : ∀ r, ∑ i, bits r i = (r.val : ZMod 2)) :
    finrank (ZMod 2) (LinearMap.range (convolution (F := ZMod 2) (X^(2^j)-1) (symbol bits))) + 6 = 2^j := by
  classical
  let T : (ZMod 2)[X] := X - C 1
  have pow_two (j : ℕ) : T^(2^j) = X^(2^j)-1 := by
    simp [T, sub_pow_char_pow]
  have small : ∑ r : Fin 8, X^(r : ℕ) * C (∑ i, bits r i) = T^6 * X := by
    simp_rw [hb]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    have h2 : T^2 = X^2-1 := pow_two 1
    have h4 : T^4 = X^4-1 := pow_two 2
    rw [show T^6 = T^2 * T^4 from pow_add T 2 4, h2, h4]
    norm_num
    simp only [CharTwo.sub_eq_add]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      show (4 : ZMod 2) = 0 by decide, show (5 : ZMod 2) = 1 by decide,
      show (6 : ZMod 2) = 0 by decide, show (7 : ZMod 2) = 1 by decide,
      map_zero, map_one, mul_zero, mul_one, add_zero, zero_add]
  obtain ⟨V, he⟩ := block_reduction bits
  have h8 : T^8 = X^8-1 := pow_two 3
  rw [small, ← h8] at he
  let U := X + T^2 * V
  have hk : symbol bits = T^6 * U := by
    dsimp [U]
    linear_combination he
  have cop : IsCoprime U T := by
    refine ⟨1,-(1+T*V), ?_⟩
    dsimp [U,T]
    rw [map_one]
    ring
  let R (f k : (ZMod 2)[X]) := finrank (ZMod 2) (LinearMap.range (convolution f k)) + 6
  change R _ _ = 2^j
  calc
    _ = R (T^(2^j)) (T^6*U) := congrArg₂ R (pow_two j).symm hk
    _ = _ := local_rank (1 : ZMod 2) (2^j) 6 hd U cop

private theorem named_rank {m : ℕ} (bits : Fin 8 → Fin m → ZMod 2)
    (hb : ∀ r, ∑ i, bits r i = (r.val : ZMod 2)) :
    finrank (ZMod 2) (LinearMap.range (convolution (F := ZMod 2) (X^(2^30)-1) (symbol bits))) =
      1073741818 := by
  exact (show ∀ a : ℕ, a + 6 = 2^30 → a = 1073741818 by intro a h; omega) _
    (rank_from_blocks 30 (by decide) bits hb)

/-- Binary rank of the literal cyclic character kernel at the first named prime. -/
theorem first_rank :
    let bits := fun (r : Fin 8) (i : Fin (2^27)) =>
      NamedCharacterBlocks.bit (NamedCharacterBlocks.factor ArkLib.ProximityGap.PrizeShapePrimeP30.g r i)
    finrank (ZMod 2) (LinearMap.range (convolution (F := ZMod 2) (X^(2^30)-1) (symbol bits))) =
      1073741818 :=
  named_rank _ NamedCharacterBlocks.first_block_sums

/-- Binary rank of the literal cyclic character kernel at the second named prime. -/
theorem second_rank :
    let bits := fun (r : Fin 8) (i : Fin (2^27)) =>
      NamedCharacterBlocks.bit (NamedCharacterBlocks.factor ArkLib.ProximityGap.PrizeShapePrimeP30Second.g r i)
    finrank (ZMod 2) (LinearMap.range (convolution (F := ZMod 2) (X^(2^30)-1) (symbol bits))) =
      1073741818 :=
  named_rank _ NamedCharacterBlocks.second_block_sums

#print axioms first_rank
#print axioms second_rank
#print axioms local_rank
#print axioms rank_from_blocks
end ProximityGap.DyadicCharacterCirculant
