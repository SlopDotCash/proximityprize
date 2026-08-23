/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungClassFamily

/-!
# The three-class collapse (#371, rung): the generic size-6 bound

The clean, instance-free core of the size-6 kernel bound (probe
`probe_wb371_size6cap`: holds for 98.9% of configurations).  Three
degree-`< 3` cross-polynomials whose pairwise differences each vanish on a
2-point overlap satisfy the cycle relation

  `(q₁−q₂) + (q₂−q₃) + (q₃−q₁) = 0`,

and each difference is a scalar multiple of the overlap's monic quadratic
`m_{ij} = (X−aᵢⱼ)(X−bᵢⱼ)`.  Hence
`c₁₂·m₁₂ + c₂₃·m₂₃ + c₃₁·m₃₁ = 0`; if the three overlap-quadratics are
linearly independent, all `cᵢⱼ = 0`, forcing `q₁ = q₂ = q₃`
(`three_class_collapse`).  Geometrically: three size-6 agreement sets in
`μ₁₆` (forced pairwise overlap ≥ 2, since `3·6 > 16`) with independent
overlap-quadratics cannot carry three distinct classes — at most two
size-6 classes coexist.
-/

open Polynomial
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [Field F]

section ThreeClassCollapse

/-- A degree-`≤ 2` polynomial vanishing at two distinct points is a scalar
multiple of the monic quadratic with those roots. -/
theorem eq_const_mul_of_degree_le_two_roots {f : F[X]} {a b : F}
    (hab : a ≠ b) (hd : f.natDegree ≤ 2)
    (ha : f.eval a = 0) (hb : f.eval b = 0) :
    ∃ c : F, f = C c * ((X - C a) * (X - C b)) := by
  classical
  have hdvd : (X - C a) * (X - C b) ∣ f := by
    have hcop : IsCoprime (X - C a) (X - C b) :=
      isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit (sub_ne_zero.mpr hab))
    exact hcop.mul_dvd
      ((dvd_iff_isRoot).mpr ha) ((dvd_iff_isRoot).mpr hb)
  obtain ⟨c, hc⟩ := hdvd
  have hmdeg : ((X - C a) * (X - C b)).natDegree = 2 := by
    rw [natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b),
      natDegree_X_sub_C, natDegree_X_sub_C]
  have hcdeg : c.natDegree = 0 := by
    rcases eq_or_ne f 0 with rfl | hf
    · rw [zero_eq_mul] at hc
      rcases hc with h | h
      · exact absurd h (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
      · rw [h, natDegree_zero]
    · have hcne : c ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hc; exact hf hc
      have := congrArg natDegree hc
      rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)) hcne,
        hmdeg] at this
      omega
  obtain ⟨k, hk⟩ := Polynomial.natDegree_eq_zero.mp hcdeg
  exact ⟨k, by rw [hc, ← hk]; ring⟩

/-- **The three-class collapse.**  Three degree-`< 3` polynomials whose
pairwise differences vanish on 2-point overlaps, with the overlap monic
quadratics linearly independent, must all coincide. -/
theorem three_class_collapse {q₁ q₂ q₃ : F[X]}
    {a₁ b₁ a₂ b₂ a₃ b₃ : F}
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂) (hab₃ : a₃ ≠ b₃)
    (hd₁ : (q₁ - q₂).natDegree ≤ 2)
    (hd₂ : (q₂ - q₃).natDegree ≤ 2)
    (hd₃ : (q₃ - q₁).natDegree ≤ 2)
    (hv₁a : (q₁ - q₂).eval a₁ = 0) (hv₁b : (q₁ - q₂).eval b₁ = 0)
    (hv₂a : (q₂ - q₃).eval a₂ = 0) (hv₂b : (q₂ - q₃).eval b₂ = 0)
    (hv₃a : (q₃ - q₁).eval a₃ = 0) (hv₃b : (q₃ - q₁).eval b₃ = 0)
    (hindep : ∀ c d e : F,
      C c * ((X - C a₁) * (X - C b₁))
        + C d * ((X - C a₂) * (X - C b₂))
        + C e * ((X - C a₃) * (X - C b₃)) = 0 →
      c = 0 ∧ d = 0 ∧ e = 0) :
    q₁ = q₂ ∧ q₂ = q₃ := by
  obtain ⟨c, hc⟩ := eq_const_mul_of_degree_le_two_roots hab₁ hd₁ hv₁a hv₁b
  obtain ⟨d, hd⟩ := eq_const_mul_of_degree_le_two_roots hab₂ hd₂ hv₂a hv₂b
  obtain ⟨e, he⟩ := eq_const_mul_of_degree_le_two_roots hab₃ hd₃ hv₃a hv₃b
  have hcycle : C c * ((X - C a₁) * (X - C b₁))
      + C d * ((X - C a₂) * (X - C b₂))
      + C e * ((X - C a₃) * (X - C b₃)) = 0 := by
    rw [← hc, ← hd, ← he]; ring
  obtain ⟨hc0, hd0, he0⟩ := hindep c d e hcycle
  rw [hc0, map_zero, zero_mul] at hc
  rw [hd0, map_zero, zero_mul] at hd
  exact ⟨sub_eq_zero.mp hc, sub_eq_zero.mp hd⟩

end ThreeClassCollapse

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.eq_const_mul_of_degree_le_two_roots
#print axioms ProximityGap.WBPencil.three_class_collapse
