/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import Research.ProximityPrize.Frontier._HDdNodeTranslation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# HDd — the `(g₁, g₂)` bigrading of the origin contact substitution

The origin substitution `contactSubstD d 0 0` is homogeneous for the pair grading

* input  weights (`X, Y₀, Y_{j+1}`):  `wIn  i = (g₁, g₂)`-weights `((0,1), (1,0), … )`:
  `g₁`: `X ↦ 0`, `Y₀ ↦ 1`, `Y_{j+1} ↦ 1`;  `g₂`: `X ↦ 1`, `Y₀ ↦ 0`, `Y_{j+1} ↦ −(j+1)`.
* output weights (`T, E, Y_{j+1}`):
  `g₁`: `T ↦ 0`, `E ↦ 1`, `Y_{j+1} ↦ 1`;  `g₂`: `T ↦ 1`, `E ↦ −d`, `Y_{j+1} ↦ −(j+1)`.

`contactSubstD_origin_isWeightedHomogeneous`: the image of a monomial with input pair degree
`c` is weighted homogeneous of the same pair degree `c` for the output weights.  Combined
with `contactSubstD_translate` this puts every node map in block-diagonal form over the
`(g₁, g₂)` blocks, which is what `finrank_span_range_le_sum_min`
(`_HDdCountingBound.lean`) consumes; the remaining assembly is finite reindexing of rows
and columns per block (bookkeeping, not mathematics).
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open MvPolynomial

variable {F : Type*} [CommRing F]

/-- Input pair weights on the variables `(X, Y₀, Y₁, …, Y_d)`. -/
def wIn (d : ℕ) : Fin (d + 2) → ℤ × ℤ :=
  Fin.cons (0, 1) (Fin.cons (1, 0) (fun j : Fin d => (1, -((j : ℤ) + 1))))

/-- Output pair weights on the variables `(T, E, Y₁, …, Y_d)`. -/
def wOut (d : ℕ) : Fin (d + 2) → ℤ × ℤ :=
  Fin.cons (0, 1) (Fin.cons (1, -(d : ℤ)) (fun j : Fin d => (1, -((j : ℤ) + 1))))

theorem isWeightedHomogeneous_X_pow_mul_X {σ : Type*} (w : σ → ℤ × ℤ) (s t : σ) (k : ℕ) :
    IsWeightedHomogeneous w ((X s ^ k * X t : MvPolynomial σ F)) (k • w s + w t) := by
  exact ((isWeightedHomogeneous_X F w s).pow k).mul (isWeightedHomogeneous_X F w t)

/-- Each generator image of the origin substitution is weighted homogeneous of the degree of
the corresponding input variable. -/
theorem contactSubstD_origin_X_homogeneous (d : ℕ) (i : Fin (d + 2)) :
    IsWeightedHomogeneous (wOut d) (contactSubstD d (0 : F) 0 (X i)) (wIn d i) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · -- X ↦ C 0 + T
    simp only [contactSubstD, aeval_X, Fin.cons_zero, map_zero, zero_add, wIn]
    simpa using isWeightedHomogeneous_X F (wOut d) 0
  · -- Y₀ ↦ C 0 + Σ_j C(−1)^j T^{j+1} Y_{j+1} + T^d E
    have h1 : (1 : Fin (d + 2)) = Fin.succ 0 := by ext; simp
    simp only [contactSubstD, aeval_X, h1, Fin.cons_succ, Fin.cons_zero, map_zero, zero_add,
      wIn]
    refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_) ?_
    · -- C(−1)^j * T^{j+1} * Y_{j+1} has pair degree (1, 0)
      have hC : IsWeightedHomogeneous (wOut d)
          ((C ((-1 : F) ^ (j : ℕ)) : MvPolynomial (Fin (d + 2)) F)) 0 :=
        isWeightedHomogeneous_C _ _
      have hXX := isWeightedHomogeneous_X_pow_mul_X (F := F) (wOut d) 0 j.succ.succ
        ((j : ℕ) + 1)
      have hmul := hC.mul hXX
      convert hmul using 1
      · simp only [map_pow, map_neg, map_one]
        ring
      · show ((1 : ℤ), (0 : ℤ)) = 0 + (((j : ℕ) + 1) • wOut d 0 + wOut d j.succ.succ)
        simp only [wOut, Fin.cons_zero, Fin.cons_succ, Prod.smul_mk, smul_eq_mul,
          Prod.mk_add_mk, zero_add, Prod.mk.injEq, mul_zero, mul_one]
        constructor <;> push_cast <;> ring
    · -- T^d * E has pair degree (1, 0)
      have hXX := isWeightedHomogeneous_X_pow_mul_X (F := F) (wOut d) 0 1 d
      have h1' : (1 : Fin (d + 2)) = Fin.succ 0 := by ext; simp
      convert hXX using 1
      show ((1 : ℤ), (0 : ℤ)) = d • wOut d 0 + wOut d 1
      rw [h1']
      simp only [wOut, Fin.cons_zero, Fin.cons_succ, Prod.smul_mk, smul_eq_mul,
        Prod.mk_add_mk, Prod.mk.injEq, mul_zero, mul_one]
      constructor <;> push_cast <;> ring
  · -- Y_{j+1} ↦ Y_{j+1}
    simp only [contactSubstD, aeval_X, Fin.cons_succ, wIn]
    exact isWeightedHomogeneous_X F (wOut d) j.succ.succ

/-- Pair degree of an exponent vector under a pair weighting. -/
noncomputable def pairDeg (w : Fin (d + 2) → ℤ × ℤ) (μ : Fin (d + 2) →₀ ℕ) : ℤ × ℤ :=
  μ.sum fun i k => k • w i

/-- **Monomial images are bigraded.**  The origin substitution maps a monomial with input
pair degree `c` to a polynomial that is weighted homogeneous of pair degree `c` for the
output weights. -/
theorem contactSubstD_origin_monomial_homogeneous (d : ℕ) (μ : Fin (d + 2) →₀ ℕ) (c : F) :
    IsWeightedHomogeneous (wOut d)
      (contactSubstD d (0 : F) 0 (monomial μ c)) (pairDeg (wIn d) μ) := by
  classical
  have hmono : (monomial μ c : MvPolynomial (Fin (d + 2)) F) =
      C c * μ.prod fun i k => X i ^ k := by
    rw [monomial_eq]
  rw [hmono, map_mul]
  have hC : IsWeightedHomogeneous (wOut d)
      (contactSubstD d (0 : F) 0 (C c)) 0 := by
    rw [show (contactSubstD d (0 : F) 0) (C c) = C c from by
      simp [contactSubstD, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]]
    exact isWeightedHomogeneous_C _ _
  have hprod : IsWeightedHomogeneous (wOut d)
      (contactSubstD d (0 : F) 0 (μ.prod fun i k => X i ^ k)) (pairDeg (wIn d) μ) := by
    rw [Finsupp.prod, map_prod]
    unfold pairDeg
    rw [Finsupp.sum]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      rw [map_pow]
      exact (contactSubstD_origin_X_homogeneous d i).pow _
  simpa using hC.mul hprod

/-- **Support invariance.**  Every exponent vector in the support of the origin substitution
of a monomial carries the same output pair degree as the monomial's input pair degree —
the `(g₁, g₂)` block structure of the node maps. -/
theorem weightedDegree_of_mem_support_contactSubstD (d : ℕ) (μin : Fin (d + 2) →₀ ℕ) (c : F)
    (μout : Fin (d + 2) →₀ ℕ)
    (h : μout ∈ (contactSubstD d (0 : F) 0 (monomial μin c)).support) :
    Finsupp.weight (wOut d) μout = pairDeg (wIn d) μin :=
  contactSubstD_origin_monomial_homogeneous d μin c (mem_support_iff.mp h)

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.contactSubstD_origin_X_homogeneous
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.weightedDegree_of_mem_support_contactSubstD
