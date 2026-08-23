/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24SymbolicRank
import ArkLib.Data.CodingTheory.AGL24Submatrix

/-!
# [AGL24] the nonzero polynomial minor from the symbolic interface (issue #354, stage 1)

The bridge from the symbolic Theorem 2.11 interface to a concrete *nonzero polynomial
determinant* — the object Schwartz–Zippel can price:

* `frac_kernel_trivial_of_poly_kernel_trivial` — denominator clearing: trivial kernel over
  the polynomial ring lifts to the fraction field (`IsLocalization.exist_integer_multiples`);
* `exists_nonzero_poly_minor` — **the minor**: under the symbolic interface, every
  weakly-partition-connected RIM has a square submatrix whose *polynomial* determinant is
  nonzero (brick 15's extraction at the fraction field + `RingHom.map_det` descent).
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- **Denominator clearing**: a matrix over a domain with trivial kernel over the ring has
trivial kernel over its fraction field. -/
theorem frac_kernel_trivial_of_poly_kernel_trivial
    {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    {A : Type*} [CommRing A] [IsDomain A]
    (M : Matrix R C A)
    (h : ∀ v : C → A, M.mulVec v = 0 → v = 0)
    (v : C → FractionRing A)
    (hv : (M.map (algebraMap A (FractionRing A))).mulVec v = 0) :
    v = 0 := by
  classical
  -- A common integer multiplier for the finitely many entries of v.
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors A) (Finset.univ : Finset C) v
  choose w hw using fun c => hb c (Finset.mem_univ c)
  -- w is a polynomial kernel vector.
  have hwker : M.mulVec w = 0 := by
    funext r
    have hrow := congrFun hv r
    rw [show (0 : R → FractionRing A) r = 0 from rfl] at hrow
    -- Multiply the row equation by b.
    have hmul : (algebraMap A (FractionRing A)) (M.mulVec w r) = 0 := by
      rw [show M.mulVec w r = ∑ c, M r c * w c from rfl]
      rw [map_sum]
      have : ∀ c, (algebraMap A (FractionRing A)) (M r c * w c)
          = (M.map (algebraMap A (FractionRing A))) r c * ((b : A) • v c) := by
        intro c
        rw [map_mul, hw c]
        rfl
      rw [Finset.sum_congr rfl fun c _ => this c]
      rw [show ∑ c, (M.map (algebraMap A (FractionRing A))) r c * ((b : A) • v c)
          = (b : A) • ∑ c, (M.map (algebraMap A (FractionRing A))) r c * v c from by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun c _ => by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring]
      rw [show ∑ c, (M.map (algebraMap A (FractionRing A))) r c * v c
          = (M.map (algebraMap A (FractionRing A))).mulVec v r from rfl]
      rw [hrow, smul_zero]
    have hinj := IsFractionRing.injective A (FractionRing A)
    have := hmul
    rw [show (0 : FractionRing A) = (algebraMap A (FractionRing A)) 0 from (map_zero _).symm]
      at this
    exact hinj this
  -- Hence w = 0, so b • v = 0, so v = 0 (b is a nonzerodivisor).
  have hw0 : w = 0 := h w hwker
  funext c
  have : (algebraMap A (FractionRing A)) (w c) = (b : A) • v c := hw c
  rw [hw0] at this
  rw [show (0 : C → A) c = 0 from rfl, map_zero] at this
  have hbne : (algebraMap A (FractionRing A)) (b : A) ≠ 0 := by
    intro hzero
    have := IsFractionRing.injective A (FractionRing A)
      (by rw [hzero, map_zero] : (algebraMap A (FractionRing A)) (b : A)
        = (algebraMap A (FractionRing A)) 0)
    exact nonZeroDivisors.coe_ne_zero b this
  have hsmul : (b : A) • v c = (algebraMap A (FractionRing A)) (b : A) * v c := by
    rw [Algebra.smul_def]
  rw [hsmul] at this
  rw [show (0 : C → FractionRing A) c = 0 from rfl]
  rcases mul_eq_zero.mp this.symm with h1 | h2
  · exact absurd h1 hbne
  · exact h2

/-- **The nonzero polynomial minor**: under the symbolic Theorem 2.11 interface, every
weakly-partition-connected RIM admits an injective row selection whose square submatrix has
nonzero determinant *as a polynomial*. -/
theorem exists_nonzero_poly_minor {k : ℕ}
    (hsym : SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e) :
    ∃ rows : Fin t × Fin k → RIMRowIdx e, Function.Injective rows ∧
      ((RIM F e).submatrix rows id).det ≠ 0 := by
  classical
  set K := FractionRing (MvPolynomial ι F)
  -- The fraction-field kernel is trivial.
  have hfrac : ∀ v : Fin t × Fin k → K,
      ((RIM F e).map (algebraMap (MvPolynomial ι F) K)).mulVec v = 0 → v = 0 :=
    frac_kernel_trivial_of_poly_kernel_trivial (RIM F e) (hsym ht e hwpc)
  -- Brick 15 at the fraction field.
  obtain ⟨rows, hinj, hdet⟩ :=
    exists_square_submatrix_det_ne_zero
      ((RIM F e).map (algebraMap (MvPolynomial ι F) K)) hfrac
  refine ⟨rows, hinj, ?_⟩
  -- The determinant descends: nonzero over K means nonzero as a polynomial.
  intro hzero
  apply hdet
  have hcomm : ((RIM F e).map (algebraMap (MvPolynomial ι F) K)).submatrix rows
      (id : Fin t × Fin k → Fin t × Fin k)
      = (((RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).map (algebraMap (MvPolynomial ι F) K)) := rfl
  rw [hcomm]
  rw [show ((((RIM F e).submatrix rows (id : Fin t × Fin k → Fin t × Fin k)).map
      (algebraMap (MvPolynomial ι F) K)).det)
      = (algebraMap (MvPolynomial ι F) K) (((RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).det) from by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]]
  rw [hzero, map_zero]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.frac_kernel_trivial_of_poly_kernel_trivial
#print axioms AGL24.exists_nonzero_poly_minor
