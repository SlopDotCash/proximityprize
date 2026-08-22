/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKSpecialCoefficientKernel
import ArkLib.Data.CodingTheory.ProximityGap.StepanovGeneratorIndep

/-!
# Nonvanishing of the HBK specialization

HBK specialize a box polynomial by `(Y,Z)=(X^h,(X-1)^h)`.  Grouping by the `Z` exponent gives
valuation blocks `(X-1)^{hc} P_c(X)`.  Each `P_c` has at most `AB` distinct exponents `a+hb`;
when `A≤h` these are distinct, and when `AB≤h` the sparse-multiplicity theorem gives
`ord_1(P_c)<h`.  The valuation blocks are disjoint, so a nonzero coefficient tensor cannot
specialize to zero.  This is HBK Lemma 6 in the exact form needed by Lemma 5. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKSpecializationNonzero

open scoped BigOperators
open Polynomial
open ArkLib.ProximityGap.Wronskian
open HBKSpecialCoefficientKernel

variable {F : Type*} [Field F]

private def pairIndex (A B : ℕ) (j : Fin (A * B)) : Fin A × Fin B :=
  finProdFinEquiv.symm j

/-- The exponent `a+hb` appearing after substituting `Y=X^h`. -/
def specializedExponent (h A B : ℕ) (j : Fin (A * B)) : ℕ :=
  (pairIndex A B j).1 + h * (pairIndex A B j).2

/-- The `c`-th sparse coefficient block after substituting `Y=X^h`. -/
noncomputable def coefficientBlock (h A B : ℕ) (coeffs : CoeffSpace F A B) (c : Fin B) : F[X] :=
  ∑ j : Fin (A * B),
    C (coeffs ((pairIndex A B j).1, (pairIndex A B j).2, c)) *
      X ^ specializedExponent h A B j

/-- The univariate HBK specialization `Φ(X,X^h,(X-1)^h)`, grouped into valuation blocks. -/
noncomputable def specializedAuxiliary (h A B : ℕ) (coeffs : CoeffSpace F A B) : F[X] :=
  ∑ c : Fin B, (X - 1) ^ (h * (c : ℕ)) * coefficientBlock h A B coeffs c

/-- Base-`h` exponents in the box are distinct when `A≤h`. -/
theorem specializedExponent_injective {h A B : ℕ} (hA : A ≤ h) :
    Function.Injective (specializedExponent h A B) := by
  intro i j hij
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · have hiA : ((pairIndex A B i).1 : ℕ) < h :=
      lt_of_lt_of_le (pairIndex A B i).1.isLt hA
    have hjA : ((pairIndex A B j).1 : ℕ) < h :=
      lt_of_lt_of_le (pairIndex A B j).1.isLt hA
    have hmod := congrArg (fun x : ℕ => x % h) hij
    have hmod' : ((pairIndex A B i).1 : ℕ) = (pairIndex A B j).1 := by
      simpa only [specializedExponent, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hiA, Nat.mod_eq_of_lt hjA] using hmod
    exact Fin.ext hmod'
  · have ha : (pairIndex A B i).1 = (pairIndex A B j).1 := by
      have hiA : ((pairIndex A B i).1 : ℕ) < h :=
        lt_of_lt_of_le (pairIndex A B i).1.isLt hA
      have hjA : ((pairIndex A B j).1 : ℕ) < h :=
        lt_of_lt_of_le (pairIndex A B j).1.isLt hA
      have hmod := congrArg (fun x : ℕ => x % h) hij
      have hmod' : ((pairIndex A B i).1 : ℕ) = (pairIndex A B j).1 := by
        simpa only [specializedExponent, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hiA, Nat.mod_eq_of_lt hjA] using hmod
      exact Fin.ext hmod'
    simp only [specializedExponent, ha, Nat.add_left_cancel_iff] at hij
    by_cases hh : h = 0
    · have hAz : A = 0 := Nat.eq_zero_of_le_zero (hA.trans_eq hh)
      exact Fin.elim0 (hAz ▸ (pairIndex A B i).1)
    · exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh) hij)

/-- Nonzero tensor coefficients cannot all disappear inside one sparse block family. -/
private theorem coeffs_eq_zero_of_blocks_eq_zero
    {h A B : ℕ} (hinj : Function.Injective (specializedExponent h A B))
    {coeffs : CoeffSpace F A B}
    (hblocks : ∀ c, coefficientBlock h A B coeffs c = 0) : coeffs = 0 := by
  funext p
  obtain ⟨a, b, c⟩ := p
  let j : Fin (A * B) := finProdFinEquiv (a, b)
  have hz := eq_zero_of_sum_monomial_eq_zero hinj (hblocks c)
  have hj := congrFun hz j
  simpa [coefficientBlock, pairIndex, j] using hj

/-- **HBK specialization nonvanishing.**  The sparse multiplicity/Vandermonde hypothesis is the
characteristic-faithful form of `deg < p` in HBK Lemma 6. -/
theorem specializedAuxiliary_ne_zero
    {h A B : ℕ} (hA : A ≤ h) (hAB : A * B ≤ h)
    (hvand :
      (Matrix.vandermonde (fun j : Fin (A * B) =>
        (specializedExponent h A B j : F))).det ≠ 0)
    {coeffs : CoeffSpace F A B} (hne : coeffs ≠ 0) :
    specializedAuxiliary h A B coeffs ≠ 0 := by
  intro hzero
  have hinj := specializedExponent_injective (B := B) hA
  have hblocks : ∀ c, coefficientBlock h A B coeffs c = 0 := by
    apply eq_zero_of_sum_pow_block (1 : F) h
    · intro c hc
      exact lt_of_lt_of_le
        (rootMultiplicity_sparse_lt
          (specializedExponent h A B)
          (fun j => coeffs ((pairIndex A B j).1, (pairIndex A B j).2, c))
          1 one_ne_zero hvand hc) hAB
    · exact hzero
  exact hne (coeffs_eq_zero_of_blocks_eq_zero hinj hblocks)

/-- HBK's original `deg < char` hypothesis supplies the Vandermonde condition automatically. -/
theorem specializedVandermonde_ne_zero_of_charP
    {p h A B : ℕ} [CharP F p] (hA : A ≤ h) (hdeg : A + h * B ≤ p) :
    (Matrix.vandermonde (fun j : Fin (A * B) =>
      (specializedExponent h A B j : F))).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  have hinj := specializedExponent_injective (B := B) hA
  apply hinj
  apply CharP.natCast_injOn_Iio F p
  · have ha := (pairIndex A B i).1.isLt
    have hb := (pairIndex A B i).2.isLt
    have hh : 0 < h := lt_of_lt_of_le (pairIndex A B i).1.pos hA
    dsimp [specializedExponent]
    exact (Nat.add_lt_add ha ((Nat.mul_lt_mul_left hh).2 hb)).trans_le hdeg
  · have ha := (pairIndex A B j).1.isLt
    have hb := (pairIndex A B j).2.isLt
    have hh : 0 < h := lt_of_lt_of_le (pairIndex A B j).1.pos hA
    dsimp [specializedExponent]
    exact (Nat.add_lt_add ha ((Nat.mul_lt_mul_left hh).2 hb)).trans_le hdeg
  · exact hij

/-- Characteristic-form specialization nonvanishing, matching the hypotheses of HBK Lemma 6. -/
theorem specializedAuxiliary_ne_zero_of_charP
    {p h A B : ℕ} [CharP F p] (hA : A ≤ h) (hAB : A * B ≤ h)
    (hdeg : A + h * B ≤ p) {coeffs : CoeffSpace F A B} (hne : coeffs ≠ 0) :
    specializedAuxiliary h A B coeffs ≠ 0 :=
  specializedAuxiliary_ne_zero hA hAB
    (specializedVandermonde_ne_zero_of_charP hA hdeg) hne

end ArkLib.ProximityGap.Frontier.HBKSpecializationNonzero

#print axioms ArkLib.ProximityGap.Frontier.HBKSpecializationNonzero.specializedExponent_injective
#print axioms ArkLib.ProximityGap.Frontier.HBKSpecializationNonzero.specializedAuxiliary_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.HBKSpecializationNonzero.specializedAuxiliary_ne_zero_of_charP
