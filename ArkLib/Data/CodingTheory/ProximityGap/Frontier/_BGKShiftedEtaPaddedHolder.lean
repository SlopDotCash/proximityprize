/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKFourteenFactorYoung
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# Root-free generalized Holder for coefficient-shifted Gauss periods

The Newton--Mobius expansion of the repeated depth-seven sector contains monomials

`prod_(j < k) |eta_(c_j b)|`, with `k <= 13` and `c_j` among `1, ..., 7`.

Multiplication by every nonzero coefficient permutes the nonzero frequencies.  Hence each shifted
factor has the same fourteenth-moment budget

`M14 = sum_(b != 0) |eta_b|^14`.

Choose a padding scale `R` satisfying `(q - 1) * R^14 = M14`.  Padding a `k`-factor monomial by
`14-k` copies of `R` makes all fourteen factors have exactly the same budget.  The finite
fourteen-factor Young inequality then gives, without introducing fractional powers,

`R^(14-k) * sum_(b != 0) prod_j |eta_(c_j b)| <= M14`.

This file proves the finite-family padding adapter, the nonzero-frequency dilation identity, and
the specialization to coefficients `1, ..., 7` in characteristic greater than seven.  It first
exposes the root-free witness equation for `R`, then discharges it with the canonical NNReal
fourteenth root of the moment average, including the zero-moment case.  Issue #466.
-/

set_option autoImplicit false

open scoped BigOperators NNReal
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung

namespace ArkLib.ProximityGap.Frontier.BGKShiftedEtaPaddedHolder

/-! ## Generic optimized padding -/

/-- Root-free generalized Holder for `k <= 14` factors with a common fourteenth-moment budget.
The last `14-k` factors are constant padding. -/
theorem finite_family_padded_holder
    {B : Type*} [Fintype B] (k : Nat) (hk : k <= 14) (R M : NNReal)
    (f : Fin k -> B -> NNReal)
    (hfactor : forall j, (∑ b, f j b ^ 14) <= M)
    (hpadding : (Fintype.card B : NNReal) * R ^ 14 <= M) :
    R ^ (14 - k) * (∑ b, ∏ j, f j b) <= M := by
  let hsize : k + (14 - k) = 14 := Nat.add_sub_of_le hk
  let e : (Fin k ⊕ Fin (14 - k)) ≃ Fin 14 :=
    finSumFinEquiv.trans (finCongr hsize)
  let mono : B -> NNReal := fun b => ∏ j, f j b
  let z : B -> Fin 14 -> NNReal := fun b i =>
    (e.symm i).elim (fun j => f j b) (fun _ => R)
  have hprod : forall b, ∏ i, z b i = R ^ (14 - k) * mono b := by
    intro b
    calc
      (∏ i, z b i) = ∏ t : Fin k ⊕ Fin (14 - k), z b (e t) := by
        symm
        exact e.prod_comp (z b)
      _ = (∏ j : Fin k, f j b) * ∏ _j : Fin (14 - k), R := by
        rw [Fintype.prod_sum_type]
        simp [z, e]
      _ = R ^ (14 - k) * mono b := by
        simp [mono, mul_comm]
  have hbudget : forall i, (∑ b, z b i ^ 14) <= M := by
    intro i
    obtain ⟨j | j, rfl⟩ := e.surjective i
    · simpa [z, e] using hfactor j
    · simpa [z, e] using hpadding
  exact optimized_padded_holder k R M mono z hprod hbudget

/-! ## Dilation of the nonzero frequency line -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The unit index is exactly the usual deleted zero-frequency sum. -/
theorem sum_units_eq_sum_erase (g : F -> NNReal) :
    (∑ b : Fˣ, g (b : F)) = ∑ b ∈ Finset.univ.erase (0 : F), g b := by
  calc
    (∑ b : Fˣ, g (b : F)) = ∑ b : {b : F // b ≠ 0}, g b := by
      exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
    _ = ∑ b ∈ Finset.univ.erase (0 : F), g b := by
      exact (Finset.sum_subtype (Finset.univ.erase (0 : F))
        (fun b => by simp [Finset.mem_erase]) g).symm

/-- Multiplication by a unit merely reindexes the nonzero-frequency fourteenth moment. -/
theorem sum_eta_nnnorm_pow_fourteen_mul_unit
    (psi : AddChar F Complex) (G : Finset F) (c : Fˣ) :
    (∑ b : Fˣ, ‖eta psi G ((c * b : Fˣ) : F)‖₊ ^ 14) =
      ∑ b : Fˣ, ‖eta psi G (b : F)‖₊ ^ 14 := by
  simpa using
    (Equiv.sum_comp (Equiv.mulLeft c)
      (fun b : Fˣ => ‖eta psi G (b : F)‖₊ ^ 14))

/-- The common nonzero-frequency fourteenth-moment budget, indexed by the canonical unit model
of `F \ {0}`. -/
noncomputable def nonzeroFourteenthMoment
    (psi : AddChar F Complex) (G : Finset F) : NNReal :=
  ∑ b : Fˣ, ‖eta psi G (b : F)‖₊ ^ 14

/-- Canonical padding scale: the fourteenth root of the nonzero-frequency moment average. -/
noncomputable def canonicalPaddingScale
    (psi : AddChar F Complex) (G : Finset F) : NNReal :=
  (nonzeroFourteenthMoment psi G / (Fintype.card Fˣ : NNReal)) ^ ((14 : Real)⁻¹)

/-- The canonical scale has exactly the padding budget required by optimized Young.  This is
uniform when the moment vanishes; no positivity hypothesis on the moment is needed. -/
theorem canonicalPaddingScale_spec (psi : AddChar F Complex) (G : Finset F) :
    (Fintype.card Fˣ : NNReal) * canonicalPaddingScale psi G ^ 14 =
      nonzeroFourteenthMoment psi G := by
  have hcard : (Fintype.card Fˣ : NNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Fˣ).ne'
  have hroot : canonicalPaddingScale psi G ^ 14 =
      nonzeroFourteenthMoment psi G / (Fintype.card Fˣ : NNReal) := by
    unfold canonicalPaddingScale
    convert NNReal.rpow_inv_natCast_pow
      (nonzeroFourteenthMoment psi G / (Fintype.card Fˣ : NNReal))
      (by norm_num : (14 : Nat) ≠ 0) using 1 <;> norm_num
  rw [hroot]
  exact mul_div_cancel₀ _ hcard

/-- **Coefficient-shifted eta Holder adapter.**  Any `k <= 14` nonzero coefficient shifts obey
the same root-free bound.  The equation `#Fˣ * R^14 = M14` is the exact scale witness remaining. -/
theorem shifted_eta_padded_holder
    (psi : AddChar F Complex) (G : Finset F) (k : Nat) (hk : k <= 14)
    (coeff : Fin k -> Fˣ) (R : NNReal)
    (hscale : (Fintype.card Fˣ : NNReal) * R ^ 14 = nonzeroFourteenthMoment psi G) :
    R ^ (14 - k) *
        (∑ b : Fˣ, ∏ j, ‖eta psi G (((coeff j) * b : Fˣ) : F)‖₊) <=
      nonzeroFourteenthMoment psi G := by
  apply finite_family_padded_holder k hk R (nonzeroFourteenthMoment psi G)
      (fun j b => ‖eta psi G (((coeff j) * b : Fˣ) : F)‖₊)
  · intro j
    exact (sum_eta_nnnorm_pow_fourteen_mul_unit psi G (coeff j)).le
  · exact hscale.le

/-! ## The production coefficient alphabet `1, ..., 7` -/

omit [Fintype F] [DecidableEq F] in
/-- In characteristic greater than seven, each integer `1, ..., 7` is nonzero. -/
theorem small_natCast_ne_zero (hchar : 7 < ringChar F) (a : Nat) (ha0 : 0 < a) (ha7 : a <= 7) :
    (a : F) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff F (ringChar F)]
  intro hdiv
  have hchar_le : ringChar F <= a := Nat.le_of_dvd (by omega) hdiv
  omega

/-- The unit represented by the `j`-th member of the coefficient alphabet `1, ..., 7`. -/
noncomputable def smallCoefficientUnit (hchar : 7 < ringChar F) (j : Fin 7) : Fˣ :=
  Units.mk0 ((j.val + 1 : Nat) : F)
    (small_natCast_ne_zero hchar (j.val + 1) (by omega) (by omega))

/-- **Production specialization.**  A Newton monomial of any length `k <= 13`, with every shift
selected from `1, ..., 7`, satisfies the optimized root-free Holder bound. -/
theorem production_small_shift_padded_holder
    (psi : AddChar F Complex) (G : Finset F) (hchar : 7 < ringChar F)
    (k : Nat) (hk : k <= 13) (which : Fin k -> Fin 7) (R : NNReal)
    (hscale : (Fintype.card Fˣ : NNReal) * R ^ 14 = nonzeroFourteenthMoment psi G) :
    R ^ (14 - k) *
        (∑ b : Fˣ, ∏ j,
          ‖eta psi G (((smallCoefficientUnit hchar (which j)) * b : Fˣ) : F)‖₊) <=
      nonzeroFourteenthMoment psi G := by
  apply shifted_eta_padded_holder psi G k (by omega)
    (fun j => smallCoefficientUnit hchar (which j)) R hscale

/-- Witness-free production form.  The canonical scale discharges the sole root interface in
`production_small_shift_padded_holder`; all coefficients `1, ..., 7` are handled uniformly. -/
theorem production_small_shift_holder_canonical
    (psi : AddChar F Complex) (G : Finset F) (hchar : 7 < ringChar F)
    (k : Nat) (hk : k <= 13) (which : Fin k -> Fin 7) :
    canonicalPaddingScale psi G ^ (14 - k) *
        (∑ b : Fˣ, ∏ j,
          ‖eta psi G (((smallCoefficientUnit hchar (which j)) * b : Fˣ) : F)‖₊) <=
      nonzeroFourteenthMoment psi G := by
  exact production_small_shift_padded_holder psi G hchar k hk which
    (canonicalPaddingScale psi G) (canonicalPaddingScale_spec psi G)

/-- Deleted-zero-frequency spelling of `production_small_shift_holder_canonical`. -/
theorem production_small_shift_holder_canonical_erase
    (psi : AddChar F Complex) (G : Finset F) (hchar : 7 < ringChar F)
    (k : Nat) (hk : k <= 13) (which : Fin k -> Fin 7) :
    canonicalPaddingScale psi G ^ (14 - k) *
        (∑ b ∈ Finset.univ.erase (0 : F), ∏ j,
          ‖eta psi G ((smallCoefficientUnit hchar (which j) : F) * b)‖₊) <=
      nonzeroFourteenthMoment psi G := by
  have h := production_small_shift_holder_canonical psi G hchar k hk which
  have hsum :
      (∑ b : Fˣ, ∏ j,
          ‖eta psi G (((smallCoefficientUnit hchar (which j)) * b : Fˣ) : F)‖₊) =
        ∑ b ∈ Finset.univ.erase (0 : F), ∏ j,
          ‖eta psi G ((smallCoefficientUnit hchar (which j) : F) * b)‖₊ := by
    simpa using sum_units_eq_sum_erase (F := F)
      (fun b => ∏ j, ‖eta psi G ((smallCoefficientUnit hchar (which j) : F) * b)‖₊)
  rw [hsum] at h
  exact h

#print axioms finite_family_padded_holder
#print axioms sum_units_eq_sum_erase
#print axioms sum_eta_nnnorm_pow_fourteen_mul_unit
#print axioms shifted_eta_padded_holder
#print axioms canonicalPaddingScale_spec
#print axioms small_natCast_ne_zero
#print axioms production_small_shift_padded_holder
#print axioms production_small_shift_holder_canonical
#print axioms production_small_shift_holder_canonical_erase

end ArkLib.ProximityGap.Frontier.BGKShiftedEtaPaddedHolder
