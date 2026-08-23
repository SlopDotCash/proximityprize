/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightClearedObstruction

/-!
# `W = liftToFunctionField H.leadingCoeff` is not a root of unity (non-monic `H`)

Reusable `W`-power bookkeeping for the BCIKS20 Appendix-A clearing identities. The `W`/`ξ`
denominators in `βHensel`, `B_coeff`, and the `RestrictedFaaDiBrunoMatch` keystone carry powers of
`W = liftToFunctionField H.leadingCoeff`; comparisons like `W^d = W^{natDegreeY p}` reduce to the
exponents only when `W` has no finite multiplicative order — which holds exactly when `H` is
non-monic (`H.leadingCoeff` a non-unit).

## Main results

* `liftToFunctionField_injective` — a public form of the field-coefficient embedding's injectivity
  (a constant `C a` lies below the modulus `H̃`, so `liftBivariate (C a) = liftToFunctionField a`
  is faithful by `liftBivariate_eq_zero_of_natDegree_lt`).
* `leadingCoeff_pow_inj` — for non-monic `H`, `H.leadingCoeff ^ a = H.leadingCoeff ^ b → a = b`.
* `W_pow_eq_iff` — `W ^ a = W ^ b ↔ a = b`. The tool for reducing `W`-power identities to their
  exponents (e.g. the order-0 keystone's `W^{R.natDegree}` vs `W^{natDegreeY p}` mismatch).
-/

open scoped BigOperators
open Polynomial Polynomial.Bivariate ToRatFunc BCIKS20AppendixA
open BCIKS20.HenselNumerator ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.AlphaWeightClearedObstruction

namespace BCIKS20.WPow

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Fact (Irreducible H)] in
/-- `liftToFunctionField` is injective: a constant `C a` has `Y`-degree `0 < H.natDegree`, so it
sits below the modulus `H̃` and `liftBivariate (C a) = liftToFunctionField a` is faithful
(`liftBivariate_eq_zero_of_natDegree_lt`). -/
theorem liftToFunctionField_injective :
    Function.Injective (liftToFunctionField (H := H)) := by
  intro a b hab
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hz : liftBivariate (H := H) (Polynomial.C a - Polynomial.C b) = 0 := by
    rw [map_sub, liftBivariate_C, liftBivariate_C, hab, sub_self]
  have hdeg : (Polynomial.C a - Polynomial.C b : F[X][Y]).natDegree < H.natDegree := by
    rw [← Polynomial.C_sub, Polynomial.natDegree_C]; exact hHdeg
  have h0 := liftBivariate_eq_zero_of_natDegree_lt H hz hdeg
  rw [← Polynomial.C_sub] at h0
  exact sub_eq_zero.mp (Polynomial.C_eq_zero.mp h0)

omit [Fact (Irreducible H)] in
/-- For non-monic `H` (`H.leadingCoeff` a non-unit) the leading coefficient has no finite
multiplicative order: `lc ^ a = lc ^ b → a = b`. -/
theorem leadingCoeff_pow_inj (hlc : ¬ IsUnit H.leadingCoeff) {a b : ℕ}
    (h : H.leadingCoeff ^ a = H.leadingCoeff ^ b) : a = b := by
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  have hlc0 : H.leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.2
    intro hH0; rw [hH0, Polynomial.natDegree_zero] at hHdeg; omega
  have key : ∀ {m n : ℕ}, m ≤ n → H.leadingCoeff ^ m = H.leadingCoeff ^ n → m = n := by
    intro m n hmn hmn_eq
    by_contra hne
    have hpos : 1 ≤ n - m := by omega
    have hb : H.leadingCoeff ^ m * H.leadingCoeff ^ (n - m) = H.leadingCoeff ^ m := by
      rw [← pow_add, show m + (n - m) = n by omega, ← hmn_eq]
    have h1 : H.leadingCoeff ^ (n - m) = 1 :=
      mul_left_cancel₀ (pow_ne_zero m hlc0) (by rw [hb, mul_one])
    exact hlc (IsUnit.of_mul_eq_one (H.leadingCoeff ^ (n - m - 1))
      (by rw [← pow_succ', Nat.sub_add_cancel hpos]; exact h1))
  rcases Nat.le_total a b with hab | hab
  · exact key hab h
  · exact (key hab h.symm).symm

omit [Fact (Irreducible H)] in
/-- **`W = liftToFunctionField H.leadingCoeff` is not a root of unity** for non-monic `H`:
`W ^ a = W ^ b ↔ a = b`.  The tool for the `W`-power bookkeeping in the (P1)/(P2) clearing
identities (e.g. reducing the order-0 keystone's `W^{R.natDegree}` vs `W^{natDegreeY p}` to the
exponent equality). -/
theorem W_pow_eq_iff (hlc : ¬ IsUnit H.leadingCoeff) (a b : ℕ) :
    (liftToFunctionField (H := H) H.leadingCoeff) ^ a
      = (liftToFunctionField (H := H) H.leadingCoeff) ^ b ↔ a = b := by
  rw [← map_pow, ← map_pow]
  refine ⟨fun h => leadingCoeff_pow_inj H hlc (liftToFunctionField_injective H h), ?_⟩
  rintro rfl; rfl

end BCIKS20.WPow

section Audit
open BCIKS20.WPow
#print axioms liftToFunctionField_injective
#print axioms leadingCoeff_pow_inj
#print axioms W_pow_eq_iff
end Audit
