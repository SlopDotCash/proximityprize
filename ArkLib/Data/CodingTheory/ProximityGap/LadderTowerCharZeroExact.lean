/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NewtonPowerSumWindow
import ArkLib.Data.CodingTheory.ProximityGap.CensusTowerDescent
import ArkLib.Data.CodingTheory.ProximityGap.KKH26GapCensusLaw
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The general dyadic-tower exact upper structure (#389): the WHOLE line in char 0

This closes the exact sub-Johnson list law for **every** dyadic tower (stride `m = 2^a`),
not just the squaring tower (`a = 1`).  Combining three pieces — all now in-tree:

* the Newton bridge `psum_window_zero_of_esymm_window_zero` (esymm-window ⟹ psum-window);
* Vieta `Multiset.prod_X_sub_C_coeff` (coefficients = elementary symmetric of roots);
* the 2-adic tower descent `tower_closed_of_dyadic_sums_zero` (dyadic power sums ⟹
  order-`2^a` closure)

— gives:

> **`ladder_tower_fiberClosed_charZero`** — over a `2^μ`-th-root domain in a
> characteristic-zero field, every `GapBand` solution `T` of the stride-`2^a` ladder stack
> `(X^{r·2^a}, X^{(r−1)·2^a})` is **closed under the order-`2^a` subgroup** — a union of
> `r` fibres of `x ↦ x^{2^a}`.

With `fiberUnion_gapBand` (the converse), the char-0 ladder census at agreement `r·2^a` is
**exactly** the `2^a`-fibre family, for every `a` and `r` — so the exact sub-Johnson list
size `= N_fib` at every dyadic agreement level.  The whole line, in characteristic zero,
no wall.  (Finite-field statement above the resultant transfer threshold; the deployed
`ε* = 2^{−128}` regime sits far above it.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial Finset MvPolynomial

namespace ArkLib.ProximityGap.KKH26

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **THE GENERAL DYADIC-TOWER EXACT UPPER STRUCTURE (char 0).** -/
theorem ladder_tower_fiberClosed_charZero {ζ : L} {μ a : ℕ} (haμ : a ≤ μ) (ha : 1 ≤ a)
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {r : ℕ} (hr : 2 ≤ r)
    {T : Finset L} (hT : ∀ x ∈ T, x ^ (2 ^ μ) = 1) (hTcard : T.card = r * 2 ^ a)
    {lam : L} (hband : GapBand T (r * 2 ^ a) ((r - 1) * 2 ^ a) ((r - 2) * 2 ^ a + 1) lam) :
    ∀ x ∈ T, ζ ^ (2 ^ (μ - a)) * x ∈ T := by
  classical
  set P : ℕ := 2 ^ a with hPdef
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  set A : ℕ := r * P with hAdef
  -- the window arithmetic, all linear in A, P
  have hBA : (r - 1) * P = A - P := by rw [hAdef, Nat.sub_mul, one_mul]
  have hkA : (r - 2) * P + 1 = A - 2 * P + 1 := by rw [hAdef, Nat.sub_mul]
  have h2PA : 2 * P ≤ A := by rw [hAdef]; exact Nat.mul_le_mul hr (le_refl P)
  -- Step 1: the elementary symmetric functions of T's roots vanish on [1, P−1].
  have hcardval : Multiset.card T.val = A := by rw [← hTcard]; rfl
  have hesymm : ∀ c, 1 ≤ c → c < P → T.val.esymm c = 0 := by
    intro c hc1 hcP
    have hmc : (r - 2) * P + 1 ≤ A - c ∧ A - c < A ∧ A - c ≠ (r - 1) * P := by
      rw [hBA, hkA]; omega
    have hcoeff0 : (∏ x ∈ T, (Polynomial.X - Polynomial.C x)).coeff (A - c) = 0 :=
      hband.1 (A - c) hmc.1 hmc.2.1 hmc.2.2
    have hprodeq : (∏ x ∈ T, (Polynomial.X - Polynomial.C x))
        = (T.val.map fun t => Polynomial.X - Polynomial.C t).prod := rfl
    have hcle : A - c ≤ Multiset.card T.val := by rw [hcardval]; omega
    have hvieta := Multiset.prod_X_sub_C_coeff T.val hcle
    rw [hcardval] at hvieta
    have hAcc : A - (A - c) = c := by omega
    rw [hAcc] at hvieta
    rw [hprodeq, hvieta] at hcoeff0
    have hunit : ((-1 : L) ^ c) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp hcoeff0).resolve_left hunit
  -- Step 2: the power sums vanish on [1, P−1] (Newton bridge over the subtype ↥T).
  have hmap : (Finset.univ.val.map (Subtype.val : {x // x ∈ T} → L)) = T.val := by
    rw [Finset.univ_eq_attach, Finset.attach_val]; exact Multiset.attach_map_val T.val
  have haevalesymm : ∀ c, 1 ≤ c → c < P →
      aeval (Subtype.val : {x // x ∈ T} → L) (esymm {x // x ∈ T} ℤ c) = 0 := by
    intro c hc1 hcP
    rw [aeval_esymm_eq_multiset_esymm, hmap]
    exact hesymm c hc1 hcP
  have hpsum : ∀ k, 1 ≤ k → k < P → ∑ x ∈ T, x ^ k = 0 := by
    intro k hk1 hkP
    have hnewton := psum_window_zero_of_esymm_window_zero
      (σ := {x // x ∈ T}) (f := (Subtype.val : {x // x ∈ T} → L)) (j := P)
      haevalesymm k hk1 hkP
    rwa [Finset.sum_coe_sort T (fun x => x ^ k)] at hnewton
  -- Step 3: the dyadic power sums vanish (2^i < 2^a = P for i < a).
  have hdyadic : ∀ i, i < a → ∑ x ∈ T, x ^ (2 ^ i) = 0 := by
    intro i hi
    refine hpsum (2 ^ i) Nat.one_le_two_pow ?_
    rw [hPdef]
    exact Nat.pow_lt_pow_right (by norm_num) hi
  -- Step 4: the in-tree tower descent gives order-2^a closure.
  exact tower_closed_of_dyadic_sums_zero a μ haμ hζ T hT hdyadic

end ArkLib.ProximityGap.KKH26

#print axioms ArkLib.ProximityGap.KKH26.ladder_tower_fiberClosed_charZero
