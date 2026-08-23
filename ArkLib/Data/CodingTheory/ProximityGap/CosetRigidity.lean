/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Rigidity: vanishing-statistic `h`-subsets are exactly cosets (Issue #232)

This is the **converse** to the coset construction of `CosetPowerSumConcentration.lean`. There we
showed that a coset `g·μ_h` of the order-`h` roots of unity kills all the elementary symmetric
functions `e_1, …, e_{h-1}` (its characteristic polynomial is `X^h - g^h`). Here we prove the
sharp converse:

* `all_pow_eq_of_esymm_zero` — if an `h`-element subset `S` of a field has `e_1(S) = … =
  e_{h-1}(S) = 0`, then **every** `x ∈ S` is an `h`-th root of one common constant `c`
  (`x^h = c`). Hence `S ⊆ {x : x^h = c}`, and since `|S| = h = deg(X^h - c)`, `S` is *exactly* the
  root set of `X^h - c` — a coset of `μ_h`.

**Consequence (the exact count at `a = h`).** Combined with the forward direction, the
vanishing-statistic `h`-subsets of the smooth domain `μ_n` are *exactly* the `n/h` cosets of the
order-`h` subgroup. So `CosetPowerSumConcentration.exists_many_vanishing_powersum_subsets` is not
merely a lower bound at `a = h`: the count `C(n/h, 1) = n/h` is **tight** — the coset construction
captures *all* of the concentration at the agreement level equal to the subgroup order. This
upgrades the `decide`-verified `μ_8` tightness witness (`N2(μ_8, 4, 0, 0) = 2`) to a theorem, and
it pins exactly why the coset method, while sharp here, cannot reach deeper: at `a = h` the only
vanishing-statistic subsets are the rigid cosets, leaving no extra freedom to push the depth.

The proof: the monic polynomial `P = ∏_{x∈S}(X - x)` has degree `h` (Vieta /
`natDegree_multiset_prod_X_sub_C_eq_card`); its coefficients `P.coeff k = (-1)^{h-k} e_{h-k}(S)`
vanish for `1 ≤ k ≤ h-1` by hypothesis, so evaluating at any root `x ∈ S` gives
`0 = P.eval x = P.coeff 0 + x^h`, i.e. `x^h = -P.coeff 0` — the same constant for every `x ∈ S`.

All results are `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.Rigidity

variable {F : Type*} [Field F]

/-- **Rigidity of vanishing-symmetric-function `h`-subsets.** If an `h`-element subset `S` of a
field has its first `h-1` elementary symmetric functions all zero, then every element of `S` is an
`h`-th root of one common constant `c`: `∃ c, ∀ x ∈ S, x^h = c`. Since `|S| = h = deg(X^h - c)`,
`S` is exactly the root set of `X^h - c` — a coset of the order-`h` roots of unity. The converse to
the coset construction: vanishing-statistic `h`-subsets are exactly the cosets. -/
theorem all_pow_eq_of_esymm_zero {S : Finset F} {h : ℕ} (hh : 0 < h) (hcard : S.card = h)
    (hesymm : ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0) :
    ∃ c : F, ∀ x ∈ S, x ^ h = c := by
  classical
  set s : Multiset F := S.val with hs
  have hcs : Multiset.card s = h := by rw [hs]; exact hcard
  set P : F[X] := (s.map fun t => X - C t).prod with hP
  have hmonic : P.Monic := by
    rw [hP]; exact monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hdeg : P.natDegree = h := by
    rw [hP, natDegree_multiset_prod_X_sub_C_eq_card, hcs]
  have hcoeffh : P.coeff h = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  have hcoeffmid : ∀ k, 1 ≤ k → k ≤ h - 1 → P.coeff k = 0 := by
    intro k hk1 hkh
    have hkc : k ≤ Multiset.card s := by rw [hcs]; omega
    have hv := Multiset.prod_X_sub_C_coeff s (k := k) hkc
    rw [hcs] at hv
    rw [hP, hv, hesymm (h - k) (by omega) (by omega), mul_zero]
  refine ⟨- P.coeff 0, fun x hx => ?_⟩
  have hroot : P.eval x = 0 := by
    rw [hP, eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨x, by rw [hs]; exact hx, ?_⟩
    simp
  have hsum : P.eval x = ∑ k ∈ range (h + 1), P.coeff k * x ^ k := by
    rw [eval_eq_sum_range, hdeg]
  have hsub : ({0, h} : Finset ℕ) ⊆ range (h + 1) := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_range, Finset.mem_range]
    omega
  have hzero : ∀ k ∈ range (h + 1), k ∉ ({0, h} : Finset ℕ) → P.coeff k * x ^ k = 0 := by
    intro k hk hknot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hknot
    rw [Finset.mem_range] at hk
    rw [hcoeffmid k (by omega) (by omega), zero_mul]
  have hcollapse : ∑ k ∈ range (h + 1), P.coeff k * x ^ k
      = P.coeff 0 * x ^ 0 + P.coeff h * x ^ h := by
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0:ℕ) ≠ h)]
  rw [hsum, hcollapse, hcoeffh, pow_zero, mul_one, one_mul] at hroot
  exact eq_neg_of_add_eq_zero_right hroot

/-- **The vanishing-statistic `h`-subset is contained in a single `h`-th-root fiber.** Restatement
of `all_pow_eq_of_esymm_zero`: such an `S` is a subset of `{x : x^h = c}`, the root set of
`X^h - c`. With `|S| = h = deg(X^h - c)`, the containment is an equality — `S` is the whole fiber
(a coset). -/
theorem subset_pow_fiber_of_esymm_zero {S : Finset F} {h : ℕ} (hh : 0 < h) (hcard : S.card = h)
    (hesymm : ∀ j, 1 ≤ j → j ≤ h - 1 → S.val.esymm j = 0) :
    ∃ c : F, (S : Set F) ⊆ {x : F | x ^ h = c} := by
  obtain ⟨c, hc⟩ := all_pow_eq_of_esymm_zero hh hcard hesymm
  exact ⟨c, fun x hx => hc x hx⟩

/-- **Forward direction.** The root set of `X^h - c` (when it has `h` distinct roots) has its first
`h-1` elementary symmetric functions all zero — its characteristic polynomial is literally `X^h - c`,
whose middle coefficients vanish (Vieta: `coeff_eq_esymm_roots_of_card`). Together with
`all_pow_eq_of_esymm_zero` this characterizes the vanishing-statistic `h`-subsets as *exactly* the
complete `h`-th-root fibers — the cosets of `μ_h`. Over `μ_n` these are the `n/h` cosets, so the
`a = h` slice of `CosetPowerSumConcentration.exists_many_vanishing_powersum_subsets` is exact. -/
theorem esymm_roots_X_pow_sub_C_eq_zero {h : ℕ} (hh : 0 < h) (c : F)
    (hcard : Multiset.card (X ^ h - C c).roots = h) :
    ∀ j, 1 ≤ j → j ≤ h - 1 → (X ^ h - C c).roots.esymm j = 0 := by
  intro j hj1 hjh
  have hne : (h : ℕ) ≠ 0 := by omega
  have hdeg : (X ^ h - C c : F[X]).natDegree = h := natDegree_X_pow_sub_C
  have hlc : (X ^ h - C c : F[X]).leadingCoeff = 1 := (monic_X_pow_sub_C c hne).leadingCoeff
  have hcard' : Multiset.card (X ^ h - C c).roots = (X ^ h - C c).natDegree := by
    rw [hdeg]; exact hcard
  have hk : h - j ≤ (X ^ h - C c : F[X]).natDegree := by rw [hdeg]; omega
  have hv := Polynomial.coeff_eq_esymm_roots_of_card hcard' hk
  rw [hdeg, hlc, one_mul] at hv
  have hjj : h - (h - j) = j := by omega
  rw [hjj] at hv
  have hcoeff0 : (X ^ h - C c : F[X]).coeff (h - j) = 0 := by
    rw [coeff_sub, coeff_X_pow, coeff_C]
    have h1 : h - j ≠ h := by omega
    have h2 : ¬ (h - j = 0) := by omega
    simp only [h1, if_false, h2, if_false, sub_zero]
  rw [hcoeff0] at hv
  have hunit : ((-1 : F) ^ j) ≠ 0 := by apply pow_ne_zero; norm_num
  exact (mul_eq_zero.mp hv.symm).resolve_left hunit

end ArkLib.ProximityGap.Rigidity

#print axioms ArkLib.ProximityGap.Rigidity.all_pow_eq_of_esymm_zero
