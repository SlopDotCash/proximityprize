/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyKernel

/-!
# The BGK kernel as polynomial coprimality / the Mersenne obstruction (#232)

Sharpens `AdditiveEnergyKernel`: the open additive-energy count `M = bgkCount n` is the number of
COMMON ROOTS of the two explicit polynomials `X^n - 1` and `(X+1)^n - 1` (for even `n`, since
`(-(1+u))^n = (1+u)^n`).  Hence:

* `bgkCount_eq_zero_of_coprime` — if `X^n - 1` and `(X+1)^n - 1` are **coprime** in `F[X]`
  (equivalently their resultant is nonzero in `F`), then `M = 0`: the additive energy vanishes and
  the prize survives at this cell.  This reduces the open Bourgain kernel to a concrete
  polynomial-coprimality / resultant question over the deployed field.
* `one_mem_bgk_iff` — `u = 1` is a solution iff `(2:F)^n = 1`, i.e. `char F ∣ 2^n - 1`: the explicit
  "bad characteristic" (Mersenne-factor) obstruction to `M = 0`.  Since the resultant carries the
  factor `2^n - 1` (the `ζ=1` term), the additive energy is forced `≥ 1` exactly in those
  characteristics — pinpointing precisely which fields can break the cell.

So the open prize core at this cell is exactly: *for the deployed smooth fields `F_q` (`2^k ∣ q-1`),
is `char F_q` a prime dividing the resultant `Res(X^{2^k}-1, (X+1)^{2^k}-1)`?* — a concrete, explicit
arithmetic question that is the analytic-number-theory heart of the prize. Axiom-clean.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- A `μ_n` element `u` lies in the BGK set iff it is a common root of `X^n - 1` and `(X+1)^n - 1`
(for even `n`, since `(-(1+u))^n = (1+u)^n`). -/
theorem mem_bgk_iff_common_root {n : ℕ} (hn : 0 < n) (hne : Even n) {u : F} :
    (u ∈ nthRootsFinset n (1 : F) ∧ -(1 + u) ∈ nthRootsFinset n (1 : F))
      ↔ ((X ^ n - 1 : F[X]).IsRoot u ∧ ((X + 1) ^ n - 1 : F[X]).IsRoot u) := by
  rw [mem_nthRootsFinset hn, mem_nthRootsFinset hn]
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one, eval_add]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1, sub_self], ?_⟩
    have : (-(1 + u)) ^ n = (1 + u) ^ n := by rw [neg_pow, hne.neg_one_pow, one_mul]
    rw [add_comm u 1, ← this, h2, sub_self]
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination h1, ?_⟩
    have : (-(1 + u)) ^ n = (1 + u) ^ n := by rw [neg_pow, hne.neg_one_pow, one_mul]
    rw [this, add_comm 1 u]; linear_combination h2

/-- **The open kernel vanishes when the two explicit polynomials are coprime.** If
`X^n - 1` and `(X+1)^n - 1` are coprime in `F[X]` (equivalently their resultant is nonzero in `F`),
then `M = bgkCount n = 0`: the additive energy of `μ_n` vanishes and the prize survives at this cell.
This reduces the open Bourgain kernel to a concrete polynomial-coprimality / resultant question over
the deployed field. -/
theorem bgkCount_eq_zero_of_coprime {n : ℕ} (hn : 0 < n) (hne : Even n)
    (hcop : IsCoprime (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1)) :
    bgkCount (F := F) n = 0 := by
  rw [bgkCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu hcon
  obtain ⟨hr1, hr2⟩ := (mem_bgk_iff_common_root hn hne).mp ⟨hu, hcon⟩
  rw [IsRoot.def] at hr1 hr2
  obtain ⟨a, b, hab⟩ := hcop
  have hev := congrArg (eval u) hab
  rw [eval_add, eval_mul, eval_mul, eval_one, hr1, hr2, mul_zero, mul_zero, add_zero] at hev
  exact zero_ne_one hev

/-- **`u = 1` is in the BGK set iff the characteristic divides the Mersenne number `2^n - 1`.**
So the additive energy is automatically `≥ 1` exactly when `2^n = 1` in `F` (`char F ∣ 2^n - 1`) —
the explicit "bad characteristic" obstruction to `M = 0`. -/
theorem one_mem_bgk_iff {n : ℕ} (hn : 0 < n) (hne : Even n) :
    (1 ∈ nthRootsFinset n (1 : F) ∧ -(1 + 1) ∈ nthRootsFinset n (1 : F))
      ↔ (2 : F) ^ n = 1 := by
  rw [mem_bgk_iff_common_root hn hne]
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one, eval_add, one_pow]
  constructor
  · rintro ⟨_, h2⟩
    have : ((1 : F) + 1) ^ n = 1 := by linear_combination h2
    rw [← this]; norm_num
  · intro h
    refine ⟨by norm_num, ?_⟩
    have : ((1 : F) + 1) ^ n = 1 := by rw [show (1 : F) + 1 = 2 by norm_num, h]
    rw [this, sub_self]

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_eq_zero_of_coprime
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.one_mem_bgk_iff
