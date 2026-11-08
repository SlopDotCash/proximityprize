/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyKernel

/-!
# The BGK kernel as polynomial coprimality / the Mersenne obstruction (#232)

Sharpens `AdditiveEnergyKernel`: the shifted-root intersection count
`M = bgkCount n = |μ_n ∩ -(1 + μ_n)|` is the number of COMMON ROOTS in `F` of the two explicit
polynomials `X^n - 1` and `(X+1)^n - 1` (for even `n`, since `(-(1+u))^n = (1+u)^n`).

**`bgkCount` is not the additive energy (audit PG-064).**  `bgkCount n` is one particular
shifted-root intersection statistic (it governs the zero-sum triple count `tripleZero`), not the
additive energy `E(μ_n) = #{a + b = c + d}` of `μ_n`.  Its vanishing does not make the additive
energy vanish: every nonempty set has positive (diagonal) additive energy, e.g. over `ℂ`,
`μ₂ = {−1, 1}` has empty shifted intersection (`bgkCount 2 = 0`) but additive energy `6`.

* `bgkCount_eq_zero_of_coprime` — if `X^n - 1` and `(X+1)^n - 1` are **coprime** in `F[X]`
  (equivalently their resultant is nonzero in `F`), then the shifted intersection is empty,
  `M = 0`.  This reduces the vanishing of this statistic to a concrete polynomial-coprimality /
  resultant question over the deployed field.
* `one_mem_bgk_iff` — the single candidate point `u = 1` lies in the intersection iff
  `(2:F)^n = 1`, i.e. `char F ∣ 2^n - 1`.  So a Mersenne-factor characteristic is **one sufficient
  obstruction** to `M = 0`.  It is NOT an exact classification of the characteristics with a
  nonempty intersection: other points `u ≠ 1` can be common roots.  Checked example
  (`bgkCount_zmod97_32_pos`, `two_pow_32_ne_one_zmod97`): in `𝔽₉₇` with `n = 32`, `u = 18` and
  `-(1+u) = 78` are both 32nd roots of unity, so `bgkCount 32 > 0`, although `2^32 ≡ 35 ≢ 1`
  (mod 97), i.e. `97 ∤ 2^32 − 1`.

So, for the deployed smooth fields `F_q` (`2^k ∣ q-1`), `char F_q` dividing the integer resultant
`Res(X^{2^k}-1, (X+1)^{2^k}-1)` is a NECESSARY condition for `bgkCount (2^k) > 0` (a common root
in `F_q` makes the reductions non-coprime); the Mersenne factor `2^{2^k} - 1` of that resultant
accounts only for the `u = 1` root. Axiom-clean.
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

/-- **The shifted intersection is empty when the two explicit polynomials are coprime.** If
`X^n - 1` and `(X+1)^n - 1` are coprime in `F[X]` (equivalently their resultant is nonzero in `F`),
then `M = bgkCount n = |μ_n ∩ -(1 + μ_n)| = 0`.  This is the vanishing of the shifted-root
intersection statistic only, NOT of the additive energy of `μ_n` (which is positive whenever `μ_n`
is nonempty). -/
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
This identifies only the single candidate point `u = 1`: when `2^n = 1` in `F`
(`char F ∣ 2^n - 1`) the shifted intersection is nonempty, so `M = bgkCount n ≥ 1`.  It is one
sufficient obstruction to `M = 0`, not a classification: `bgkCount_zmod97_32_pos` exhibits
`M > 0` in `𝔽₉₇` at `n = 32` although `2^32 ≠ 1` there. -/
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

section Mersenne97

/-! ### The Mersenne condition is not necessary (audit PG-064)

In `𝔽₉₇` with `n = 32`, the point `u = 18` and `-(1+u) = 78` are both 32nd roots of unity, so the
shifted intersection is nonempty, while `2^32 ≡ 35 ≠ 1`, i.e. `97 ∤ 2^32 − 1`. -/

local instance fact_prime_97_bgkMersenne : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- `2^32 ≠ 1` in `𝔽₉₇`: `97` does not divide the Mersenne number `2^32 − 1`. -/
theorem two_pow_32_ne_one_zmod97 : (2 : ZMod 97) ^ 32 ≠ 1 := by decide

/-- `u = 18` lies in the shifted intersection `μ₃₂ ∩ -(1 + μ₃₂)` of `𝔽₉₇`. -/
theorem eighteen_mem_bgk_zmod97 :
    (18 : ZMod 97) ∈ nthRootsFinset 32 (1 : ZMod 97) ∧
      -(1 + (18 : ZMod 97)) ∈ nthRootsFinset 32 (1 : ZMod 97) := by
  rw [mem_nthRootsFinset (by norm_num), mem_nthRootsFinset (by norm_num)]
  exact ⟨by decide, by decide⟩

/-- **A nonempty shifted intersection outside the Mersenne characteristics.**
`bgkCount 32 > 0` over `𝔽₉₇`, although `2^32 ≠ 1` in `𝔽₉₇` (`two_pow_32_ne_one_zmod97`). -/
theorem bgkCount_zmod97_32_pos : 0 < bgkCount (F := ZMod 97) 32 := by
  rw [bgkCount, Finset.card_pos]
  exact ⟨18, Finset.mem_filter.mpr eighteen_mem_bgk_zmod97⟩

end Mersenne97

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_eq_zero_of_coprime
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.one_mem_bgk_iff
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_zmod97_32_pos
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.two_pow_32_ne_one_zmod97
