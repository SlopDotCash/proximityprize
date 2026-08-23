/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyParity
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyThreeDvd

/-!
# `6 ∣ bgkCount` away from the exceptional characteristics (#232)

The capstone combining the two structural constraints on the open additive-energy count
`M = bgkCount n = #{u ∈ μ_n : -(1+u) ∈ μ_n}`:

* `AdditiveEnergyParity.even_bgkCount_of_two_pow_ne_one` — `M` is **even** unless `(2:F)^n = 1`
  (i.e. unless `char F ∣ 2^n − 1`), via the inversion involution;
* `AdditiveEnergyThreeDvd.three_dvd_bgkCount` — `3 ∣ M` when `char F ≠ 3` and `3 ∤ n`, via the
  order-3 element of the `S₃` action.

Since `2` and `3` are coprime, for any characteristic outside the finite exceptional set
`{3} ∪ {Fermat/Mersenne-bad primes}`:

* `six_dvd_bgkCount` — `6 ∣ M`.
* `six_dvd_bgkCount_two_pow` — in particular `6 ∣ bgkCount (2^k)` for the smooth domain, whenever
  `char F ≠ 3` and `(2:F)^{2^k} ≠ 1`.

So away from finitely many exceptional characteristics the prize-deciding kernel count is a multiple
of 6 — ruling out the smallest nonzero values. This narrows the arithmetic of `M` but does not pin
its **magnitude**, which remains the open BGK/Bourgain core. Axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- **`6 ∣ bgkCount n`** for even `n` with `3 ∤ n`, in characteristic `≠ 3`, away from the
Mersenne/Fermat-bad characteristics (`(2:F)^n ≠ 1`). Combines the parity (inversion involution) and
the divisibility-by-3 (`S₃` order-3 element) constraints, which are coprime. -/
theorem six_dvd_bgkCount {n : ℕ} (hn : 0 < n) (hne : Even n) (hn3 : ¬ 3 ∣ n)
    (h3 : (3 : F) ≠ 0) (h2 : (2 : F) ^ n ≠ 1) :
    6 ∣ bgkCount (F := F) n := by
  have hdvd2 : 2 ∣ bgkCount (F := F) n := (even_bgkCount_of_two_pow_ne_one hn hne h2).two_dvd
  have hdvd3 : 3 ∣ bgkCount (F := F) n := three_dvd_bgkCount hn hn3 h3
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) hdvd2 hdvd3

/-- **`6 ∣ bgkCount (2^k)`** for the smooth domain, in characteristic `≠ 3` and away from the
Fermat-bad characteristics (`(2:F)^{2^k} ≠ 1`). -/
theorem six_dvd_bgkCount_two_pow {k : ℕ} (hk : 0 < k) (h3 : (3 : F) ≠ 0)
    (h2 : (2 : F) ^ (2 ^ k) ≠ 1) :
    6 ∣ bgkCount (F := F) (2 ^ k) := by
  refine six_dvd_bgkCount (Nat.two_pow_pos k) ?_ (fun hdvd => ?_) h3 h2
  · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  · have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.six_dvd_bgkCount
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.six_dvd_bgkCount_two_pow
