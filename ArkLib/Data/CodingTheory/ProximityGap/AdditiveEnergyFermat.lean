/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultant

/-!
# The `u = 1` BGK obstruction as Fermat-number divisibility (#232)

Sharpens `AdditiveEnergyResultant.one_mem_bgk_iff`. There the `u = 1` additive-energy solution of
the BGK kernel for the smooth domain `μ_n` (`n = 2^k`) was reduced to the single field condition
`(2 : F)^n = 1`, i.e. `char F ∣ 2^n − 1` (the "Mersenne obstruction"). Here we make that bad-prime
condition **explicit** using the classical Fermat-number factorisation
`2^(2^k) − 1 = ∏_{j<k} F_j` (`F_j = 2^(2^j)+1 = 3, 5, 17, 257, 65537, …`, Mathlib's
`Nat.prod_fermatNumber`):

* `two_pow_two_pow_sub_one_eq_prod_fermat` — `2^(2^k) − 1 = ∏_{j<k} Nat.fermatNumber j`.
* `one_mem_bgk_iff_exists_fermat_dvd` — over a field of **prime** characteristic `p`, the `u = 1`
  obstruction holds **iff** `p` divides one of the first `k` Fermat numbers `F_0, …, F_{k−1}`. So
  the `u = 1` prize-breaking characteristics are *exactly* the prime factors of those Fermat
  numbers.
* `fermat_dvd_unique` — each prime divides **at most one** Fermat number (they are pairwise
  coprime), so the witnessing Fermat index is unique.

**Interpretation.** This pins one explicit infinite family of bad characteristics for the open
prize kernel and, simultaneously, *re-explains why the full bad-prime set is hard to determine*:
even this `u = 1` sub-family is governed by the factorisations of Fermat numbers, which are famously
open beyond `F_4` (`F_5, …, F_{32}` are known composite but most are not fully factored, and it is
unknown whether any Fermat number beyond `F_4` is prime). A deployed smooth field `F_q`
(`2^k ∣ q − 1`) survives the `u = 1` cell precisely when its characteristic divides none of
`F_0, …, F_{k−1}`. Axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- Bridge: in a field of prime characteristic `p`, `(2:F)^m = 1 ↔ p ∣ 2^m − 1`. -/
theorem two_pow_eq_one_iff_dvd {p : ℕ} [CharP F p] (m : ℕ) :
    (2 : F) ^ m = 1 ↔ p ∣ 2 ^ m - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hcast : ((2 ^ m - 1 : ℕ) : F) = (2 : F) ^ m - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [← CharP.cast_eq_zero_iff F p (2 ^ m - 1), hcast, sub_eq_zero]

/-- **Fermat-number factorisation of the `u = 1` obstruction.** For `n = 2^k`, the Mersenne number
`2^(2^k) − 1` is exactly the product of the first `k` Fermat numbers
`∏_{j<k} F_j` (`F_j = 2^(2^j)+1 = 3, 5, 17, 257, …`). -/
theorem two_pow_two_pow_sub_one_eq_prod_fermat (k : ℕ) :
    2 ^ (2 ^ k) - 1 = ∏ j ∈ range k, Nat.fermatNumber j := by
  rw [Nat.prod_fermatNumber]
  unfold Nat.fermatNumber
  omega

/-- **The `u = 1` prize-breaking characteristics for `n = 2^k` are exactly the prime factors of the
Fermat numbers `F_0, …, F_{k−1}`.** Over a field `F` of prime characteristic `p`, the `u = 1`
additive-energy solution of the BGK kernel exists (so `M ≥ 1` and the prize cell breaks at `u = 1`)
**iff** `p` divides one of the first `k` Fermat numbers. Since each prime divides at most one Fermat
number (`fermat_dvd_unique`), this *enumerates* the bad characteristics. It also explains why even
this `u = 1` sub-family is hard to pin in general: it requires the factorisations of Fermat numbers,
which are famously open beyond `F_4`. -/
theorem one_mem_bgk_iff_exists_fermat_dvd {p : ℕ} [CharP F p] (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    ((1 : F) ∈ nthRootsFinset (2 ^ k) (1 : F) ∧
        -(1 + 1) ∈ nthRootsFinset (2 ^ k) (1 : F))
      ↔ ∃ j ∈ range k, p ∣ Nat.fermatNumber j := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have heven : Even (2 ^ k) := by
    rw [Nat.even_pow]; exact ⟨even_two, by omega⟩
  rw [one_mem_bgk_iff hpos heven, two_pow_eq_one_iff_dvd,
    two_pow_two_pow_sub_one_eq_prod_fermat,
    hp.prime.dvd_finset_prod_iff (fun j => Nat.fermatNumber j)]

/-- **Disjointness of the bad-characteristic families.** A prime `p` divides at most one Fermat
number, so the `u = 1` obstruction is witnessed by a *unique* Fermat index. -/
theorem fermat_dvd_unique {p : ℕ} (hp : p.Prime) {i j : ℕ}
    (hi : p ∣ Nat.fermatNumber i) (hj : p ∣ Nat.fermatNumber j) : i = j := by
  by_contra hne
  have hcop := Nat.coprime_fermatNumber_fermatNumber hne
  have hgcd : p ∣ Nat.gcd (Nat.fermatNumber i) (Nat.fermatNumber j) := Nat.dvd_gcd hi hj
  rw [Nat.Coprime] at hcop
  rw [hcop] at hgcd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hgcd)

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.one_mem_bgk_iff_exists_fermat_dvd
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.fermat_dvd_unique
