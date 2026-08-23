/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# `AlmostAllPrimesWick`: the per-pair divisor-count ceiling helper

This is the small `ℕ`-arithmetic helper consumed by `_BchksF4_GoodPrimeLinnik.lean` (the
good-prime existence residual for the δ* floor). It supplies the single elementary fact that
`_BchksF4` references at its per-pair bound: a positive integer has at most `Nat.log 2`-many
distinct prime factors.

The file is named `_AlmostAllPrimesWick` to match the existing import in `_BchksF4`; only the
divisor-count ceiling lemma is needed there and is provided here, axiom-clean.

## Main statement

* `card_primeFactors_le_natLog` : for `1 ≤ n`, `n.primeFactors.card ≤ Nat.log 2 n`.

## Mechanism (no `sorry`, no `axiom`)

Each `p ∈ n.primeFactors` satisfies `2 ≤ p`, so
`2 ^ (n.primeFactors.card) = ∏_{p ∈ n.primeFactors} 2 ≤ ∏_{p ∈ n.primeFactors} p ∣ n ≤ n`,
hence the card is `≤ Nat.log 2 n` by `Nat.le_log_of_pow_le`.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick

open Finset

/-- `2 ^ (#primeFactors n)` divides-bounded by `n`: the product of the distinct prime factors
(each `≥ 2`) dominates `2` raised to their count, and that product divides `n`. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  classical
  have hprod_dvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hn0 : 0 < n := hn
  have hprod_le : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn0 hprod_dvd
  have hconst : (∏ _p ∈ n.primeFactors, (2 : ℕ)) ≤ ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_le_prod'
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hconst_eq : (∏ _p ∈ n.primeFactors, (2 : ℕ)) = 2 ^ n.primeFactors.card := by
    simp [Finset.prod_const]
  calc 2 ^ n.primeFactors.card
      = ∏ _p ∈ n.primeFactors, (2 : ℕ) := hconst_eq.symm
    _ ≤ ∏ p ∈ n.primeFactors, p := hconst
    _ ≤ n := hprod_le

/-- **The per-pair divisor-count ceiling.** A positive integer has at most `Nat.log 2`-many
distinct prime factors. This is the helper `_BchksF4_GoodPrimeLinnik` references to bound the
per-pair bad-prime count by `log₂ |N|`. -/
theorem card_primeFactors_le_natLog {n : ℕ} (hn : 1 ≤ n) :
    n.primeFactors.card ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le Nat.one_lt_two (two_pow_card_primeFactors_le hn)

end ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick
