/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# B3 — DISCHARGING THE [TZ24] SUPPLY FROM EXPLICIT PRIMES (#334)

The single open input of the B3 (s=128) lane is the named hypothesis `TZPrimeSupply n β supply`
(`KKH26ThornerZaman.lean`) — "the window `[n^β, 2·n^β]` contains `≥ supply` primes `≡ 1 (mod n)`".
The asymptotic instantiation needs the analytic Thorner–Zaman PNT-in-APs input (not yet in mathlib).
This file supplies the **concrete** route (option (ii) of the B3 plan):

* **`tzPrimeSupply_of_subset`** — a reusable *constructor*: an explicit finset of verified window
  primes `⟹ TZPrimeSupply`.  Discharges the named hypothesis for any concrete parameters whose
  primes can be listed, with no analytic machinery.
* **`tzPrimeSupply_two_three`** — a concrete non-vacuous instance (`[8,16] ∋ 11, 13 ≡ 1 mod 2`).
* **`kkh26_good_prime_concrete`** — an **end-to-end machinery check**: feeding the concrete supply
  through the [KKH26] Lemma-2 consumer `kkh26_good_prime_of_TZ` (empty resultant family, budget
  `0 < 2`) yields an *actual* good prime, confirming the whole B3 chain is non-vacuous and wired.

Axiom-clean.  Issue #334 (B3).
-/

open Finset
namespace ArkLib.ProximityGap.KKH26

/-- **Constructor for the [TZ24] supply hypothesis from explicit verified primes.**  If `S` is a
finset of primes `≡ 1 (mod n)`, each lying in `[n^β, 2·n^β]`, and `supply ≤ |S|`, then
`TZPrimeSupply n β supply`.  This discharges the named hypothesis for any *concrete* parameters
where the window primes can be exhibited (option (ii) of the B3 plan) — without the analytic
prime-counting input.  Reusable for every concrete s=128 row whose primes are listed. -/
theorem tzPrimeSupply_of_subset {n : ℕ} {β : ℝ} {supply : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≡ 1 [MOD n] ∧ (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β)
    (hcard : supply ≤ S.card) : TZPrimeSupply n β supply where
  le_card := hcard.trans (Finset.card_le_card fun p hp => mem_tzWindow.mpr (hS p hp))

/-- **A concrete, non-vacuous instance.**  The Thorner–Zaman window `[2³, 2·2³] = [8, 16]` contains
the two primes `11, 13 ≡ 1 (mod 2)`, so `TZPrimeSupply 2 3 2` holds.  Demonstrates that the named
hypothesis (and hence the whole B3 chain) is genuinely instantiable. -/
theorem tzPrimeSupply_two_three : TZPrimeSupply 2 ((3 : ℕ) : ℝ) 2 := by
  refine tzPrimeSupply_of_subset (S := {11, 13}) (fun p hp => ?_) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨by decide, by decide, by rw [Real.rpow_natCast]; norm_num,
      by rw [Real.rpow_natCast]; norm_num⟩
  · exact ⟨by decide, by decide, by rw [Real.rpow_natCast]; norm_num,
      by rw [Real.rpow_natCast]; norm_num⟩

/-- **End-to-end machinery check of the B3 chain.**  Feeding the concrete supply
`tzPrimeSupply_two_three` through the [KKH26] Lemma-2 consumer `kkh26_good_prime_of_TZ` (with the
empty resultant family, so the bad-prime budget is `0 < 2`) produces an actual good prime:
some prime `p ≡ 1 (mod 2)` in `[8, 16]`.  Confirms the consumer chain is non-vacuous and correctly
wired — not merely conditionally stated. -/
theorem kkh26_good_prime_concrete :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD 2] ∧
      ((2 : ℕ) : ℝ) ^ ((3 : ℕ) : ℝ) ≤ p ∧ (p : ℝ) ≤ 2 * ((2 : ℕ) : ℝ) ^ ((3 : ℕ) : ℝ) := by
  obtain ⟨p, hp, hmod, hlb, hub, _⟩ :=
    kkh26_good_prime_of_TZ (m := 0) (M := 1) (R := fun i => i.elim0) tzPrimeSupply_two_three
      (fun i => i.elim0) (fun i => i.elim0)
      (by rw [Real.rpow_natCast]; norm_num)
      (by rw [Nat.cast_zero, zero_mul]; norm_num)
  exact ⟨p, hp, hmod, hlb, hub⟩

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_of_subset
-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.tzPrimeSupply_two_three
-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_concrete
