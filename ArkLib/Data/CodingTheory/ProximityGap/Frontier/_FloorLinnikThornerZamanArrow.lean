/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman

/-!
# The Thorner–Zaman ⇒ small-prime arrow for the off-BGK floor closure (#444 / #464)

`_AssaultV2_FloorLocalizationN32.floor_closes_by_linnik` reduces the off-BGK floor closure to two
named inputs, one of which is `LinnikLeastPrimeBelowPrize`: the least prime `≡ 1 mod 2^a` sits below
prize scale `(2^a)^4`. Shaw's #464 dossier names **Thorner–Zaman** ([TZ24], the unconditional refined
PNT-in-AP for smooth/powerful moduli, `β > 12/5`) as the realistic unconditional route to that input.

The in-tree `KKH26ThornerZaman` already packages the named TZ hypothesis `TZPrimeSupply n β supply`
(= the window `[n^β, 2n^β]` holds `≥ supply` primes `≡ 1 mod n`) and `mem_tzWindow`. This file builds
the ELEMENTARY arrow from that supply to the small-prime existence the floor closure consumes:

> `tzSupplyOne_gives_small_prime` : `TZPrimeSupply n β 1 ⟹ ∃ p, p.Prime ∧ p ≡ 1 [MOD n] ∧ p ≤ 2·n^β`.

plus the numeric companion that `2·n^β ≤ (n)^4` whenever `2 ≤ n` and `β ≤ 3` (so the produced prime is
strictly below prize scale `n^4` at the unconditional TZ exponent `β = 3 < 4`):

> `tzSupplyOne_gives_prime_below_prize` : `TZPrimeSupply n β 1 ⟹ ∃ p, p.Prime ∧ p ≡ 1 [MOD n] ∧ p < n^4`
> (for `2 ≤ n`, `12/5 < β`, `β ≤ 3`).

## Honesty (scope)

This is the ELEMENTARY supply⇒existence⇒numeric step. The DEEP analytic content stays packaged in the
named hypothesis `TZPrimeSupply` (NEVER an axiom; it is the [TZ24] literature statement, consumed by
explicit hypothesis exactly as `_ThornerZamanPNTStatement` does). Nothing here proves `TZPrimeSupply`
itself, and nothing here is the BGK/Paley sup-norm wall. It connects the in-tree TZ packaging to the
floor closure's least-prime premise at the unconditional exponent `β = 3`. CORE stays OPEN.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow

/-- **TZ supply ⇒ small prime (existence).** If the Thorner–Zaman window `[n^β, 2n^β]` holds at least
one prime `≡ 1 mod n`, then there exists a prime `p ≡ 1 mod n` with `p ≤ 2·n^β`. Pure unpacking of
`TZPrimeSupply`/`mem_tzWindow`: a nonempty `Finset` yields a member, whose `mem_tzWindow` conjuncts
include `p ≤ 2·n^β`. -/
theorem tzSupplyOne_gives_small_prime {n : ℕ} {β : ℝ} (hTZ : TZPrimeSupply n β 1) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β := by
  have hne : (tzWindow n β).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.lt_of_lt_of_le Nat.one_pos hTZ.le_card
  obtain ⟨p, hp⟩ := hne
  rw [mem_tzWindow] at hp
  exact ⟨p, hp.1, hp.2.1, hp.2.2.2⟩

/-- **Numeric companion.** For `2 ≤ n` and `β ≤ 3`, the upper window endpoint `2·n^β` is at most
`n^4` (since `2 ≤ n` gives `2·n^β ≤ n·n^β = n^{β+1} ≤ n^4`). So any prime in the TZ window is below
prize scale `n^4` at every TZ exponent `β ≤ 3` (in particular the unconditional `β` just above
`12/5`, and `β = 3`). -/
theorem two_mul_npow_le_npow_four {n : ℕ} {β : ℝ} (hn : 2 ≤ n) (hβ : β ≤ 3) :
    2 * (n : ℝ) ^ β ≤ (n : ℝ) ^ 4 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- 2·n^β ≤ n·n^β = n^(β+1) ≤ n^4
  have hstep1 : 2 * (n : ℝ) ^ β ≤ (n : ℝ) * (n : ℝ) ^ β :=
    mul_le_mul_of_nonneg_right hn2 (Real.rpow_nonneg (le_of_lt hnpos) β)
  have hcomb : (n : ℝ) * (n : ℝ) ^ β = (n : ℝ) ^ (β + 1) := by
    rw [Real.rpow_add hnpos, Real.rpow_one]; ring
  have hexp : (β + 1) ≤ (4 : ℝ) := by linarith
  have hstep2 : (n : ℝ) ^ (β + 1) ≤ (n : ℝ) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hfour : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  calc 2 * (n : ℝ) ^ β ≤ (n : ℝ) * (n : ℝ) ^ β := hstep1
    _ = (n : ℝ) ^ (β + 1) := hcomb
    _ ≤ (n : ℝ) ^ (4 : ℝ) := hstep2
    _ = (n : ℝ) ^ 4 := hfour

/-- **TZ supply ⇒ prime below prize scale.** Combining the two: with `2 ≤ n`, `β ≤ 3`, the named TZ
hypothesis `TZPrimeSupply n β 1` produces a prime `p ≡ 1 mod n` with `p ≤ n^4` (real). This is the
unconditional-route delivery of the floor closure's least-prime premise: at the TZ exponent `β` (any
`β` in `(12/5, 3]`, all `< 4`), the least prime `≡ 1 mod n` is below prize scale. -/
theorem tzSupplyOne_gives_prime_below_prize {n : ℕ} {β : ℝ}
    (hn : 2 ≤ n) (hβ : β ≤ 3) (hTZ : TZPrimeSupply n β 1) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧ (p : ℝ) ≤ (n : ℝ) ^ 4 := by
  obtain ⟨p, hp, hmod, hle⟩ := tzSupplyOne_gives_small_prime hTZ
  exact ⟨p, hp, hmod, hle.trans (two_mul_npow_le_npow_four hn hβ)⟩

/-- **Existence of a floor-good-scale prime, in `≡ 1 mod n` AP form, from TZ.** The same conclusion
phrased with the explicit residue `p % n = 1` (for `2 ≤ n`, so `1 % n = 1`), matching the
`smallestPrime1ModN` predicate's residue test in `_AssaultV2_FloorLocalizationN32`. This is the
TZ-supplied witness that the floor closure's least-prime search is non-vacuous and below `n^4`. -/
theorem tzSupplyOne_gives_residue_prime_below_prize {n : ℕ} {β : ℝ}
    (hn : 2 ≤ n) (hβ : β ≤ 3) (hTZ : TZPrimeSupply n β 1) :
    ∃ p : ℕ, p.Prime ∧ p % n = 1 ∧ (p : ℝ) ≤ (n : ℝ) ^ 4 := by
  obtain ⟨p, hp, hmod, hle⟩ := tzSupplyOne_gives_prime_below_prize hn hβ hTZ
  refine ⟨p, hp, ?_, hle⟩
  -- p ≡ 1 [MOD n] means p % n = 1 % n; with 2 ≤ n, 1 % n = 1
  have h1 : (1 : ℕ) % n = 1 := Nat.one_mod_eq_one.mpr (by omega)
  have := hmod                    -- p ≡ 1 [MOD n] : p % n = 1 % n
  rw [Nat.ModEq, h1] at this
  exact this

end ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow

-- Axiom audits (must show only [propext, Classical.choice, Quot.sound]).
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow.tzSupplyOne_gives_small_prime
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow.two_mul_npow_le_npow_four
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow.tzSupplyOne_gives_prime_below_prize
#print axioms ArkLib.ProximityGap.Frontier.FloorLinnikTZArrow.tzSupplyOne_gives_residue_prime_below_prize
