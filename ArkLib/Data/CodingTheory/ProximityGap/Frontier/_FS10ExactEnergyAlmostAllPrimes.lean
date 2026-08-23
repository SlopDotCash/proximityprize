/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS6AlmostAllPrimesWickRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R50Depth3WraparoundVanishing

/-!
# LANE FS10 (#466, Fable session 2026-07-09): THE EXACT ENERGY AT ALMOST ALL PRIMES —
  r50's `Depth3WraparoundVanishing` (refuted as universal by r52) is PROVEN at all but
  `≤ n⁶·(k+4)n/s` primes of any family, with the exact char-0 value

At threshold `T = 1` the FS6 ledger caps the primes at which ANY nontrivial pattern
vanishes.  At every other prime the wraparound excess is ZERO, so FS5's exact decomposition
collapses to the exact characteristic-zero value:

  `addEnergy3 (μ_n) = 15n³ − 45n² + 40n`   (exactly — not merely `≤ Wick`),

i.e. round-50's atom `Depth3WraparoundVanishing G (15n³−45n²+40n)`.  History: r50 named the
atom, r52 REFUTED it as a universal statement (sparse bad primes carry genuine excess), r53
downgraded to the headroom form.  This brick completes the picture: the exact form is TRUE
at almost all primes, with an explicit machine-checked cap on the exceptions —

* `wraparoundExcess_eq_zero_of_strict_good_prime` — zero excess off the T=1 bad set;
* `depth3WraparoundVanishing_of_strict_good_prime` — the r50 atom holds there;
* `strictBadPrime_cap` — the T=1 bad set has `≤ n⁶·((k+4)·n/s)` members.

**Honest scope:** same ledger window as FS6 and worse (T=1 needs `β ≳ 8` to be non-vacuous
against `n^{β−1}` primes since the cap is `≈ n⁷/s`); the prize regime is uncapped and the
deep-`r` wall untouched.  The value is taxonomic: the r50/r52/r53 trichotomy (exact /
refuted-universal / headroom) is now fully resolved into "exact at almost all primes, with
the exceptional set explicitly budgeted".

Issue #466, lane FS10.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS10ExactEnergyAlmostAllPrimes

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

open scoped Classical

/-- **THE T=1 CAP.**  The primes at which ANY nontrivial depth-3 pattern vanishes number at
most `n⁶·((k+4)·n/s)` in any family of primes `≥ 2^s` (`n = 2^{k+1}`). -/
theorem strictBadPrime_cap {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p) :
    (P.filter (fun p => 1 ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p)).card
      ≤ (2 ^ (k + 1)) ^ 6 * (((k + 1 + 3) * 2 ^ (k + 1)) / s) := by
  have h := badPrime_cap (k := k) (T := 1) hs one_pos P hP
  simpa using h

/-- Off the T=1 bad set the wraparound excess vanishes identically. -/
theorem wraparoundExcess_eq_zero_of_strict_good_prime {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p =>
      1 ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k)) :
    wraparoundExcess ζ (2 ^ k) = 0 := by
  have hexc0 : excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p = 0 := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hle := wraparoundExcess_le_excessCount (k := k) (F := F) p hprim
  omega

/-- **THE EXACT ENERGY AT STRICT GOOD PRIMES (r50's atom, almost-all-primes form).**
Off the T=1 bad set, the depth-3 additive energy of `μ_n` takes EXACTLY its
characteristic-zero closed-form value: `Depth3WraparoundVanishing G (15n³ − 45n² + 40n)`. -/
theorem depth3WraparoundVanishing_of_strict_good_prime {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p =>
      1 ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k)) :
    Depth3WraparoundVanishing (Gset ζ (2 ^ k))
      (15 * (2 ^ (k + 1)) ^ 3 + 40 * 2 ^ (k + 1) - 45 * (2 ^ (k + 1)) ^ 2) := by
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  set n : ℕ := 2 ^ (k + 1) with hn
  have hzero : wraparoundExcess ζ (2 ^ k) = 0 :=
    wraparoundExcess_eq_zero_of_strict_good_prime hs P hP p hp hgood hprim
  have hdec := addEnergy3_eq_closedForm_add_excess (F := F) hm hprim
  rw [hzero] at hdec
  have h2 : (2 : ℕ) * 2 ^ k = n := by rw [hn]; ring
  rw [h2] at hdec
  -- transfer the ℤ identity to the ℕ statement (truncated subtraction is exact here)
  unfold Depth3WraparoundVanishing
  have hn1 : (1 : ℕ) ≤ n := Nat.one_le_two_pow
  have h45 : 45 * n ^ 2 ≤ 15 * n ^ 3 + 40 * n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · have h3 : 3 * n ^ 2 ≤ n ^ 3 := by
        calc 3 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ h
          _ = n ^ 3 := by ring
      linarith
  have hZ : (addEnergy3 (Gset ζ (2 ^ k)) : ℤ)
      = 15 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 40 * (n : ℤ) := by
    rw [hdec]; push_cast; ring
  have hZ' : (addEnergy3 (Gset ζ (2 ^ k)) : ℤ)
      = ((15 * n ^ 3 + 40 * n - 45 * n ^ 2 : ℕ) : ℤ) := by
    rw [hZ]
    push_cast [Nat.cast_sub h45]
    ring
  exact_mod_cast hZ'

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms strictBadPrime_cap
#print axioms wraparoundExcess_eq_zero_of_strict_good_prime
#print axioms depth3WraparoundVanishing_of_strict_good_prime

end ArkLib.ProximityGap.Frontier.FS10ExactEnergyAlmostAllPrimes
