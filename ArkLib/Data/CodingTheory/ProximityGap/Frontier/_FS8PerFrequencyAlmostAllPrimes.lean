/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS6AlmostAllPrimesWickRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R54Depth3PerFrequencyChain

/-!
# LANE FS8 (#466, Fable session 2026-07-09): THE PER-FREQUENCY GAUSS-PERIOD BOUND AT
  ALMOST ALL PRIMES — `‖η_b‖⁶ ≤ 15·q·n³` for every `b ≠ 0`, unconditionally at every
  good prime of the FS6 ledger

One-lemma composition: FS5's unconditional `Depth3ExcessBounded` + FS6's good-prime headroom
+ the r54 chain (`GaussianEnergyBound → DCEnergyBound → eta_pow_le_of_dcEnergyBound`) give,
at every prime of a family outside the FS6-capped bad set, the sharp per-frequency Wick bound

  `‖η_b‖⁶ ≤ q · 15 · n³`   for every nontrivial frequency `b ≠ 0`,

i.e. `‖η_b‖ ≤ (15)^{1/6} · q^{1/6} · n^{1/2}` — the depth-3 instance of the object the prize
moment method consumes, now a THEOREM at almost all primes (no named inputs).

**Honest scope:** the r=3 depth alone certifies `M ≲ q^{1/6}√n`, nontrivial versus the trivial
`M ≤ n` only for `β < 3` — while the FS6 cap is non-vacuous only for `β ≳ 6`.  The two windows
are DISJOINT: this composition is a structural completion of the r54 chain, not a new sup-norm
regime (recorded so nobody re-derives it hoping otherwise).  Reaching the prize needs the same
bound at depth `r ≈ ln q` — the wall, untouched.

Issue #466, lane FS8.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS8PerFrequencyAlmostAllPrimes

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom
open ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped Classical

/-- **THE PER-FREQUENCY BOUND AT GOOD PRIMES.**  At any prime of the family outside the
FS6-capped bad set, every nontrivial Gauss period of `μ_n` (`n = 2^{k+1}`) obeys the sharp
depth-3 Wick bound `‖η_b‖⁶ ≤ q·15·n³` — end-to-end, no named hypotheses. -/
theorem eta_sixth_le_of_good_prime {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p =>
      45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1
        ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ (Gset ζ (2 ^ k)) b‖ ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * ((Gset ζ (2 ^ k)).card : ℝ) ^ 3) := by
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  set n : ℕ := 2 ^ (k + 1) with hn
  have h2 : (2 : ℕ) * 2 ^ k = n := by rw [hn]; ring
  have hexc_le : excessCount (tupleSet n) (BadPat k) p ≤ 45 * n ^ 2 - 40 * n := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hwrap_le : wraparoundExcess ζ (2 ^ k) ≤ 45 * n ^ 2 - 40 * n :=
    le_trans (by simpa [hn] using wraparoundExcess_le_excessCount (k := k) p hprim) hexc_le
  have hcard : (Gset ζ (2 ^ k)).card = n := by
    rw [Gset_card hm hprim, h2]
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have h40 : 40 * n ≤ 45 * n ^ 2 := by nlinarith
  have hhead : (wraparoundExcess ζ (2 ^ k) : ℝ)
      ≤ 45 * ((Gset ζ (2 ^ k)).card : ℝ) ^ 2 - 40 * ((Gset ζ (2 ^ k)).card : ℝ) := by
    rw [hcard]
    calc (wraparoundExcess ζ (2 ^ k) : ℝ)
        ≤ ((45 * n ^ 2 - 40 * n : ℕ) : ℝ) := by exact_mod_cast hwrap_le
      _ = 45 * (n : ℝ) ^ 2 - 40 * (n : ℝ) := by
          push_cast [Nat.cast_sub h40]
          ring
  exact eta_sixth_le_of_excess_headroom hψ
    (ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm.Gset (F := F) ζ (2 ^ k))
    (depth3ExcessBounded_wraparound hm hprim) hhead hb

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms eta_sixth_le_of_good_prime

end ArkLib.ProximityGap.Frontier.FS8PerFrequencyAlmostAllPrimes
