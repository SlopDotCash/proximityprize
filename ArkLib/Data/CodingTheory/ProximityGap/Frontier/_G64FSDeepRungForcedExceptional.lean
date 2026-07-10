/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS18OddVanishingMinLadder
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# G64: the FS15-FS18 deep ladder is forced exceptional

FS15-FS18 prove the raw Wick energy ladder outside a resultant-defined exceptional-prime set.
This file proves the converse obstruction needed at the explicit prize field: once the principal
frequency alone exceeds the raw Wick ceiling, the characteristic prime must lie in that exceptional
set. Consequently the simultaneous FS17 good-prime ladder is empty at every depth containing such
a rung.

The mechanism is exact. FS14 says `excessCount = 0` implies `GaussianEnergyBound`; the
DC lower bound says `GaussianEnergyBound` is false when

`q * (2r-1)‼ * n^r < n^(2r)`.

Thus a nontrivial characteristic-`p` relation pattern is not merely possible but forced. At the
nominal prize scale `n = 2^30`, `q ≤ 2^158`, depth `r = 6` already crosses this threshold. Hence the
almost-all-prime ladder cannot contain the fixed prize field even at depth six, far before the
moment saddle `r ≈ log q`.

This is a route no-go, not a DC-subtracted moment bound and not a closure of CORE.
Issue #466. Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G64FSDeepRungForcedExceptional

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger
open ArkLib.ProximityGap.Frontier.FS17SimultaneousLadder
open ArkLib.ProximityGap.DCEnergyEssential
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped Classical

/-- If the DC contribution already exceeds the raw Wick ceiling, the characteristic prime is in
FS14's depth-`r` exceptional set. Equivalently, at least one nonzero folded relation polynomial
vanishes at the order-`2^(k+1)` root in characteristic `p`. -/
theorem deep_rung_forces_bad_prime {k s r b p : ℕ} (hs : 0 < s) (hb : 2 * r ≤ 2 ^ b)
    (P : Finset ℕ) (hP : ∀ q ∈ P, Nat.Prime q ∧ 2 ^ s ≤ q) (hp : p ∈ P)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hdeep : (Fintype.card F : ℝ) *
        ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
          (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ r)
      < (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ (2 * r)) :
    p ∈ P.filter (fun q => 1 ≤ excessCount (patsG k r) (BadPatG k r) q) := by
  rw [Finset.mem_filter]
  refine ⟨hp, ?_⟩
  by_contra hnot
  have hzero : excessCount (patsG k r) (BadPatG k r) p = 0 := by omega
  have hgood : p ∉ P.filter
      (fun q => 1 ≤ excessCount (patsG k r) (BadPatG k r) q) := by
    simp [hzero]
  have hgaussian : GaussianEnergyBound ((range (2 * 2 ^ k)).image (ζ ^ ·)) r :=
    gaussianEnergyBound_of_good_prime hs hb P hP p hp hgood hprim
  exact (not_gaussianEnergyBound_of_deep hψ
    ((range (2 * 2 ^ k)).image (ζ ^ ·)) r hdeep) hgaussian

/-- The same obstruction in the predicate used by FS17's simultaneous bad set. Any ladder
containing a deep rung has a bad depth at this prime, so its min-over-depth consumer cannot use the
prime. This avoids adding any new counting estimate: the witness is the forced FS14 relation. -/
theorem deep_rung_forces_ladder_exception {k s r R p : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ q ∈ P, Nat.Prime q ∧ 2 ^ s ≤ q) (hp : p ∈ P)
    (hr : r ∈ Finset.Icc 1 R)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hdeep : (Fintype.card F : ℝ) *
        ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
          (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ r)
      < (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ (2 * r)) :
    ∃ t ∈ Finset.Icc 1 R, 1 ≤ excessCount (patsG k t) (BadPatG k t) p := by
  refine ⟨r, hr, ?_⟩
  have hbad := deep_rung_forces_bad_prime hs
    (two_mul_le_two_pow (Finset.mem_Icc.mp hr).1) P hP hp hprim hψ hdeep
  exact (Finset.mem_filter.mp hbad).2

/-- At `n = 2^30` and every field of size at most `2^158`, the FS depth-six badness count is
positive. The arithmetic margin is exact:
`2^158 * 11!! * (2^30)^6 < (2^30)^12`, by a factor greater than `2^8`. -/
theorem prize_scale_depth_six_forces_wraparound {p : ℕ} (hpprime : Nat.Prime p)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (hq : Fintype.card F ≤ 2 ^ 158)
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 ^ 30))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    1 ≤ excessCount (patsG 29 6) (BadPatG 29 6) p := by
  have horder : (2 * 2 ^ 29 : ℕ) = 2 ^ 30 := by norm_num
  have hprim' : IsPrimitiveRoot ζ (2 * 2 ^ 29) := by simpa [horder] using hprim
  have hcard : ((range (2 * 2 ^ 29)).image (ζ ^ ·)).card = 2 * 2 ^ 29 :=
    ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm.Gset_card (by positivity) hprim'
  have hqreal : (Fintype.card F : ℝ) ≤ (2 ^ 158 : ℕ) := by exact_mod_cast hq
  have hdeep : (Fintype.card F : ℝ) *
        ((Nat.doubleFactorial (2 * 6 - 1) : ℝ) *
          (((range (2 * 2 ^ 29)).image (ζ ^ ·)).card : ℝ) ^ 6)
      < (((range (2 * 2 ^ 29)).image (ζ ^ ·)).card : ℝ) ^ (2 * 6) := by
    rw [hcard]
    calc
      (Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * 6 - 1) : ℝ) * ((2 * 2 ^ 29 : ℕ) : ℝ) ^ 6)
        ≤ ((2 ^ 158 : ℕ) : ℝ) *
          ((Nat.doubleFactorial (2 * 6 - 1) : ℝ) * ((2 * 2 ^ 29 : ℕ) : ℝ) ^ 6) := by
            gcongr
      _ < ((2 * 2 ^ 29 : ℕ) : ℝ) ^ (2 * 6) := by norm_num [Nat.doubleFactorial]
  have hP : ∀ q ∈ ({p} : Finset ℕ), Nat.Prime q ∧ 2 ^ 1 ≤ q := by
    intro q hqmem
    simp only [Finset.mem_singleton] at hqmem
    subst q
    exact ⟨hpprime, hpprime.two_le⟩
  have hmem := deep_rung_forces_bad_prime (k := 29) (s := 1) (r := 6) (b := 4)
    (by norm_num) (by norm_num) ({p} : Finset ℕ) hP (by simp) hprim' hψ hdeep
  exact (Finset.mem_filter.mp hmem).2

/-- Therefore every FS17 simultaneous ladder reaching depth six has a bad rung at the nominal
prize field. In particular, its one-good-prime premise cannot discharge the explicit field
quantifier. -/
theorem prize_scale_depth_six_has_ladder_exception {p R : ℕ} (hpprime : Nat.Prime p)
    (hR : 6 ≤ R)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    (hq : Fintype.card F ≤ 2 ^ 158)
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 ^ 30))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∃ t ∈ Finset.Icc 1 R, 1 ≤ excessCount (patsG 29 t) (BadPatG 29 t) p := by
  exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, hR⟩,
    prize_scale_depth_six_forces_wraparound hpprime hq hprim hψ⟩

/-- Honest scope marker: G64 is a forced-exception theorem for the raw FS ladder, not a proof of the
DC-subtracted Paley/BGK bound. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms deep_rung_forces_bad_prime
#print axioms deep_rung_forces_ladder_exception
#print axioms prize_scale_depth_six_forces_wraparound
#print axioms prize_scale_depth_six_has_ladder_exception
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G64FSDeepRungForcedExceptional
