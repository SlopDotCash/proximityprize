/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS6AlmostAllPrimesWickRung

/-!
# LANE FS9 (#466, Fable session 2026-07-09): `WorstCaseIncompleteSumBound` AT ALMOST ALL
  PRIMES — the FS arc terminates at the δ*-side interface object

One-line composition: FS6's good-prime `GaussianEnergyBound (μ_n) 3` feeds the in-tree
moment-method bridge `worstCaseIncompleteSumBound_of_energyBound` (the δ*-consumer interface
of `GaussPeriodMomentBound`), giving, at every prime of a family outside the FS6-capped bad
set,

  `WorstCaseIncompleteSumBound ψ μ_n ((q·15·n³)^{1/3})`,

i.e. the worst-case incomplete character sum over the smooth domain is
`≤ 15^{1/6}·q^{1/6}·√n` — as a THEOREM, no named inputs, at almost all primes.

**Honest scope:** the scale `M_3 = (15q n³)^{1/3}` is the r = 3 rung of the moment ladder;
the δ* interior consumers need the minimized `M_r` at `r ≈ ln q` (scale `2n·ln q`), and the
FS6 cap window (`β ≳ 6`) is disjoint from the regime where `M_3` beats trivial (`β < 3`) —
recorded in FS8.  This brick's value is INTERFACE: the annihilator-ledger arc now terminates
in the exact named object (`WorstCaseIncompleteSumBound`) that the δ* consumer chain reads,
so any future deepening of the ledger (r = 4, 5, …) lands directly on the δ* side with no
further plumbing.

Issue #466, lane FS9.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS9WorstCaseBoundAlmostAllPrimes

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

open scoped Classical

/-- **THE δ*-INTERFACE BOUND AT GOOD PRIMES.**  At any prime of the family outside the
FS6-capped bad set, the worst-case incomplete character sum over `μ_n` (`n = 2^{k+1}`) is
bounded at the depth-3 moment scale `M_3 = (q·15·n³)^{1/3}` — the named object the interior
δ* consumer chain reads. -/
theorem worstCaseIncompleteSumBound_of_good_prime {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p =>
      45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1
        ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    WorstCaseIncompleteSumBound ψ (Gset ζ (2 ^ k))
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 3 - 1) : ℝ)
          * ((Gset ζ (2 ^ k)).card : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹)) := by
  have hwick : GaussianEnergyBound (Gset ζ (2 ^ k)) 3 :=
    gaussianEnergyBound_three_of_good_prime hs P hP p hp hgood hprim hψ
  have h := worstCaseIncompleteSumBound_of_energyBound hψ (r := 3) (by norm_num) hwick
  simpa using h

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms worstCaseIncompleteSumBound_of_good_prime

end ArkLib.ProximityGap.Frontier.FS9WorstCaseBoundAlmostAllPrimes
