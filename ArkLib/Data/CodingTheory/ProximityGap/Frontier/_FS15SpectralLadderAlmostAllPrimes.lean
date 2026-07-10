/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS14DepthGenericLedger
import ArkLib.Data.CodingTheory.ProximityGap.EnergyBoundImplication
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# LANE FS15 (#466, Fable session 2026-07-09): THE SPECTRAL LADDER AT ALMOST ALL PRIMES —
  per-frequency moment bounds and the δ*-interface object at EVERY depth at good primes

The depth-generic spectral chain (`dcEnergyBound_of_gaussianEnergyBound`,
`eta_pow_le_of_dcEnergyBound`, `worstCaseIncompleteSumBound_of_energyBound` — all already
generic in `r`) composed with FS14's good-prime Wick rung:

* **`eta_pow_le_of_good_prime`** — at every prime of the family outside the FS14 T=1 bad
  set, every nontrivial Gauss period obeys the sharp depth-`r` per-frequency bound
  `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` — the whole moment LADDER, not one rung.
* **`worstCaseIncompleteSumBound_of_good_prime`** — hence the δ*-interface object
  `WorstCaseIncompleteSumBound ψ μ_n M_r`, `M_r = (q·(2r−1)‼·n^r)^{1/r}`, at every depth at
  good primes.

**THE CLOSING NO-GO OF THE ARC (regime disjointness at every depth — record so nobody hopes
otherwise).**  Goodness at depth `r` costs a bad-set budget `≈ n^{2r+1}/s`, non-vacuous only
against prime families at `β ≳ 2r+2`; but there `M_r^{1/2} ≈ (q^{1/2r}·√(r n)) ≥
n^{β/(2r)+1/2} ≥ n^{(2r+2)/(2r)·…}` stays above the trivial `M ≤ n` for every admissible
pairing — a FIXED-depth ledger can never beat the trivial sup-norm bound; only per-prime
uniformity (empty exceptional sets) or depth-uniformity to `r ≈ ln q` breaks it.  That is
the Paley/BGK wall — the δ* core, untouched.

Issue #466, lane FS15.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS15SpectralLadderAlmostAllPrimes

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.EnergyBoundImplication
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

open scoped Classical

variable {k s r b : ℕ}

/-- **THE PER-FREQUENCY LADDER AT GOOD PRIMES.**  At any prime of the family outside the
FS14 T=1 bad set, every nontrivial Gauss period of `μ_n` (`n = 2·2^k`) obeys the sharp
depth-`r` moment bound. -/
theorem eta_pow_le_of_good_prime (hs : 0 < s) (hb : 2 * r ≤ 2 ^ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {v : F} (hv : v ≠ 0) :
    ‖eta ψ ((range (2 * 2 ^ k)).image (ζ ^ ·)) v‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
          * ((Nat.doubleFactorial (2 * r - 1) : ℝ)
              * (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ r) := by
  have hwick : GaussianEnergyBound ((range (2 * 2 ^ k)).image (ζ ^ ·)) r :=
    gaussianEnergyBound_of_good_prime hs hb P hP p hp hgood hprim
  have hdc : DCEnergyBound ((range (2 * 2 ^ k)).image (ζ ^ ·)) r :=
    dcEnergyBound_of_gaussianEnergyBound hwick
  exact eta_pow_le_of_dcEnergyBound hψ hdc hv

/-- **THE δ*-INTERFACE LADDER AT GOOD PRIMES.**  Same hypotheses; the named
`WorstCaseIncompleteSumBound` fires at scale `M_r = (q·(2r−1)‼·n^r)^{1/r}`. -/
theorem worstCaseIncompleteSumBound_of_good_prime (hs : 0 < s) (hr : 1 ≤ r)
    (hb : 2 * r ≤ 2 ^ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    WorstCaseIncompleteSumBound ψ ((range (2 * 2 ^ k)).image (ζ ^ ·))
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
          * (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ r) ^ ((r : ℝ)⁻¹)) :=
  worstCaseIncompleteSumBound_of_energyBound hψ hr
    (gaussianEnergyBound_of_good_prime hs hb P hP p hp hgood hprim)

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms eta_pow_le_of_good_prime
#print axioms worstCaseIncompleteSumBound_of_good_prime

end ArkLib.ProximityGap.Frontier.FS15SpectralLadderAlmostAllPrimes
