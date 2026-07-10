/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS13PairingInductionWick
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS17SimultaneousLadder
import ArkLib.Data.CodingTheory.ProximityGap.EnergyBoundImplication
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# LANE FS18 (#466, Fable session 2026-07-09): ODD-LENGTH VANISHING + THE MIN-LADDER —
  completing the zero-sum census taxonomy and the single-prime depth optimization

Two completing lemmas:

* **`zeroSumCount_odd_eq_zero`** — for odd `N`, `zeroSumCount m N = 0`: evaluating the
  folded-monomial sum at `1` gives `Σᵢ ±1 ≡ N (mod 2) ≠ 0`, so no odd-length tuple is
  zero-sum.  With FS13 (`Z(2r) ≤ (2r−1)‼(2m)^r`) the census taxonomy is complete: odd
  lengths vanish, even lengths obey Wick.
* **`eta_pow_ladder_of_good_prime`** — on FS17's single good-prime set, the per-frequency
  moment bound holds at EVERY depth `r ∈ [1, R]` simultaneously, so the minimizing depth
  can be chosen per-frequency: `‖η_b‖² ≤ min_{r ≤ R} (q·(2r−1)‼·n^r)^{1/r}` is well-formed
  at a single prime (stated as the ∀-over-depths bound; the `min` is downstream arithmetic).

**Honest scope:** unchanged from FS15/FS17 — the good windows and the prize regime remain
disjoint; the wall is untouched.

Issue #466, lane FS18.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS18OddVanishingMinLadder

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.FS12ZeroSumCountBijection
open ArkLib.ProximityGap.Frontier.FS13PairingInductionWick
open ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger
open ArkLib.ProximityGap.Frontier.FS17SimultaneousLadder
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.EnergyBoundImplication
open ArkLib.ProximityGap.DCEnergyCorrection

open scoped Classical

/-- Evaluating a folded monomial at `1` gives `±1`. -/
theorem monomF_eval_one {m x : ℕ} :
    (monomF m x).eval 1 = 1 ∨ (monomF m x).eval 1 = -1 := by
  unfold monomF
  split_ifs <;> simp

/-- **Odd lengths carry no zero-sum tuples.**  `zeroSumCount m N = 0` for odd `N`. -/
theorem zeroSumCount_odd_eq_zero (m : ℕ) {N : ℕ} (hN : Odd N) :
    zeroSumCount m N = 0 := by
  unfold zeroSumCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c _ hzero
  -- evaluate at 1: the sum of ±1 over N items has the parity of N
  have heval : ((∑ i, monomF m (c i)).eval 1 : ℤ) = 0 := by
    rw [hzero]; simp
  rw [Polynomial.eval_finset_sum] at heval
  -- each term is ±1 ≡ 1 (mod 2), so the sum has the parity of N
  have hmod : ((0 : ℤ)) % 2 = (N : ℤ) % 2 := by
    rw [← heval, Finset.sum_int_mod]
    have hone : ∀ i : Fin N, ((monomF m (c i)).eval 1) % 2 = 1 := by
      intro i
      rcases monomF_eval_one (m := m) (x := c i) with h | h <;> rw [h] <;> decide
    rw [Finset.sum_congr rfl (fun i _ => hone i)]
    simp
  obtain ⟨t, ht⟩ := hN
  omega

/-- **The complete census taxonomy.**  Every length: odd vanishes, even obeys Wick. -/
theorem zeroSumCount_taxonomy (m : ℕ) (hm : 0 < m) (N : ℕ) :
    (Odd N → zeroSumCount m N = 0) ∧
    (∀ r, N = 2 * r → zeroSumCount m N ≤ Nat.doubleFactorial (2 * r - 1) * (2 * m) ^ r) :=
  ⟨fun h => zeroSumCount_odd_eq_zero m h,
   fun r hNr => by rw [hNr]; exact zeroSumCount_le_wick m r hm⟩

/-- **The per-frequency ladder on the simultaneous good set.**  At any FS17-good prime,
every nontrivial Gauss period obeys the depth-`r` moment bound for every `r ∈ [1, R]` at
once — the min-over-depth optimization is per-prime well-formed. -/
theorem eta_pow_ladder_of_good_prime {k s R : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P) (hgood : p ∉ ladderBadSet k R P)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {v : F} (hv : v ≠ 0) :
    ∀ r ∈ Finset.Icc 1 R,
      ‖eta ψ ((range (2 * 2 ^ k)).image (ζ ^ ·)) v‖ ^ (2 * r)
        ≤ (Fintype.card F : ℝ)
            * ((Nat.doubleFactorial (2 * r - 1) : ℝ)
                * (((range (2 * 2 ^ k)).image (ζ ^ ·)).card : ℝ) ^ r) := by
  intro r hr
  have hwick := gaussianEnergyBound_ladder_of_good_prime hs P hP p hp hgood hprim hr
  have hdc := dcEnergyBound_of_gaussianEnergyBound hwick
  exact eta_pow_le_of_dcEnergyBound hψ hdc hv

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms zeroSumCount_odd_eq_zero
#print axioms zeroSumCount_taxonomy
#print axioms eta_pow_ladder_of_good_prime

end ArkLib.ProximityGap.Frontier.FS18OddVanishingMinLadder
