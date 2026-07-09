/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS1Depth3AnnihilatorLedger
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm

/-!
# LANE FS6 (#466, Fable session 2026-07-09): THE ALMOST-ALL-PRIMES r=3 WICK RUNG —
  the composed FS1→FS5 theorem, no named mathematical inputs

The full composition of the Fable-session arc:

* **`badPrime_cap`** — for any finite family `P` of primes `≥ 2^s` and `n = 2^{k+1}`, the
  number of primes at which the depth-3 pattern badness count reaches `T` is at most
  `n⁶ · (L/s) / T` with `L = (k+4)·2^{k+1}` (FS1 double-count/Markov + FS2 resultant
  annihilator + FS3 Sylvester height + FS4 pattern shape).
* **`gaussianEnergyBound_three_of_good_prime`** — at any prime of the family OUTSIDE that
  capped bad set (threshold `T = 45n² − 40n + 1`), in ANY field of that characteristic
  containing a primitive `n`-th root `ζ`, the EXACT Wick bound `GaussianEnergyBound (μ_n) 3`
  holds (FS5 unconditional decomposition + closed form + r53 weld).

Together: **the depth-3 Wick rung holds at all but `≤ n⁶(L/s)/(45n²−40n+1) ≈ n⁴(k+4)/(45·s)`
primes of any family of primes `≥ 2^s` splitting `μ_n`** — machine-checked end to end, no
`sorry`, no named hypotheses.

**HONEST SCOPE (unchanged from FS1):** this is an almost-all-primes statement.  Against the
`≈ x/(n·log x)` primes `≡ 1 (mod n)` below `x = n^β` it is non-vacuous only for `β ≳ 6`; at
the prize shape (`q ≈ n·2^128`, `β ≈ 5.3`) the cap exceeds the family size, and the deep-`r`
(`r ≈ ln q`) tower is untouched.  The per-prime prize rung remains the open core.  This arc's
value: the r=3 rung's obstruction is now EXACTLY localized in a finite, explicit,
per-prime pattern count with a proven global (prime-averaged) budget.

Issue #466, lane FS6.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound
open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

open scoped Classical

/-- The badness relation: pattern `t` (a sextuple over `[0, 2^{k+1})`) goes bad at `p` when its
pattern polynomial is nonzero yet vanishes at an order-`2^{k+1}` root in some field of
characteristic `p`. -/
def BadPat (k : ℕ) (p : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  pp (2 ^ k) t ≠ 0 ∧
    ∃ (F : Type) (_ : Field F) (_ : CharP F p) (ζ : F),
      ζ ^ (2 ^ k) = -1 ∧ aeval ζ (pp (2 ^ k) t) = 0

/-- **THE BAD-PRIME CAP** (`n = 2^{k+1}`, `L = (k+4)·2^{k+1}`): the number of primes of the
family at which the pattern badness count reaches `T` is at most `n⁶·(L/s)/T`. -/
theorem badPrime_cap {k s T : ℕ} (hs : 0 < s) (hT : 0 < T)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p) :
    (P.filter (fun p => T ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p)).card
      ≤ (2 ^ (k + 1)) ^ 6 * (((k + 1 + 3) * 2 ^ (k + 1)) / s) / T := by
  have hcap := annihilator_ledger_badPrime_cap (P := P)
    (pats := tupleSet (2 ^ (k + 1))) (Bad := BadPat k)
    (s := s) (L := (k + 1 + 3) * 2 ^ (k + 1)) (H := 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)))
    (T := T) hs hT le_rfl hP ?_
  · rwa [tupleSet_card] at hcap
  · -- per-pattern annihilators
    intro t htup
    by_cases hzero : pp (2 ^ k) t = 0
    · -- trivial pattern: never bad; N = 1 works
      refine ⟨1, one_ne_zero, Nat.one_le_two_pow, ?_⟩
      intro p _ hbad
      exact absurd hzero hbad.1
    · -- nontrivial pattern: the FS2/FS3 resultant annihilator with dyadic height
      have hbounds := htup
      simp only [tupleSet, Finset.mem_product, mem_range] at hbounds
      have hdeg : (pp (2 ^ k) t).natDegree < 2 ^ k := by
        have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        exact patternPoly_natDegree_lt (by positivity)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcoeff : ∀ i, |(pp (2 ^ k) t).coeff i| ≤ 2 ^ 3 := fun i =>
        patternPoly_coeff_abs_le (2 ^ k) _ _ _ _ _ _ i
      obtain ⟨N, hN0, hNH, hdvd⟩ :=
        pattern_annihilator_exists_with_height (k := k) (b := 3) hzero hdeg hcoeff
      refine ⟨N, hN0, hNH, ?_⟩
      rintro p _ ⟨-, F, hF, hCh, ζ, hζ, hroot⟩
      exact hdvd F hF p hCh ζ hζ hroot

set_option maxHeartbeats 1000000 in
/-- Any concrete wraparound excess is dominated by the abstract badness count. -/
theorem wraparoundExcess_le_excessCount {k : ℕ} {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (p : ℕ) [CharP F p] {ζ : F}
    (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k)) :
    wraparoundExcess ζ (2 ^ k) ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p := by
  unfold wraparoundExcess excessCount
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  have h2 : (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) := by ring
  refine Finset.card_le_card ?_
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  obtain ⟨htup, hne, hroot⟩ := ht
  rw [h2] at htup
  exact ⟨htup, hne, F, inferInstance, inferInstance, ζ, zeta_pow_m hm hprim, hroot⟩

/-- **THE GOOD-PRIME WICK WELD.**  At any prime of the family outside the capped bad set
(threshold `45n² − 40n + 1`, `n = 2^{k+1}`), the EXACT depth-3 Wick bound holds for `μ_n` in
every field of that characteristic. -/
theorem gaussianEnergyBound_three_of_good_prime {k s : ℕ} (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p =>
      45 * (2 ^ (k + 1)) ^ 2 - 40 * 2 ^ (k + 1) + 1
        ≤ excessCount (tupleSet (2 ^ (k + 1))) (BadPat k) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    GaussianEnergyBound (Gset ζ (2 ^ k)) 3 := by
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  set n : ℕ := 2 ^ (k + 1) with hn
  have h2 : (2 : ℕ) * 2 ^ k = n := by rw [hn]; ring
  -- the excess is under the headroom
  have hexc_le : excessCount (tupleSet n) (BadPat k) p ≤ 45 * n ^ 2 - 40 * n := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hwrap_le : wraparoundExcess ζ (2 ^ k) ≤ 45 * n ^ 2 - 40 * n :=
    le_trans (by simpa [hn] using wraparoundExcess_le_excessCount (k := k) p hprim) hexc_le
  -- cast to the real headroom over the subgroup cardinality
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
  exact gaussianEnergyBound_three_of_wraparound_headroom hψ hm hprim hhead

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms badPrime_cap
#print axioms wraparoundExcess_le_excessCount
#print axioms gaussianEnergyBound_three_of_good_prime

end ArkLib.ProximityGap.Frontier.FS6AlmostAllPrimesWickRung
