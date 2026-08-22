/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS14DepthGenericLedger

/-!
# LANE FS17 (#466, Fable session 2026-07-09): THE SIMULTANEOUS LADDER — one good-prime set
  on which ALL Wick rungs `r ≤ R` hold at once

FS14/FS15 give each depth its own good-prime set.  A finite union bound merges them:

* **`simultaneous_badPrime_cap`** — the primes bad at ANY depth `r ∈ [1, R]` number at most
  `Σ_{r ≤ R} n^{2r}·((k+1+bᵣ)·n/s)` (each summand the FS14 T=1 cap).
* **`gaussianEnergyBound_ladder_of_good_prime`** — off that one set, in every field of the
  characteristic with a primitive `n`-th root, `GaussianEnergyBound (μ_n) r` holds for EVERY
  `r ∈ [1, R]` simultaneously — the usable form for min-over-depth moment optimization
  (`min_{r ≤ R} M_r`) at a single prime.

**Honest scope:** the union budget is dominated by the deepest term `≈ n^{2R+1}/s`, so
simultaneity is free (same window `β ≳ 2R+2` as the single deepest rung); the prize joint
limit `R ≈ ln q` stays out of reach exactly as before (FS15's closing no-go).  This brick is
interface hygiene: the ladder becomes a single-event statement instead of `R` separate ones.

Issue #466, lane FS17.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS17SimultaneousLadder

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger
open ArkLib.ProximityGap.GaussPeriodMomentBound

open scoped Classical

variable {k s R : ℕ}

/-- `2r ≤ 2^r` for `r ≥ 1`. -/
theorem two_mul_le_two_pow {r : ℕ} (hr : 1 ≤ r) : 2 * r ≤ 2 ^ r := by
  induction r with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n <;> norm_num
    · have hle := ih h
      have h2 : (2 : ℕ) ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      calc 2 * (n + 1) = 2 * n + 2 := by ring
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-- The depth-uniform bad set: primes at which some depth `r ∈ [1, R]` has a vanishing
nontrivial pattern. -/
noncomputable def ladderBadSet (k R : ℕ) (P : Finset ℕ) : Finset ℕ :=
  P.filter (fun p => ∃ r ∈ Finset.Icc 1 R,
    1 ≤ excessCount (patsG k r) (BadPatG k r) p)

/-- **THE SIMULTANEOUS CAP.**  The depth-uniform bad set is bounded by the sum of the
per-depth FS14 caps. -/
theorem simultaneous_badPrime_cap (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p) :
    (ladderBadSet k R P).card
      ≤ ∑ r ∈ Finset.Icc 1 R,
          (2 * 2 ^ k) ^ r * (2 * 2 ^ k) ^ r * (((k + 1 + r) * 2 ^ (k + 1)) / s) := by
  -- the bad set is contained in the union of the per-depth bad sets
  have hsub : ladderBadSet k R P
      ⊆ (Finset.Icc 1 R).biUnion (fun r =>
          P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p)) := by
    intro p hp
    simp only [ladderBadSet, Finset.mem_filter] at hp
    obtain ⟨hpP, r, hr, hexc⟩ := hp
    rw [Finset.mem_biUnion]
    exact ⟨r, hr, Finset.mem_filter.mpr ⟨hpP, hexc⟩⟩
  calc (ladderBadSet k R P).card
      ≤ ((Finset.Icc 1 R).biUnion (fun r =>
          P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
          (P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
          (2 * 2 ^ k) ^ r * (2 * 2 ^ k) ^ r * (((k + 1 + r) * 2 ^ (k + 1)) / s) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        have h := badPrime_capG (k := k) (s := s) (r := r) (b := r) (T := 1)
          hs one_pos (two_mul_le_two_pow (Finset.mem_Icc.mp hr).1) P hP
        simpa using h

/-- **THE SIMULTANEOUS GOOD-PRIME LADDER.**  Off the one capped set, every Wick rung
`r ∈ [1, R]` holds at once. -/
theorem gaussianEnergyBound_ladder_of_good_prime (hs : 0 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P) (hgood : p ∉ ladderBadSet k R P)
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k))
    {r : ℕ} (hr : r ∈ Finset.Icc 1 R) :
    GaussianEnergyBound ((range (2 * 2 ^ k)).image (ζ ^ ·)) r := by
  have hb : 2 * r ≤ 2 ^ r := two_mul_le_two_pow (Finset.mem_Icc.mp hr).1
  have hnotbad : p ∉ P.filter
      (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p) := by
    intro hmem
    rw [Finset.mem_filter] at hmem
    apply hgood
    simp only [ladderBadSet, Finset.mem_filter]
    exact ⟨hp, r, hr, hmem.2⟩
  exact gaussianEnergyBound_of_good_prime hs hb P hP p hp hnotbad hprim

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms simultaneous_badPrime_cap
#print axioms gaussianEnergyBound_ladder_of_good_prime

end ArkLib.ProximityGap.Frontier.FS17SimultaneousLadder
