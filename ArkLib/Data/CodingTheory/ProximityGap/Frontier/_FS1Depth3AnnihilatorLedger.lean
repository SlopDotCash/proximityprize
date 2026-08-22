/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R53Depth3ExcessHeadroom

/-!
# LANE FS1 (#466, Fable session 2026-07-09): THE ANNIHILATOR LEDGER — an unconditional
  (prime × pattern) double count turning the r53 headroom atom into an
  ALMOST-ALL-PRIMES depth-3 Wick rung

**The idea (new to the tree at fixed depth).**  A char-`p` depth-3 wraparound excess tuple is a
*nontrivial exponent pattern* `σ` (a 6-tuple of `n`-th-root exponents whose signed root-of-unity
sum is nonzero in char 0) that happens to vanish at the mod-`p` root `ζ_p`.  Every such pattern
owns a nonzero integer annihilator `N(σ)` (for 2-power `n`: the resultant
`Res(x^{n/2}+1, σ̄)`, of height `≤ 6^{n/2}`), and `σ` can only go bad at a prime dividing
`N(σ)`.  So each pattern is bad at `≤ log₂(6^{n/2})/log₂(min p) = O(n/log p)` primes of the
family — and a (prime × pattern) double count caps the TOTAL excess over any prime family,
hence (Markov) the number of primes whose excess exceeds the r53 headroom `45n² − 40n`.

**What is proven here, unconditionally (no named hypotheses inside the proofs):**
* `sum_badCount_eq` — the exact incidence double count
  `∑_{p ∈ P} excess(p) = ∑_{σ ∈ pats} #{p ∈ P : Bad p σ}`.
* `perPattern_primeCount_le` — the height cap: if every prime of the family is `≥ 2^s` and
  pattern `σ` has a nonzero annihilator `N ≤ H` divisible by every prime at which `σ` is bad,
  then `σ` is bad at `≤ Nat.log 2 H / s` primes (distinct primes ≥ 2^s dividing `N` multiply).
* `badPrime_card_mul_le` / `annihilator_ledger_badPrime_cap` — the Markov composition:
  `#{p ∈ P : excess(p) ≥ T} · T ≤ |pats| · (Nat.log 2 H / s)`.
* `gaussianEnergyBound_three_of_ledger_good_prime` — the r53 weld: at any prime of the family
  NOT in the capped bad set, the excess fits the headroom, so the EXACT Wick bound
  `GaussianEnergyBound G 3` fires (via `gaussianEnergyBound_three_of_excess_headroom`).

**Honest scope (read before consuming):**
* The pattern set / `Bad` relation / excess-decomposition hypothesis
  (`Depth3ExcessBounded G (excess p)`) are ABSTRACT inputs here.  Instantiating them for
  `G = μ_n` requires (i) the exponent-parametrization of `addEnergy3` against the char-0
  closed form `15n³ − 45n² + 40n` (the r50/r52-established decomposition; pattern count
  `≤ n⁶`), and (ii) discharging the annihilator via the cyclotomic resultant with
  `H = 6^{n/2}` (classical height bound).  Both are named follow-up bricks, not done here.
* At `|pats| = n⁶`, `H = 6^{n/2}`, `p ≥ n^β` the cap reads
  `#bad ≤ n⁶ · (3n/(2·β·log₂ n)) / 45n² ≈ n⁵/(30·β·log₂ n)` — NON-VACUOUS against the
  `≈ n^{β−1}/(β ln n)` primes `≡ 1 (mod n)` below `n^β` only for `β ≳ 6`; at the prize shape
  `β ≈ 5.3` it caps nothing.  This is the fixed-depth (r=3) shadow of the F9/J1 verdict
  (`DISPROOF_LOG` union-budget wall): the ledger gives an ALMOST-ALL-primes rung at high `β`,
  not a per-prime prize rung.  Logged as a reduction/positive brick, not a closure.

Issue #466, lane FS1.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

variable {Pat : Type*} [DecidableEq Pat]

section Ledger

variable (P : Finset ℕ) (pats : Finset Pat) (Bad : ℕ → Pat → Prop)
  [∀ p σ, Decidable (Bad p σ)]

/-- The per-prime excess count: the number of patterns that go bad at `p`. -/
def excessCount (p : ℕ) : ℕ := (pats.filter (fun σ => Bad p σ)).card

/-- **The incidence double count.**  Total excess over the prime family = total badness over
the pattern family. -/
theorem sum_badCount_eq :
    ∑ p ∈ P, excessCount pats Bad p
      = ∑ σ ∈ pats, (P.filter (fun p => Bad p σ)).card := by
  simp only [excessCount, Finset.card_filter]
  exact Finset.sum_comm

/-- **The height cap.**  If every prime of the family is `≥ 2^s` (with `s > 0`) and the pattern
`σ` has a nonzero integer annihilator `N ≤ H` divisible by every prime of the family at which
`σ` is bad, then `σ` is bad at no more than `Nat.log 2 H / s` primes of the family. -/
theorem perPattern_primeCount_le {s L H : ℕ} (hs : 0 < s) (hHL : H ≤ 2 ^ L)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (σ : Pat) {N : ℕ} (hN0 : N ≠ 0) (hNH : N ≤ H)
    (hdvd : ∀ p ∈ P, Bad p σ → p ∣ N) :
    (P.filter (fun p => Bad p σ)).card ≤ L / s := by
  set S : Finset ℕ := P.filter (fun p => Bad p σ) with hS
  have hSsub : S ⊆ P := Finset.filter_subset _ _
  -- the product of the distinct primes in S divides N
  have hprod_dvd : (∏ p ∈ S, p) ∣ N := by
    refine Finset.prod_primes_dvd N ?_ ?_
    · intro p hp
      exact (hP p (hSsub hp)).1.prime
    · intro p hp
      have hpP := hSsub hp
      have hbad : Bad p σ := (Finset.mem_filter.mp hp).2
      exact hdvd p hpP hbad
  -- each prime is ≥ 2^s, so the product is ≥ (2^s)^|S|
  have hpow_le_prod : (2 ^ s) ^ S.card ≤ ∏ p ∈ S, p :=
    Finset.pow_card_le_prod S _ _ (fun p hp => (hP p (hSsub hp)).2)
  have hprod_le : (∏ p ∈ S, p) ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hprod_dvd
  have hpow_le_pow : 2 ^ (s * S.card) ≤ 2 ^ L := by
    calc 2 ^ (s * S.card) = (2 ^ s) ^ S.card := by rw [pow_mul]
      _ ≤ ∏ p ∈ S, p := hpow_le_prod
      _ ≤ N := hprod_le
      _ ≤ H := hNH
      _ ≤ 2 ^ L := hHL
  have hlog : s * S.card ≤ L :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow_le_pow
  exact Nat.le_div_iff_mul_le hs |>.mpr (by rwa [Nat.mul_comm] at hlog)

/-- **The Markov composition.**  With a uniform per-pattern cap `D`, the number of primes whose
excess reaches `T` satisfies `#bad · T ≤ |pats| · D`. -/
theorem badPrime_card_mul_le {D T : ℕ}
    (hcap : ∀ σ ∈ pats, (P.filter (fun p => Bad p σ)).card ≤ D) :
    (P.filter (fun p => T ≤ excessCount pats Bad p)).card * T
      ≤ pats.card * D := by
  have hmarkov :
      (P.filter (fun p => T ≤ excessCount pats Bad p)).card * T
        ≤ ∑ p ∈ P, excessCount pats Bad p := by
    calc (P.filter (fun p => T ≤ excessCount pats Bad p)).card * T
        = ∑ _p ∈ P.filter (fun p => T ≤ excessCount pats Bad p), T := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ P.filter (fun p => T ≤ excessCount pats Bad p),
            excessCount pats Bad p :=
          Finset.sum_le_sum (fun p hp => (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ P, excessCount pats Bad p :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc (P.filter (fun p => T ≤ excessCount pats Bad p)).card * T
      ≤ ∑ p ∈ P, excessCount pats Bad p := hmarkov
    _ = ∑ σ ∈ pats, (P.filter (fun p => Bad p σ)).card :=
        sum_badCount_eq P pats Bad
    _ ≤ ∑ _σ ∈ pats, D := Finset.sum_le_sum hcap
    _ = pats.card * D := by rw [Finset.sum_const, smul_eq_mul]

/-- **THE LEDGER CAP (headline).**  Annihilators of height `≤ H ≤ 2^L` + primes `≥ 2^s` ⟹ the
number of primes of the family whose excess reaches `T > 0` is at most
`|pats| · (L / s) / T`. -/
theorem annihilator_ledger_badPrime_cap {s L H T : ℕ} (hs : 0 < s) (hT : 0 < T)
    (hHL : H ≤ 2 ^ L)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (hann : ∀ σ ∈ pats, ∃ N : ℕ, N ≠ 0 ∧ N ≤ H ∧ ∀ p ∈ P, Bad p σ → p ∣ N) :
    (P.filter (fun p => T ≤ excessCount pats Bad p)).card
      ≤ pats.card * (L / s) / T := by
  have hcap : ∀ σ ∈ pats,
      (P.filter (fun p => Bad p σ)).card ≤ L / s := by
    intro σ hσ
    obtain ⟨N, hN0, hNH, hdvd⟩ := hann σ hσ
    exact perPattern_primeCount_le P Bad hs hHL hP σ hN0 hNH hdvd
  have := badPrime_card_mul_le P pats Bad (D := L / s) (T := T) hcap
  exact Nat.le_div_iff_mul_le hT |>.mpr this

end Ledger

section Weld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Cast helper: for `1 ≤ n` the ℕ headroom `45n² − 40n` casts to the ℝ headroom. -/
theorem headroom_cast {n : ℕ} (hn : 1 ≤ n) :
    ((45 * n ^ 2 - 40 * n : ℕ) : ℝ) = 45 * (n : ℝ) ^ 2 - 40 * (n : ℝ) := by
  have h : 40 * n ≤ 45 * n ^ 2 := by nlinarith
  push_cast [Nat.cast_sub h]
  ring

/-- **THE r53 WELD.**  At any prime of the family that is NOT in the ledger-capped bad set
(threshold `T = 45n² − 40n + 1`), the per-prime excess fits the r53 headroom, so — given the
excess decomposition for the depth-3 energy of `G` — the EXACT Wick bound
`GaussianEnergyBound G 3` fires.  Combined with `annihilator_ledger_badPrime_cap`, this is the
almost-all-primes depth-3 Wick rung. -/
theorem gaussianEnergyBound_three_of_ledger_good_prime
    (P : Finset ℕ) (pats : Finset Pat) (Bad : ℕ → Pat → Prop)
    [∀ p σ, Decidable (Bad p σ)]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter
      (fun p => 45 * G.card ^ 2 - 40 * G.card + 1 ≤ excessCount pats Bad p))
    (hn : 1 ≤ G.card)
    (hdecomp : Depth3ExcessBounded G ((excessCount pats Bad p : ℕ) : ℝ)) :
    GaussianEnergyBound G 3 := by
  -- outside the bad set the excess is ≤ 45n² − 40n
  have hexc_le : excessCount pats Bad p ≤ 45 * G.card ^ 2 - 40 * G.card := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hexc_le_real :
      ((excessCount pats Bad p : ℕ) : ℝ)
        ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ) := by
    calc ((excessCount pats Bad p : ℕ) : ℝ)
        ≤ ((45 * G.card ^ 2 - 40 * G.card : ℕ) : ℝ) := by exact_mod_cast hexc_le
      _ = 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ) := headroom_cast hn
  exact gaussianEnergyBound_three_of_excess_headroom hψ G hdecomp hexc_le_real

end Weld

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms sum_badCount_eq
#print axioms perPattern_primeCount_le
#print axioms badPrime_card_mul_le
#print axioms annihilator_ledger_badPrime_cap
#print axioms gaussianEnergyBound_three_of_ledger_good_prime

end ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
