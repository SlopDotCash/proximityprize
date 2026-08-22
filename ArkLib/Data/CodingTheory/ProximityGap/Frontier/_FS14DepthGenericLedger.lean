/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS1Depth3AnnihilatorLedger
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS3AnnihilatorHeightBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS11GenericDepthDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS13PairingInductionWick

/-!
# LANE FS14 (#466, Fable session 2026-07-09): THE DEPTH-GENERIC LEDGER THEOREM —
  `GaussianEnergyBound (μ_n) r` at almost all primes, for EVERY fixed depth `r`

The assembly of the completed FS arc (all inputs in-tree, none named):

* **`badPrime_capG`** — for `n = 2^{k+1}` and any family `P` of primes `≥ 2^s`, the primes at
  which ANY nontrivial depth-`r` pattern vanishes number at most
  `n^r·n^r·((k+1+b)·n/s)` (`2r ≤ 2^b`) — FS1's ledger fed by FS3's resultant annihilators on
  FS11's pattern polynomials.
* **`wraparoundExcessG_le_excessCountG`** — any concrete field's depth-`r` wraparound excess
  is dominated by the abstract per-prime badness count.
* **`gaussianEnergyBound_of_good_prime`** — at every prime of the family outside the capped
  bad set, in every field of that characteristic with a primitive `n`-th root:
  `rEnergy (μ_n) r = trivialCountG` EXACTLY (zero excess), and by FS13's pairing-induction
  census `≤ (2r−1)‼·n^r` — i.e. the depth-`r` Wick energy rung `GaussianEnergyBound (μ_n) r`
  holds.  ONE theorem, every fixed depth.

**Honest scope:** fixed `r`; the exceptional-prime budget `≈ n^{2r+1}/s` requires prime
families of size `n^{β−1}` with `β ≳ 2r+2` to be non-vacuous; the prize's joint limit
`r ≈ ln q` — the Paley/BGK wall, the δ* core — remains untouched and is not claimed.

Issue #466, lane FS14.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger

open ArkLib.ProximityGap.Frontier.FS1Depth3AnnihilatorLedger
open ArkLib.ProximityGap.Frontier.FS3AnnihilatorHeightBound
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.FS13PairingInductionWick
open ArkLib.ProximityGap.GaussPeriodMomentBound

open scoped Classical

/-- The depth-`r` badness relation: a nonzero pattern that vanishes at an order-`2^{k+1}`
root in some field of characteristic `p`. -/
def BadPatG (k r : ℕ) (p : ℕ) (ab : (Fin r → ℕ) × (Fin r → ℕ)) : Prop :=
  patternPolyG (2 ^ k) ab.1 ab.2 ≠ 0 ∧
    ∃ (F : Type) (_ : Field F) (_ : CharP F p) (ζ : F),
      ζ ^ (2 ^ k) = -1 ∧ aeval ζ (patternPolyG (2 ^ k) ab.1 ab.2) = 0

/-- The depth-`r` pattern family. -/
noncomputable def patsG (k r : ℕ) : Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  expTuples (2 * 2 ^ k) r ×ˢ expTuples (2 * 2 ^ k) r

theorem patsG_card (k r : ℕ) : (patsG k r).card = (2 * 2 ^ k) ^ r * (2 * 2 ^ k) ^ r := by
  rw [patsG, Finset.card_product, expTuples_card]

/-- **THE DEPTH-`r` BAD-PRIME CAP.** -/
theorem badPrime_capG {k s r b T : ℕ} (hs : 0 < s) (hT : 0 < T) (hb : 2 * r ≤ 2 ^ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p) :
    (P.filter (fun p => T ≤ excessCount (patsG k r) (BadPatG k r) p)).card
      ≤ (2 * 2 ^ k) ^ r * (2 * 2 ^ k) ^ r * (((k + 1 + b) * 2 ^ (k + 1)) / s) / T := by
  have hcap := annihilator_ledger_badPrime_cap (P := P)
    (pats := patsG k r) (Bad := BadPatG k r)
    (s := s) (L := (k + 1 + b) * 2 ^ (k + 1)) (H := 2 ^ ((k + 1 + b) * 2 ^ (k + 1)))
    (T := T) hs hT le_rfl hP ?_
  · rwa [patsG_card] at hcap
  · intro ab hab
    by_cases hzero : patternPolyG (2 ^ k) ab.1 ab.2 = 0
    · refine ⟨1, one_ne_zero, Nat.one_le_two_pow, ?_⟩
      intro p _ hbad
      exact absurd hzero hbad.1
    · rw [patsG, Finset.mem_product] at hab
      obtain ⟨ha, hbmem⟩ := hab
      rw [expTuples, Fintype.mem_piFinset] at ha hbmem
      have haval : ∀ i, ab.1 i < 2 * 2 ^ k := fun i => mem_range.mp (ha i)
      have hbval : ∀ i, ab.2 i < 2 * 2 ^ k := fun i => mem_range.mp (hbmem i)
      have hdeg : (patternPolyG (2 ^ k) ab.1 ab.2).natDegree < 2 ^ k :=
        patternPolyG_natDegree_lt (by positivity) haval hbval
      have hcoeff : ∀ i, |(patternPolyG (2 ^ k) ab.1 ab.2).coeff i| ≤ 2 ^ b := by
        intro i
        calc |(patternPolyG (2 ^ k) ab.1 ab.2).coeff i|
            ≤ (2 * r : ℤ) := patternPolyG_coeff_abs_le (2 ^ k) ab.1 ab.2 i
          _ ≤ 2 ^ b := by exact_mod_cast hb
      obtain ⟨N, hN0, hNH, hdvd⟩ :=
        pattern_annihilator_exists_with_height (k := k) (b := b) hzero hdeg hcoeff
      refine ⟨N, hN0, hNH, ?_⟩
      rintro p _ ⟨-, F, hF, hCh, ζ, hζ, hroot⟩
      exact hdvd F hF p hCh ζ hζ hroot

/-- The concrete depth-`r` wraparound excess is dominated by the abstract badness count. -/
theorem wraparoundExcessG_le_excessCountG {k r : ℕ} {F : Type} [Field F] [Fintype F]
    [DecidableEq F] (p : ℕ) [CharP F p] {ζ : F}
    (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k)) :
    wraparoundExcessG ζ (2 ^ k) r ≤ excessCount (patsG k r) (BadPatG k r) p := by
  unfold wraparoundExcessG excessCount patsG
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  refine Finset.card_le_card ?_
  intro ab hab
  rw [Finset.mem_filter] at hab ⊢
  obtain ⟨hmem, hne, hroot⟩ := hab
  exact ⟨hmem, hne, F, inferInstance, inferInstance, ζ, zeta_pow_m hm hprim, hroot⟩

/-- **THE DEPTH-GENERIC GOOD-PRIME WICK RUNG.**  At any prime of the family outside the
T=1 capped bad set, in every field of that characteristic with a primitive `n`-th root
(`n = 2^{k+1} = 2·2^k`), the depth-`r` energy takes exactly its field-free char-0 value and
satisfies the Wick bound: `GaussianEnergyBound (μ_n) r`. -/
theorem gaussianEnergyBound_of_good_prime {k s r b : ℕ} (hs : 0 < s) (hb : 2 * r ≤ 2 ^ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2 ^ s ≤ p)
    (p : ℕ) (hp : p ∈ P)
    (hgood : p ∉ P.filter (fun p => 1 ≤ excessCount (patsG k r) (BadPatG k r) p))
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p]
    {ζ : F} (hprim : IsPrimitiveRoot ζ (2 * 2 ^ k)) :
    GaussianEnergyBound ((range (2 * 2 ^ k)).image (ζ ^ ·)) r := by
  have hm : (0 : ℕ) < 2 ^ k := by positivity
  -- zero excess off the bad set
  have hexc0 : excessCount (patsG k r) (BadPatG k r) p = 0 := by
    by_contra h
    exact hgood (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hwrap0 : wraparoundExcessG ζ (2 ^ k) r = 0 := by
    have := wraparoundExcessG_le_excessCountG (k := k) (r := r) (F := F) p hprim
    omega
  -- exact char-0 energy + Wick census
  have hdec := rEnergy_eq_trivial_add_excess (F := F) hm hprim r
  rw [hwrap0, Nat.add_zero] at hdec
  have hwick := trivialCountG_le_wick (2 ^ k) r hm
  have hcard : ((range (2 * 2 ^ k)).image (ζ ^ ·)).card = 2 * 2 ^ k :=
    Gset_card hm hprim
  unfold GaussianEnergyBound
  rw [hcard, hdec]
  exact_mod_cast hwick

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms badPrime_capG
#print axioms wraparoundExcessG_le_excessCountG
#print axioms gaussianEnergyBound_of_good_prime

end ArkLib.ProximityGap.Frontier.FS14DepthGenericLedger
