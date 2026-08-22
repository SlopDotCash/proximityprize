/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# Door IV (Lane 1): the worst-`b` COSET-INDEX set is ARITHMETICALLY UNSTRUCTURED — no
# arithmetic-progression / sublattice class-restriction lever for door-(iv) anti-concentration

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_worstb_class_structure2.py` (the authoritative, artifact-corrected probe;
`..._structure.py` v1 is DEPRECATED — its QR axis is a g^j-parity scan artifact and its large-n scan
was prefix-biased; v2 works in the quotient `ℤ_k`, samples uniformly across the whole quotient, and
excludes the Fermat zero-index `v₂` artifact).

## The brief's literal Lane-1 question

The brief asks verbatim: "what arithmetic of `b` selects the worst coset alignment? is the worst-`b`
set itself structured?" A door-(iv) anti-concentration bound could be *narrowed* if the adversarial
frequency `b` were forced into a thin distinguished class (a coset of a proper sublattice / an
arithmetic progression / a fixed 2-adic-valuation or mod-`d` residue class) of the period quotient
`ℤ_k`, `k = (p−1)/n`. That would restrict the supremum to a sub-population.

## What the probe found (PROPER `μ_n`, p≈n⁴≫n³, EXACT integer phases, multiple structured primes,
   never n=q−1)

Writing `worst_j` = argmax-coset index of `|η_{g^j}|` over the cyclic quotient `ℤ_k`:

  * **2-adic valuation `v₂(worst_j)` is NOT deep.** Mean `v₂` over generic primes ≈ 0.2–1.6,
    fluctuating around the Geometric(1/2) expectation `1.0` of a uniformly random integer. (The lone
    `v₂ = 99` at the Fermat prime `p = 65537` is the known finite-size Fermat artifact — `worst_j = 0`
    — and is excluded; generic-prime `v₂` is random.) The worst index is NOT 2-adically structured.
  * **No arithmetic-progression / sublattice structure.** The gcd of the consecutive gaps of the top
    coset indices is **`1` for every prime tested** (full-scan at n=16,32; sampled at n=64,128). A set
    of integers whose consecutive-difference gcd is `1` is NOT contained in any proper residue class
    `r + d·ℤ`, `d ≥ 2`.
  * **No mod-`d` residue bias.** The `j mod 3` distribution of the top set is flat (~0.33).

VERDICT: the worst-`b` coset-index set is **arithmetically generic** in the quotient — no
2-adic depth, no AP/sublattice, no mod-`d` residue lock. So a door-(iv) anti-concentration bound
**cannot exploit a class-restriction of the worst-`b` set** to thin the search: the adversarial `b`
ranges over an arithmetically unstructured population. This pins another door-(iv) lever DEAD and is
distinct from (a) the worst-`b` *value*-side quotient arithmetic (gcd of values, scattered) and (b)
the worst-`b` internal complex geometry (generic EVT).

## What is FORMALIZED here (the enabling obstruction, axiom-clean)

The kernel-checkable content is the *enabling lemma* that turns the probe's `gap-gcd = 1` observation
into a genuine obstruction: a (multi-element) integer set whose consecutive-difference gcd is `1`
cannot lie inside any proper arithmetic progression `{ r + d·t : t ∈ ℤ }` with `d ≥ 2`. Equivalently:
if every element of a set is `≡ r (mod d)` then `d` divides every pairwise difference, hence divides
their gcd; so `gcd = 1 ⇒ d = 1`. This is the citable obstruction the probe instantiates.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVWorstCosetIndex

open scoped BigOperators

/-- **Core arithmetic fact.** If two integers lie in the same residue class mod `d`
(`a ≡ r` and `b ≡ r (mod d)`), then `d` divides their difference. -/
theorem dvd_sub_of_same_residue {d r a b : ℤ}
    (ha : a % d = r) (hb : b % d = r) : d ∣ (a - b) := by
  have hmod : a % d = b % d := by rw [ha, hb]
  exact Int.ModEq.dvd hmod.symm

/-- **Two-point sublattice obstruction.** If `d` divides each of `a - r₀` and `b - r₀` (i.e. both
`a` and `b` lie in the progression `r₀ + d·ℤ`), then `d` divides their difference `a - b`. This is
the mechanism: membership in a common AP forces `d` to divide all pairwise differences. -/
theorem dvd_diff_of_mem_progression {d r₀ a b : ℤ}
    (ha : d ∣ (a - r₀)) (hb : d ∣ (b - r₀)) : d ∣ (a - b) := by
  have : a - b = (a - r₀) - (b - r₀) := by ring
  rw [this]
  exact dvd_sub ha hb

/-- **The enabling obstruction (consecutive-difference gcd = 1 forbids any proper AP).**
Let `t₀ < t₁ < t₂` be three points (e.g. the top three worst coset indices) and suppose the gcd of the
two consecutive gaps is `1`: `Int.gcd (t₁ - t₀) (t₂ - t₁) = 1`. Then there is NO modulus `d ≥ 2`
together with a residue `r₀` placing all three in the single progression `r₀ + d·ℤ`. Hence the worst
coset-index set cannot be class-restricted to a proper arithmetic progression — the probe's
`top-gap-gcd = 1` is a genuine no-AP obstruction, not a coincidence. -/
theorem no_proper_progression_of_consecutive_gap_gcd_one
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ d r₀ : ℤ, 2 ≤ d →
      ¬ (d ∣ (t₀ - r₀) ∧ d ∣ (t₁ - r₀) ∧ d ∣ (t₂ - r₀)) := by
  rintro d r₀ hd ⟨h0, h1, h2⟩
  -- d divides each consecutive gap, hence divides their gcd, which is 1, so d = 1: contradiction.
  have hg1 : d ∣ (t₁ - t₀) := dvd_diff_of_mem_progression h1 h0
  have hg2 : d ∣ (t₂ - t₁) := dvd_diff_of_mem_progression h2 h1
  -- d divides the integer gcd of the two gaps
  have hdvd_gcd : d ∣ (Int.gcd (t₁ - t₀) (t₂ - t₁) : ℤ) := by
    have hn : (d.natAbs) ∣ Int.gcd (t₁ - t₀) (t₂ - t₁) :=
      Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hg1) (Int.natAbs_dvd_natAbs.mpr hg2)
    have : (d.natAbs : ℤ) ∣ (Int.gcd (t₁ - t₀) (t₂ - t₁) : ℤ) := Int.natCast_dvd_natCast.mpr hn
    exact (Int.natAbs_dvd.mp this)
  rw [hgcd] at hdvd_gcd
  -- d ∣ 1 with d ≥ 2 is impossible
  have : d ∣ (1 : ℤ) := by simpa using hdvd_gcd
  have hle : d ≤ 1 := Int.le_of_dvd (by norm_num) this
  omega


/-- **Direct modular-residue obstruction.**  The same `gap-gcd = 1` witness also forbids putting the
three worst coset indices in one residue class modulo any proper modulus `d ≥ 2`.  This is the exact
formal interface for the probe's "no mod-`d` residue bias" verdict: common residue would force `d` to
divide both consecutive gaps, hence to divide their gcd `1`. -/
theorem no_common_residue_mod_of_consecutive_gap_gcd_one
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ d r : ℤ, 2 ≤ d → ¬ (t₀ % d = r ∧ t₁ % d = r ∧ t₂ % d = r) := by
  rintro d r hd ⟨h0, h1, h2⟩
  have hg1 : d ∣ (t₁ - t₀) := dvd_sub_of_same_residue h1 h0
  have hg2 : d ∣ (t₂ - t₁) := dvd_sub_of_same_residue h2 h1
  have hdvd_gcd : d ∣ (Int.gcd (t₁ - t₀) (t₂ - t₁) : ℤ) := by
    have hn : (d.natAbs) ∣ Int.gcd (t₁ - t₀) (t₂ - t₁) :=
      Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr hg1) (Int.natAbs_dvd_natAbs.mpr hg2)
    have : (d.natAbs : ℤ) ∣ (Int.gcd (t₁ - t₀) (t₂ - t₁) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hn
    exact Int.natAbs_dvd.mp this
  rw [hgcd] at hdvd_gcd
  have hone : d ∣ (1 : ℤ) := by simpa using hdvd_gcd
  have hle : d ≤ 1 := Int.le_of_dvd (by norm_num) hone
  omega

/-- **Specialization corollary (no 2-adic class-restriction).** The probe's `d = 2` instance: a
worst-coset-index triple with consecutive-gap-gcd `1` cannot all share a common parity (mod-2 class).
So the worst-`b` set is not parity/2-adically restricted at the index level — matching the measured
random `v₂(worst_j)`. -/
theorem worst_index_not_parity_restricted
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ r₀ : ℤ, ¬ ((2 : ℤ) ∣ (t₀ - r₀) ∧ (2 : ℤ) ∣ (t₁ - r₀) ∧ (2 : ℤ) ∣ (t₂ - r₀)) := by
  intro r₀
  exact no_proper_progression_of_consecutive_gap_gcd_one hgcd 2 r₀ (le_refl 2)

/-- **No common divisor specialization.**  The `gap-gcd = 1` certificate also rules out the
stronger-looking but actually identical claim that the three observed worst-coset indices all lie in
`dℤ` for any proper modulus `d ≥ 2`.  This is the probe-facing form for rejecting a hidden
"all worst indices have a common arithmetic factor" lever. -/
theorem no_common_divisor_of_consecutive_gap_gcd_one
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ∀ d : ℤ, 2 ≤ d → ¬ (d ∣ t₀ ∧ d ∣ t₁ ∧ d ∣ t₂) := by
  intro d hd h
  have hprogression : d ∣ (t₀ - 0) ∧ d ∣ (t₁ - 0) ∧ d ∣ (t₂ - 0) := by
    simpa using h
  exact no_proper_progression_of_consecutive_gap_gcd_one hgcd d 0 hd hprogression

/-- **No all-even specialization.**  In particular, a `gap-gcd = 1` witness forbids the top-three
worst-coset indices from all having positive 2-adic valuation.  This is the exact integer certificate
behind the Lane-1 verdict that the worst-`b` indices are not trapped in the even sublattice. -/
theorem not_all_even_of_consecutive_gap_gcd_one
    {t₀ t₁ t₂ : ℤ} (hgcd : Int.gcd (t₁ - t₀) (t₂ - t₁) = 1) :
    ¬ ((2 : ℤ) ∣ t₀ ∧ (2 : ℤ) ∣ t₁ ∧ (2 : ℤ) ∣ t₂) := by
  exact no_common_divisor_of_consecutive_gap_gcd_one hgcd 2 (le_refl 2)

end ProximityGap.Frontier.DoorIVWorstCosetIndex

#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.dvd_sub_of_same_residue
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.dvd_diff_of_mem_progression
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.no_proper_progression_of_consecutive_gap_gcd_one
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.worst_index_not_parity_restricted
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.no_common_residue_mod_of_consecutive_gap_gcd_one
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.no_common_divisor_of_consecutive_gap_gcd_one
#print axioms ProximityGap.Frontier.DoorIVWorstCosetIndex.not_all_even_of_consecutive_gap_gcd_one
