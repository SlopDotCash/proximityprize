/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3NegSymConverse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3StrataCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The GENERAL-`r` char-`p` energy LOWER bound `rEnergy G r >= negSymCount G (2r)` (#444)

`Frontier/REnergyThreeCharPLowerBound.lean` (this session) landed the `r = 3` case of the char-`p`
energy lower bound (`rEnergy G 3 >= 15n^3 - 45n^2 + 40n`) via a tuple-count injection. This file
lifts that mechanism to **EVERY `r`**, char-`p`-universal, as a single uniform theorem:

> **`negSymCount G (2r) <= rEnergy G r`** for any negation-closed `G` (`0 ∉ G`, char ≠ 2) in ANY
> finite field, for ALL `r`.

i.e. the depth-`r` relation energy is at least the antipodally count-balanced `2r`-tuple census of
`G`, in any characteristic.

## Why this discharges the lower half of the `_BchksF5` squeeze

`_BchksF5_CharPAnomalyExpZero` defines the char-`p` energy anomaly `W_r := E_r(F_p) - E_r^{char0}`
and squeezes it `0 <= W_r <= Wick_r - E_r^{char0}`. It PROVES only the UPPER half
(`anomaly_le_gap`, from the open below-Wick hypothesis `hWick`); the LOWER half `0 <= W_r` (the
char-`p` energy is AT LEAST the char-`0` value -- the extra mod-`p` coincidences only ADD zero-sum
tuples, never remove the genuine ℂ-coincidences) is stated as fact in the docstring but never
proven. For the prize subgroup `μ_n`, `E_r^{char0} = negSymCount(μ_n) (2r)` (the char-`0`
Lam-Leung count-balanced census, an in-tree closed form per `r`), so this theorem IS the unproven
lower half `0 <= W_r`, supplied uniformly in `r` for the actual energy object.

## The mechanism (char-FREE, EXTEND-proven on landed substrate)

Two committed char-free pieces compose at general arity:

* `E3NegSymConverse.sum_eq_zero_of_fiber_balanced` (general arity `{m : ℕ}`): a `2r`-tuple of
  nonzero values whose value fibers are antipodally balanced is a genuine ZERO-SUM tuple. So the
  `negSymCount`-filter (fiber-balanced) is a SUBSET of the zero-sum filter
  (`negSymCount G (2r) <= zeroSumCount G (2r)`).
* `CharZeroWickEnergy.rEnergy_eq_zeroSumCount` (general arity, char-free negation-closure bijection
  `(v,w) ↦ v ⧺ (−w)`): `rEnergy G r = zeroSumCount G (2r)`.

Chaining: `negSymCount G (2r) <= zeroSumCount G (2r) = rEnergy G r`.

## Scope / honesty (rule 1,3,4,6 + asymptotic guard)

This is the `>=` (EASY) direction, UNCONDITIONAL in char `p`: the count-balanced tuples are always
present. The HARD direction is the matching UPPER bound `rEnergy G r <= E_r^{char0}` (equality),
which is FALSE in char `p` at small `p` (extra collisions add zero-sum tuples that are NOT
count-balanced) and is precisely the BGK/Burgess `√`-cancellation wall (= `W_r = 0`, holds only for
`p` above the onset threshold). This brick supplies only `0 <= W_r`. It is NON-MOMENT (a tuple-count
injection, not an additive-moment cancellation), EXTEND-proven on two landed char-free substrate
lemmas, and makes NO capacity / beyond-Johnson / cliff-at-n/2 claim. CORE
`M(μ_n) <= C·√(n·log(p/n))` stays OPEN.

Probe (`scripts/probes/probe_energy_lower_bound_general.py`, 12/12 decisive): PROPER thin
`μ_n = 2^a` (a=2..4), `p = 1 mod n`, NEVER `n = q-1`, small AND large primes (`p > n^3` and
`p < n^3`) incl. Fermat 257/65537, `r = 2,3,4`. In EVERY case `W_r = rEnergy(F_p) r -
negSymCount(2r) >= 0`; `W_r = 0` exactly when `p > n^3`, `W_r > 0` at small `p` (the
extra-collision surplus). The lower bound is UNCONDITIONAL.

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.Frontier.E3StrataCount (negSymCount)
open ArkLib.ProximityGap.Frontier.E3NegSymConverse (sum_eq_zero_of_fiber_balanced)
open ArkLib.ProximityGap.NegationClosedWalk (zeroSumCount)
open ProximityGap.Frontier.CharZeroWickEnergy (rEnergy_eq_zeroSumCount)

namespace ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Count-balanced `2r`-tuples inject into zero-sum `2r`-tuples (char-free, general arity).**
The `negSymCount`-filter (antipodally fiber-balanced) is a SUBSET of the zero-sum filter, because
every count-balanced tuple of nonzero values is a genuine zero-sum tuple
(`sum_eq_zero_of_fiber_balanced`, char-free). Hence `negSymCount G m <= zeroSumCount G m` for ANY
arity `m` (here used at `m = 2r`). -/
theorem negSymCount_le_zeroSumCount (G : Finset F) (m : ℕ) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    negSymCount G m ≤ zeroSumCount G m := by
  classical
  unfold negSymCount zeroSumCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc ⊢
  obtain ⟨hcG, hbal⟩ := hc
  refine ⟨hcG, ?_⟩
  exact sum_eq_zero_of_fiber_balanced h2 c (fun i => fun h => h0 (h ▸ hcG i)) hbal

/-- **The GENERAL-`r` char-`p` energy lower bound (HEADLINE).** For any negation-closed `G`
(`0 ∉ G`, char ≠ 2) in a finite field and ANY `r`, the depth-`r` relation energy is at least the
antipodally count-balanced `2r`-tuple census:
`rEnergy G r >= negSymCount G (2r)`. UNCONDITIONAL in the characteristic. Combines the count
injection `negSymCount G (2r) <= zeroSumCount G (2r)` with the char-free negation-closure bijection
`rEnergy G r = zeroSumCount G (2r)`. -/
theorem negSymCount_le_rEnergy (G : Finset F) (r : ℕ) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    negSymCount G (2 * r) ≤ rEnergy G r := by
  have hinj : negSymCount G (2 * r) ≤ zeroSumCount G (2 * r) :=
    negSymCount_le_zeroSumCount G (2 * r) h2 h0
  have hbij : rEnergy G r = zeroSumCount G (2 * r) := rEnergy_eq_zeroSumCount G r hneg
  rw [hbij]
  exact hinj

/-- **The `W_r >= 0` lower half of the `_BchksF5` squeeze, supplied uniformly in `r`.** Over `ℤ`,
`0 <= rEnergy G r - negSymCount G (2r)`. For `G = μ_n` the subtrahend `negSymCount(μ_n) (2r)` is the
char-`0` energy `E_r^{char0}` (the count-balanced Lam-Leung census), so this is exactly the
unproven lower half `0 <= W_r = E_r(F_p) - E_r^{char0}` of the `_BchksF5` anomaly squeeze, in any
characteristic, for every `r`. -/
theorem charP_anomaly_nonneg (G : Finset F) (r : ℕ) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) :
    (0 : ℤ) ≤ (rEnergy G r : ℤ) - (negSymCount G (2 * r) : ℤ) := by
  have h := negSymCount_le_rEnergy G r h2 h0 hneg
  have : (negSymCount G (2 * r) : ℤ) ≤ (rEnergy G r : ℤ) := by exact_mod_cast h
  linarith

end ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound.negSymCount_le_zeroSumCount
#print axioms ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound.negSymCount_le_rEnergy
#print axioms ArkLib.ProximityGap.Frontier.REnergyGeneralCharPLowerBound.charP_anomaly_nonneg
