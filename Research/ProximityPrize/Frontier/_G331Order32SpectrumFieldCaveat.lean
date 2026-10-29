/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G331: the order-32 weight-{1,3} spectrum is not injective at `p = 65537`

The G328 lane refuted unguarded field-uniformity of the dimension-two spectrum at the
order-eight rung (`p = 17`).  G330 then pinned the exceptional set at that rung to exactly
`{17}`.  PR #264 recorded the next rung (`h = 8`, `n = 16`): the spectrum has 464 values at
every prime outside a 34-element exceptional set (largest 4049), and in particular is
injective at `p = 65537`.

This file records the next rung, `h = 16` (`n = 32`, `|data| = 4512`): at `p = 65537` the
map is *not* injective.  The deficiency is genuine, not saturation, since `65537 > 4512`.
The mechanism is that `65537 = 2^16 + 1`, so `2` has order 32 and `g = -8` is a 32nd root of
unity that is a small integer; the identity `g^5 + 2·g^10 = 1` holds in `ZMod 65537`
(because `2^30 ≡ -2^14`), which collides a weight-1 datum with a weight-3 datum.

Named prize claim advanced: `ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(`ArkLib/Data/CodingTheory/ProximityGap/TwoPowerSubsetSumSpectrum.lean`).  Its hypothesis
`hinj : Set.InjOn (spectrumVal g) (spectrumData h A)` is the KKH26 counting core.  At this
instance `hinj` is false, so the spectrum law `4512` is not available at `p = 65537`.

Companion executable census: `scripts/probes/probe_order32_weight13_spectrum.py`
(reproduces 3264 values at `p = 65537`, and 4512 at the prize-scale Proth primes
`k·2^128+1`).

Honest scope:
* Closes off a field choice for future n = 32 spectrum / MCA pins.  `65537` is an
  inadmissible stand-in field at this rung (small-field discipline, cf. SYZ53 / G84 / G328).
* Does **not** contradict any in-tree theorem: `sVal_injOn` requires `p > 2^80` and is
  unaffected; `subsetSumSpectrum_card` stays true (it is conditional on `hinj`).
* Not a δ\* pin, not a field-uniform census theorem, no production claim.
* PR #272 already prints `3264` / `4512` as side data via a different route.  What is new
  here is the injectivity reading against `subsetSumSpectrum_card`, the Lean certificate,
  and the `g = -8` collision mechanism.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat

open ArkLib.ProximityGap.KKH26

set_option maxRecDepth 10000

/-- `65537 = 2^16 + 1`, so `(2 : ZMod 65537)^16 = -1`. -/
theorem two_pow16 : ((2 : ZMod 65537) ^ 16) = -1 := by decide

/-- `g = -8 = -2^3` is a 32nd root of unity in `ZMod 65537`. -/
def g32 : ZMod 65537 := -8

theorem g32_pow16 : g32 ^ 16 = -1 := by
  unfold g32; decide

theorem g32_pow32 : g32 ^ 32 = 1 := by
  unfold g32; decide

/-- The collision identity: `g^5 + 2·g^10 = 1`, i.e. `-g^0 + g^5 + g^10 = -g^10`. -/
theorem collision_identity : g32 ^ 5 + 2 * g32 ^ 10 = 1 := by
  unfold g32; decide

/-- Weight-1 datum: support `{10}`, positive part empty, value `-g^10`. -/
def d1 : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨1, ⟨{10}, ∅⟩⟩

/-- Weight-3 datum: support `{0,5,10}`, positive part `{5,10}`, value `g^5+g^10-g^0`. -/
def d2 : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨3, ⟨{0, 5, 10}, {5, 10}⟩⟩

lemma sVal_d1 : sVal g32 d1.2 = -(g32 ^ 10) := by
  simp [d1, sVal]

lemma sVal_d2 : sVal g32 d2.2 = g32 ^ 5 + g32 ^ 10 - g32 ^ 0 := by
  simp [d2, sVal]

/-- The two data have the same signed-sum value in `ZMod 65537`. -/
theorem collision_sVal : sVal g32 d1.2 = sVal g32 d2.2 := by
  rw [sVal_d1, sVal_d2, pow_zero]
  have h5 : g32 ^ 5 = 1 - 2 * g32 ^ 10 := by
    have h := collision_identity
    linear_combination h
  rw [h5]
  ring

/-- `spectrumVal` agrees at the two data: the weight tag is forgotten. -/
theorem collision_spectrumVal : spectrumVal g32 d1 = spectrumVal g32 d2 :=
  collision_sVal

theorem d1_mem : d1 ∈ spectrumData 16 ({1, 3} : Finset ℕ) := by
  simp [spectrumData, mem_sigData, d1]

theorem d2_mem : d2 ∈ spectrumData 16 ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, d2]
  refine ⟨by decide, ?_, by decide⟩
  decide

theorem d1_ne_d2 : d1 ≠ d2 := by
  simp [d1, d2]

/-- **The n = 32 weight-`{1,3}` spectrum is not injective at `p = 65537`.**

This is the instance-level failure of `hinj` in `KKH26.subsetSumSpectrum_card` at the
campaign's favourite large stand-in field, one rung above the G328 / G330 boundary. -/
theorem not_injOn_spectrumVal_65537 :
    ¬ Set.InjOn (spectrumVal g32) (spectrumData 16 ({1, 3} : Finset ℕ)) := by
  intro hinj
  exact d1_ne_d2 (hinj d1_mem d2_mem collision_spectrumVal)

end ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat.two_pow16
#print axioms
  ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat.g32_pow32
#print axioms
  ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat.collision_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat.collision_spectrumVal
#print axioms
  ArkLib.ProximityGap.Frontier.G331Order32SpectrumFieldCaveat.not_injOn_spectrumVal_65537
