/-
Copyright (c) 2026 Nathan Fox (nathanjfoxwork-bot). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Nathan Fox (nathanjfoxwork-bot)
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G333: the order-64 weight-{1,3} spectrum is not injective at `p = 65537`

G328 / G330 pinned the order-eight exceptional set to `{17}`.  PR #264 recorded the
order-16 rung (464 values outside a 34-prime set; injective at `p = 65537`).  PR #292
(G331) recorded the order-32 rung: at `p = 65537` the map is *not* injective
(3264 values against the law 4512).

Companion to G332 (ring-uniform `g=2` collision). This file records the instance rung, `h = 32` (`n = 64`, `|data| = 39744`): at `p = 65537`
the map is again not injective.  The deficiency is genuine, not saturation, since
`65537 > 39744`.  Mechanism: `65537 = 2^16 + 1`, so an element of exact order 64 exists;
with `g = 8224` the identity `g^3 - g^6 + g^16 = 1` (= `g^0`) collides a weight-1 datum
with a weight-3 datum.

Named prize claim advanced: `ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(`ArkLib/Data/CodingTheory/ProximityGap/TwoPowerSubsetSumSpectrum.lean`).  Its hypothesis
`hinj : Set.InjOn (spectrumVal g) (spectrumData h A)` is the KKH26 counting core.  At this
instance `hinj` is false, so the spectrum law `39744` is not available at `p = 65537`.

Companion executable census: `scripts/probes/probe_order64_weight13_spectrum.py`
(reproduces 13761 values at `p = 65537`, and 39744 at the prize-scale Proth prime
`21·2^128+1`).

Honest scope:
* Closes off a field choice for future n = 64 spectrum / MCA pins.  Together with G331,
  `65537` is inadmissible at both the n = 32 and n = 64 rungs (small-field discipline,
  cf. SYZ53 / G84 / G328).
* Does **not** contradict any in-tree theorem: `sVal_injOn` requires `p > 2^80` and is
  unaffected; `subsetSumSpectrum_card` stays true (it is conditional on `hinj`).
* Not a δ\* pin, not a field-uniform census theorem, no production claim.
* Open PR #300 already prints `13761` / `39744` as side data via a different route
  (monomial-pencil MCA census).  What is new here is the injectivity reading against
  `subsetSumSpectrum_card`, the Lean certificate, and the `g = 8224` collision mechanism.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat

open ArkLib.ProximityGap.KKH26

set_option maxRecDepth 100000

/-- `g = 8224` is a 64th root of unity in `ZMod 65537`. -/
def g64 : ZMod 65537 := 8224

theorem g64_pow32 : g64 ^ 32 = -1 := by
  unfold g64; decide

theorem g64_pow64 : g64 ^ 64 = 1 := by
  unfold g64; decide

/-- The collision identity: `g^3 - g^6 + g^16 = 1` (= `g^0`). -/
theorem collision_identity : g64 ^ 3 - g64 ^ 6 + g64 ^ 16 = 1 := by
  unfold g64; decide

/-- Weight-1 datum: support `{0}`, positive part `{0}`, value `g^0 = 1`. -/
def d1 : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨1, ⟨{0}, {0}⟩⟩

/-- Weight-3 datum: support `{3,6,16}`, positive part `{3,16}`, value `g^3+g^16-g^6`. -/
def d2 : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨3, ⟨{3, 6, 16}, {3, 16}⟩⟩

lemma sVal_d1 : sVal g64 d1.2 = g64 ^ 0 := by
  simp [d1, sVal]

lemma sVal_d2 : sVal g64 d2.2 = g64 ^ 3 + g64 ^ 16 - g64 ^ 6 := by
  have h1 : ({3, 6, 16} : Finset ℕ) \ {3, 16} = {6} := by decide
  have h : sVal g64 d2.2 = g64 ^ 3 + g64 ^ 16 - g64 ^ 6 := by
    simp [d2, sVal, h1]
  exact h

/-- The two data have the same signed-sum value in `ZMod 65537`. -/
theorem collision_sVal : sVal g64 d1.2 = sVal g64 d2.2 := by
  rw [sVal_d1, sVal_d2, pow_zero]
  calc
    (1 : ZMod 65537) = g64 ^ 3 - g64 ^ 6 + g64 ^ 16 := collision_identity.symm
    _ = g64 ^ 3 + g64 ^ 16 - g64 ^ 6 := by ring

/-- `spectrumVal` agrees at the two data: the weight tag is forgotten. -/
theorem collision_spectrumVal : spectrumVal g64 d1 = spectrumVal g64 d2 :=
  collision_sVal

theorem d1_mem : d1 ∈ spectrumData 32 ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, d1]
  refine ⟨by decide, ⟨?_, by decide⟩, by decide⟩
  intro i hi
  simp only [Finset.mem_singleton, Finset.mem_range] at hi ⊢
  omega

theorem d2_mem : d2 ∈ spectrumData 32 ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, d2]
  refine ⟨by decide, ⟨?_, by decide⟩, by decide⟩
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hi ⊢
  omega

theorem d1_ne_d2 : d1 ≠ d2 := by
  simp [d1, d2]

/-- **The n = 64 weight-`{1,3}` spectrum is not injective at `p = 65537`.**

This is the instance-level failure of `hinj` in `KKH26.subsetSumSpectrum_card` at the
campaign's favourite large stand-in field, one rung above G331. -/
theorem not_injOn_spectrumVal_65537 :
    ¬ Set.InjOn (spectrumVal g64) (spectrumData 32 ({1, 3} : Finset ℕ)) := by
  intro hinj
  exact d1_ne_d2 (hinj d1_mem d2_mem collision_spectrumVal)

end ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat.g64_pow64
#print axioms
  ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat.collision_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat.collision_spectrumVal
#print axioms
  ArkLib.ProximityGap.Frontier.G333Order64SpectrumFieldCaveat.not_injOn_spectrumVal_65537
