/-
Copyright (c) 2026 Nathan Fox (nathanjfoxwork-bot). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Nathan Fox (nathanjfoxwork-bot)
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G332: the weight-`{1,3}` spectrum is non-injective at `g = 2` in *every* commutative ring

G331 (`Frontier/_G331Order32SpectrumFieldCaveat.lean`, PR #292) recorded the instance
`h = 16` (`n = 32`), `p = 65537`, generator `g = -8`: the KKH26 signed-sum map is not
injective on `spectrumData`, so the counting core `subsetSumSpectrum_card`'s hypothesis
`hinj` is unavailable at that prime.  G330 pinned the order-eight rung's exceptional set
to `{17}`; PR #264 covered the order-sixteen rung; PR #272 / #300 supply per-prime census
side data.

This file shows the `65537` instance was the visible tip of a **ring-uniform** phenomenon,
and is not about `65537`, about `p = 2^16 + 1`, or about small fields at all.

## The mechanism

The literal integer identity

  `1 + 2 - 4 = -1`   (`= 2^0 + 2^1 - 2^2 = -2^0`)

is an identity of signed sums over the three exponents `{0,1,2}`.  Read as a collision of
*signed data* (support `U`, positive part `T ⊆ U`, value `∑_{T} g^i − ∑_{U∖T} g^i`) at
`g = 2`:

* weight `1`, `U = {0}`,      `T = ∅`        gives `-g^0 = -1`;
* weight `3`, `U = {0,1,2}`,  `T = {0,1}`    gives `g^0 + g^1 - g^2 = 1 + 2 - 4 = -1`.

Both data lie in `spectrumData h {1,3}` for every `h ≥ 3`, and the identity holds in any
commutative ring (it is a polynomial identity with integer coefficients, so it transports to
every `CommRing`).  Hence:

  `¬ Set.InjOn (spectrumVal (2 : F)) (spectrumData h ({1,3} : Finset ℕ))`   for every `h ≥ 3`.

No field, no primality, no root of unity, no size hypothesis is used.  When `2` *is* a
primitive `2h`-th root of unity (`ord_p 2 = 2h`, e.g. the Fermat-factor primes below), the map
is literally the KKH26 signed-sum map of `μ_{2h}` and `hinj` is false -- at primes of *any*
size, so this failure cannot be dismissed as a small-field / saturation artifact.

## Consequence for the counting core

`subsetSumSpectrum_card` is conditional on `hinj`.  At a prime with `ord_p 2 = 2h` the
hypothesis is *refuted* at the canonical generator `g = 2`, so the exact law
`∑_{a∈A} 2^a·C(h,a)` is not available there.  The companion probe
`scripts/probes/probe_spectrum_integer_root_family.py` records that the counts are in fact
generator-independent at the tested primes (`h = 16, p = 65537`: `3264`; `h = 32,
p = 6700417`: `34176`; `h = 64, p = 67280421310721`: `310016`, against laws `4512`, `39744`,
`333440`), all with `p ≫ |data|`, i.e. genuine algebraic deficiency rather than saturation.

Honest scope: this is an instance-level no-go for a *counting-core hypothesis*, in the
G328/G330/G331 family.  It is not a `δ*` pin, not a census theorem, not a production claim,
and it does not contradict `sVal_injOn` (which requires `p > 2^80`) -- it says the sharpened
spectrum law is per-prime, never field-uniform.  Cite prior: G331 / PR #292, G330, #264,
#272, #300.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision

open ArkLib.ProximityGap.KKH26

/-! ### The polynomial identity -/

/-- `2^0 + 2^1 - 2^2 = -1`, in any commutative ring.  This is the whole mechanism: three
consecutive exponents of a literal `2` reproduce the negative of the exponent-`0` term. -/
theorem two_spine_identity {F : Type*} [CommRing F] :
    (2 : F) ^ 0 + (2 : F) ^ 1 - (2 : F) ^ 2 = -1 := by
  ring

/-! ### The two colliding data -/

/-- Weight-`1` datum at support `{0}` with empty positive part: value `-g^0`. -/
def dOne : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨1, ⟨{0}, ∅⟩⟩

/-- Weight-`3` datum at support `{0,1,2}` with positive part `{0,1}`: value `g^0+g^1-g^2`. -/
def dThree : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨3, ⟨{0, 1, 2}, {0, 1}⟩⟩

theorem dOne_ne_dThree : dOne ≠ dThree := by
  simp [dOne, dThree]

/-- Membership in the spectrum data: needs `3 ≤ h` so that `{0,1,2} ⊆ range h`. -/
theorem dThree_mem {h : ℕ} (hh : 3 ≤ h) : dThree ∈ spectrumData h ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, dThree]
  refine ⟨by decide, ⟨?_, by decide⟩, by decide⟩
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hi ⊢
  omega

theorem dOne_mem {h : ℕ} (hh : 3 ≤ h) : dOne ∈ spectrumData h ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, dOne]
  refine ⟨by decide, ⟨?_, by decide⟩, by decide⟩
  intro i hi
  simp only [Finset.mem_singleton, Finset.mem_range] at hi ⊢
  omega

/-! ### The collision -/

/-- The weight-`3` value is `g^0 + g^1 - g^2`; at `g = 2` it equals `-1`. -/
theorem sVal_dThree_two {F : Type*} [CommRing F] : sVal (2 : F) dThree.2 = -1 := by
  have h1 : ({0, 1, 2} : Finset ℕ) \ {0, 1} = {2} := by decide
  have h : sVal (2 : F) dThree.2 = (2 : F) ^ 0 + (2 : F) ^ 1 - (2 : F) ^ 2 := by
    simp [dThree, sVal, h1]
  rw [h, two_spine_identity]

theorem sVal_dOne_two {F : Type*} [CommRing F] : sVal (2 : F) dOne.2 = -1 := by
  simp [dOne, sVal]

/-- **The spectrum map is not injective at `g = 2`, in every commutative ring, for every
`h ≥ 3`.**  The colliding data are the weight-`1` datum `({0}, ∅)` and the weight-`3` datum
`({0,1,2}, {0,1})`, whose values agree because `1 + 2 - 4 = -1`.

When `2` is a primitive `2h`-th root of unity in `F` (i.e. `F = ZMod p` with `ord_p 2 = 2h`),
this is exactly the KKH26 counting-core hypothesis `hinj` failing at that prime. -/
theorem not_injOn_spectrumVal_two {F : Type*} [CommRing F] (h : ℕ) (hh : 3 ≤ h) :
    ¬ Set.InjOn (spectrumVal (2 : F)) (spectrumData h ({1, 3} : Finset ℕ)) := by
  intro hinj
  have hmem1 : dOne ∈ spectrumData h ({1, 3} : Finset ℕ) := dOne_mem hh
  have hmem3 : dThree ∈ spectrumData h ({1, 3} : Finset ℕ) := dThree_mem hh
  have heq : spectrumVal (2 : F) dOne = spectrumVal (2 : F) dThree := by
    simp only [spectrumVal, sVal_dOne_two, sVal_dThree_two]
  exact absurd (hinj hmem1 hmem3 heq) dOne_ne_dThree

/-! ### Instances at Fermat-factor primes (`ord_p 2 = 2h`) -/

/-- `p = 65537 = 2^16 + 1` (`F₄`), `h = 16` (`n = 32`): `2` has order `32 = 2h`.  This is the
G331 rung, reached here by the canonical generator `g = 2` instead of `g = -8`. -/
theorem ord_two_65537 : ((2 : ZMod 65537) ^ 16) = -1 := by decide

theorem not_injOn_spectrumVal_65537_h16 :
    ¬ Set.InjOn (spectrumVal (2 : ZMod 65537)) (spectrumData 16 ({1, 3} : Finset ℕ)) :=
  not_injOn_spectrumVal_two 16 (by norm_num)

/-- `p = 6700417 = F₅ / 641`, so `2^32 ≡ -1 (mod p)` and `ord_p 2 = 64`; `h = 32` (`n = 64`).
Note `p / |spectrumData 32 {1,3}| = 6700417 / 39744 ≈ 169`, so the deficiency there is
*algebraic*, not saturation. -/
theorem ord_two_6700417 : ((2 : ZMod 6700417) ^ 32) = -1 := by decide

theorem not_injOn_spectrumVal_6700417_h32 :
    ¬ Set.InjOn (spectrumVal (2 : ZMod 6700417)) (spectrumData 32 ({1, 3} : Finset ℕ)) :=
  not_injOn_spectrumVal_two 32 (by norm_num)

/-- `p = 67280421310721 = F₆ / 274177`, `ord_p 2 = 128`; `h = 64` (`n = 128`). -/
theorem ord_two_F6 : ((2 : ZMod 67280421310721) ^ 64) = -1 := by decide

theorem not_injOn_spectrumVal_F6_h64 :
    ¬ Set.InjOn (spectrumVal (2 : ZMod 67280421310721)) (spectrumData 64 ({1, 3} : Finset ℕ)) :=
  not_injOn_spectrumVal_two 64 (by norm_num)

/-! ### The consequence: the counting-core law is strictly unattained -/

/-- The cardinality of the spectrum data (independent of any injectivity hypothesis). -/
theorem card_spectrumData (h : ℕ) (A : Finset ℕ) :
    (spectrumData h A).card = ∑ a ∈ A, 2 ^ a * h.choose a := by
  rw [spectrumData, Finset.card_sigma]
  exact Finset.sum_congr rfl fun a _ => by rw [card_sigData]

/-- **The KKH26 spectrum law `∑_{a∈A} 2^a·C(h,a)` is not attained at `g = 2`.**  The number of
distinct signed sums is *strictly* less than the law of `subsetSumSpectrum_card`, for every
commutative ring and every `h ≥ 3`.

The companion probe records the exact deficits at the `ord_p 2 = 2h` primes: `4512 → 3264`
(`h=16`, `p=65537`), `39744 → 34176` (`h=32`, `p=6700417`), `333440 → 310016` (`h=64`,
`p=67280421310721`). -/
theorem spectrum_card_lt_law_two {F : Type*} [CommRing F] [DecidableEq F] (h : ℕ) (hh : 3 ≤ h) :
    ((spectrumData h ({1, 3} : Finset ℕ)).image (spectrumVal (2 : F))).card
      < ∑ a ∈ ({1, 3} : Finset ℕ), 2 ^ a * h.choose a := by
  classical
  have hle : ((spectrumData h ({1, 3} : Finset ℕ)).image (spectrumVal (2 : F))).card
      ≤ (spectrumData h ({1, 3} : Finset ℕ)).card := Finset.card_image_le
  rw [card_spectrumData] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · have hinj : Set.InjOn (spectrumVal (2 : F)) (spectrumData h ({1, 3} : Finset ℕ)) :=
      (Finset.card_image_iff).1 (heq.trans (card_spectrumData h {1, 3}).symm)
    exact absurd hinj (not_injOn_spectrumVal_two h hh)

end ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.two_spine_identity
#print axioms
  ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.not_injOn_spectrumVal_two
#print axioms
  ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.not_injOn_spectrumVal_65537_h16
#print axioms
  ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.not_injOn_spectrumVal_6700417_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.not_injOn_spectrumVal_F6_h64
#print axioms
  ArkLib.ProximityGap.Frontier.G332SpectrumIntegerRootCollision.spectrum_card_lt_law_two
