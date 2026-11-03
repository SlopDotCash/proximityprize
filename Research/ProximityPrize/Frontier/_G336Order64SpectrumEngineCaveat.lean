/-
Copyright (c) 2026 Nathan Fox (nathanjfoxwork-bot). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Nathan Fox (nathanjfoxwork-bot)
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G336: n = 64 weight-`{1,3}` spectrum engine caveats beyond `p = 65537`

G333 (PR #319 companion / open #336's sibling lane) recorded that at `h = 32`
(`n = 64`), `p = 65537`, the KKH26 signed-sum map is not injective (13761 values
against the law 39744), via the collision `g^3 - g^6 + g^16 = 1` at `g = 8224`.
G334 (PR #321) packaged the reusable engine

  `2 · g^0 = g^a + g^b`    with `0 < a < b < h`

at the n = 32 rung for four non-Fermat primes.

This file lifts that engine one rung: **which other primes make the n = 64 rung
fail, and by the same `2 = g^a + g^b` mechanism?**  Hypothesis discharge is one
`decide`d arithmetic statement per prime; the non-injectivity conclusion is then
free.  In particular the engine fires at primes other than `65537`, so G333's
instance is sufficient but not necessary.

## Instances at n = 64 (`h = 32`, `|data| = 39744`)

| p       | distinct | deficiency | generator | witness           |
|---------|----------|------------|-----------|-------------------|
| 50177   | 25280    | 14464      | 10433     | `g^6  + g^8  = 2` |
| 51137   | 26304    | 13440      | 6269      | `g^2  + g^14 = 2` |
| 78017   | 29632    | 10112      | 27489     | `g^2  + g^29 = 2` |
| 97729   | 30720    | 9024       | 11143     | `g^8  + g^9  = 2` |

(Companion probe: `scripts/probes/probe_order64_engine_caveats.py`.  At each of
these primes `p > 39744`, so the deficiency is genuine, not saturation.  G333's
prize-scale Proth control `21·2^128+1` remains the injective contrast at this
rung.)

Named prize claim advanced: `ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(`ArkLib/Data/CodingTheory/ProximityGap/TwoPowerSubsetSumSpectrum.lean`).  Its
hypothesis `hinj` is unavailable at each of the four primes above.

Honest scope:
* Closes off four more field choices for future n = 64 spectrum / MCA pins, and
  reuses the G334 engine so further instances are one-line.
* Does **not** contradict any in-tree theorem: `sVal_injOn` requires `p > 2^80`;
  `subsetSumSpectrum_card` stays true (conditional on `hinj`).
* Not a δ\* pin, not a field-uniform census theorem, no production claim.
* Does not restate G333's `65537` instance (different mechanism / already open).
* Open PRs #300 / #328 print per-prime census side data via a monomial-pencil
  route; what is new here is the injectivity reading, the Lean engine at h = 32,
  and the four certificates.
* Distinct from Nathan open #319 / #321 / #292 / #336 (those are n = 32 caveats,
  the 65537 n = 64 instance, or generator-negation symmetry).
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat

open ArkLib.ProximityGap.KKH26

set_option maxRecDepth 100000

/-! ### Reusable engine: `2 · g^0` as a sum of two roots (same as G334) -/

/-- Weight-`1` datum with positive part `{0}`: value `+g^0`. -/
def dOnePos : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨1, ⟨{0}, {0}⟩⟩

/-- Weight-`3` datum at support `{0,a,b}` with positive part `{a,b}`. -/
def dTwo (a b : ℕ) : (_ : ℕ) × ((_ : Finset ℕ) × Finset ℕ) := ⟨3, ⟨{0, a, b}, {a, b}⟩⟩

theorem sVal_dOnePos {F : Type*} [CommRing F] (g : F) : sVal g dOnePos.2 = g ^ 0 := by
  simp [dOnePos, sVal]

theorem dOnePos_mem {h : ℕ} (hh : 1 ≤ h) : dOnePos ∈ spectrumData h ({1, 3} : Finset ℕ) := by
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, dOnePos]
  refine ⟨by decide, ⟨?_, by decide⟩, by decide⟩
  intro i hi
  simp only [Finset.mem_singleton, Finset.mem_range] at hi ⊢
  omega

theorem dTwo_mem {h a b : ℕ} (ha : 0 < a) (hab : a < b) (hb : b < h) :
    dTwo a b ∈ spectrumData h ({1, 3} : Finset ℕ) := by
  have h0a : (0 : ℕ) ≠ a := by omega
  have h0b : (0 : ℕ) ≠ b := by omega
  simp only [spectrumData, Finset.mem_sigma, mem_sigData, dTwo]
  refine ⟨by decide, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hi ⊢
    omega
  · simp [h0a, h0b, hab.ne]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    omega

theorem dTwo_sVal {F : Type*} [CommRing F] (g : F) (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    sVal g (dTwo a b).2 = g ^ a + g ^ b - g ^ 0 := by
  have h0a : (0 : ℕ) ≠ a := by omega
  have h0b : (0 : ℕ) ≠ b := by omega
  simp [dTwo, sVal, h0a, h0b, hab.ne]

/-- **Collision engine.**  If `2 · g^0 = g^a + g^b` with `0 < a < b < h`, then the weight-`1`
datum `({0},{0})` and the weight-`3` datum `({0,a,b},{a,b})` have the same value `g^0`, so the
KKH26 signed-sum map is not injective at `g`. -/
theorem not_injOn_of_two_eq_sum {F : Type*} [CommRing F] (g : F) (h a b : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < h) (hsum : g ^ a + g ^ b = 2 * g ^ 0) :
    ¬ Set.InjOn (spectrumVal g) (spectrumData h ({1, 3} : Finset ℕ)) := by
  intro hinj
  have h1 : dOnePos ∈ spectrumData h ({1, 3} : Finset ℕ) := dOnePos_mem (by omega)
  have h2 : dTwo a b ∈ spectrumData h ({1, 3} : Finset ℕ) := dTwo_mem ha hab hb
  have hv : spectrumVal g dOnePos = spectrumVal g (dTwo a b) := by
    simp only [spectrumVal, sVal_dOnePos, dTwo_sVal g a b ha hab]
    rw [hsum]; ring
  have : dOnePos = dTwo a b := hinj h1 h2 hv
  simp [dOnePos, dTwo] at this

/-! ### Instance: `p = 50177` -/

theorem engine_50177 :
    (10433 : ZMod 50177) ^ 6 + (10433 : ZMod 50177) ^ 8
      = 2 * (10433 : ZMod 50177) ^ 0 := by
  decide

theorem ord_10433_50177 : ((10433 : ZMod 50177) ^ 32) = -1 := by decide

theorem not_injOn_spectrumVal_50177_h32 :
    ¬ Set.InjOn (spectrumVal (10433 : ZMod 50177))
        (spectrumData 32 ({1, 3} : Finset ℕ)) :=
  not_injOn_of_two_eq_sum _ 32 6 8 (by norm_num) (by norm_num) (by norm_num) engine_50177

/-! ### Instance: `p = 51137` -/

theorem engine_51137 :
    (6269 : ZMod 51137) ^ 2 + (6269 : ZMod 51137) ^ 14
      = 2 * (6269 : ZMod 51137) ^ 0 := by
  decide

theorem ord_6269_51137 : ((6269 : ZMod 51137) ^ 32) = -1 := by decide

theorem not_injOn_spectrumVal_51137_h32 :
    ¬ Set.InjOn (spectrumVal (6269 : ZMod 51137))
        (spectrumData 32 ({1, 3} : Finset ℕ)) :=
  not_injOn_of_two_eq_sum _ 32 2 14 (by norm_num) (by norm_num) (by norm_num) engine_51137

/-! ### Instance: `p = 78017` -/

theorem engine_78017 :
    (27489 : ZMod 78017) ^ 2 + (27489 : ZMod 78017) ^ 29
      = 2 * (27489 : ZMod 78017) ^ 0 := by
  decide

theorem ord_27489_78017 : ((27489 : ZMod 78017) ^ 32) = -1 := by decide

theorem not_injOn_spectrumVal_78017_h32 :
    ¬ Set.InjOn (spectrumVal (27489 : ZMod 78017))
        (spectrumData 32 ({1, 3} : Finset ℕ)) :=
  not_injOn_of_two_eq_sum _ 32 2 29 (by norm_num) (by norm_num) (by norm_num) engine_78017

/-! ### Instance: `p = 97729` -/

theorem engine_97729 :
    (11143 : ZMod 97729) ^ 8 + (11143 : ZMod 97729) ^ 9
      = 2 * (11143 : ZMod 97729) ^ 0 := by
  decide

theorem ord_11143_97729 : ((11143 : ZMod 97729) ^ 32) = -1 := by decide

theorem not_injOn_spectrumVal_97729_h32 :
    ¬ Set.InjOn (spectrumVal (11143 : ZMod 97729))
        (spectrumData 32 ({1, 3} : Finset ℕ)) :=
  not_injOn_of_two_eq_sum _ 32 8 9 (by norm_num) (by norm_num) (by norm_num) engine_97729

end ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_of_two_eq_sum
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_50177_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_51137_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_78017_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_97729_h32
