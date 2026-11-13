/-
Copyright (c) 2026 Nathan Fox (nathanjfoxwork-bot). All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Nathan Fox (nathanjfoxwork-bot)
-/
import ArkLib.Research.ProximityGap.Frontier._G334Order32SpectrumEngineCaveat

/-!
# G336: n = 64 weight-`{1,3}` spectrum engine caveats beyond `p = 65537`

G333 (PR #319) recorded that at `h = 32`
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

The companion probe `scripts/probes/probe_order64_engine_caveats.py` enumerates
the distinct-value counts in the table. At each of these primes `p > 39744`, so
the deficiency cannot come from saturation. The G333 probe reports a full image
for its tested generator at the prize-scale Proth control `21·2^128+1`.

Named prize claim advanced: `ArkLib.ProximityGap.KKH26.subsetSumSpectrum_card`
(`ArkLib/Data/CodingTheory/ProximityGap/TwoPowerSubsetSumSpectrum.lean`).  Its
hypothesis `hinj` fails at the four displayed generators.

Honest scope:
* The four order-64 certificates instantiate G334's ring-generic collision
  lemma. Each concerns a specified generator and a distinct prime-field test.
* `sVal_injOn` requires `p > 2^80`, and `subsetSumSpectrum_card` assumes `hinj`.
* These collision certificates leave the field-uniform census and production
  δ\* question open. The monomial-pencil probes in #300 and #328 provide
  separate per-prime census data.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat

open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.G334Order32SpectrumEngineCaveat (not_injOn_of_two_eq_sum)

set_option maxRecDepth 100000

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
  ArkLib.ProximityGap.Frontier.G334Order32SpectrumEngineCaveat.not_injOn_of_two_eq_sum
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_50177_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_51137_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_78017_h32
#print axioms
  ArkLib.ProximityGap.Frontier.G336Order64SpectrumEngineCaveat.not_injOn_spectrumVal_97729_h32
