/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.Tactic.NormNum.Prime

/-!
# B3 — a concrete discharge of `TZPrimeSupply` (#334)

`ThornerZamanS128.lean` flags the single analytic hypothesis `TZPrimeSupply n β supply`
(`KKH26ThornerZaman.lean`) — the window `[n^β, 2·n^β]` contains `≥ supply` primes
`p ≡ 1 (mod n)` — and its plan **(ii)** invites a concrete instance via explicit primes
(a finite check; no `native_decide`).  This file does exactly that for `n = 16`, `β = 2`:

> **`tzPrimeSupply_16_two`** — `TZPrimeSupply 16 2 6`, witnessed by the six explicit primes
> `{257, 337, 353, 401, 433, 449} ≡ 1 (mod 16)` in the window `[256, 512]`.

This is an honest, axiom-clean discharge of the named hypothesis for a concrete smooth modulus —
the route that the `kkh26_mcaDeltaStar_le_of_TZ` consumer needs, demonstrated end-to-end on a real
instance (the asymptotic `n^{β−1−o(1)}` supply is the [TZ24] analytic statement that remains
the open input for general `n`).
-/

namespace ArkLib.ProximityGap.KKH26

/-- **Concrete discharge of `TZPrimeSupply` for `n = 16, β = 2`.**  The window `[16², 2·16²] =
[256, 512]` contains the six primes `257, 337, 353, 401, 433, 449`, all `≡ 1 (mod 16)`. -/
theorem tzPrimeSupply_16_two : TZPrimeSupply 16 (2 : ℝ) 6 := by
  refine ⟨?_⟩
  have hpow : ((16 : ℕ) : ℝ) ^ (2 : ℝ) = 256 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({257, 337, 353, 401, 433, 449} : Finset ℕ) ⊆ tzWindow 16 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (6 : ℕ) = ({257, 337, 353, 401, 433, 449} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 16 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 8, β = 2`.**  The window `[64, 128]` contains the four primes
`73, 89, 97, 113`, all `≡ 1 (mod 8)`. -/
theorem tzPrimeSupply_8_two : TZPrimeSupply 8 (2 : ℝ) 4 := by
  refine ⟨?_⟩
  have hpow : ((8 : ℕ) : ℝ) ^ (2 : ℝ) = 64 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({73, 89, 97, 113} : Finset ℕ) ⊆ tzWindow 8 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (4 : ℕ) = ({73, 89, 97, 113} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 32, β = 2`.**  The window `[1024, 2048]` contains the six primes
`1153, 1217, 1249, 1409, 1601, 1697`, all `≡ 1 (mod 32)`.  (The supply grows `4, 6, 6` across
`n = 8, 16, 32` — the `n^{β−1}`-type growth of the [TZ24] window.) -/
theorem tzPrimeSupply_32_two : TZPrimeSupply 32 (2 : ℝ) 6 := by
  refine ⟨?_⟩
  have hpow : ((32 : ℕ) : ℝ) ^ (2 : ℝ) = 1024 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({1153, 1217, 1249, 1409, 1601, 1697} : Finset ℕ) ⊆ tzWindow 32 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (6 : ℕ) = ({1153, 1217, 1249, 1409, 1601, 1697} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 32 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 64, β = 2`.**  The window `[4096, 8192]` contains the
eight primes `4289, 4481, 4673, 4801, 4993, 5441, 5569, 5953`, all `≡ 1 (mod 64)`. -/
theorem tzPrimeSupply_64_two : TZPrimeSupply 64 (2 : ℝ) 8 := by
  refine ⟨?_⟩
  have hpow : ((64 : ℕ) : ℝ) ^ (2 : ℝ) = 4096 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({4289, 4481, 4673, 4801, 4993, 5441, 5569, 5953} : Finset ℕ)
      ⊆ tzWindow 64 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (8 : ℕ)
      = ({4289, 4481, 4673, 4801, 4993, 5441, 5569, 5953} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 64 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 8, β = 3`** — in the faithful unconditional regime `β > 12/5`
of [TZ24].  The window `[512, 1024]` contains the eight primes `521, 569, 577, 593, 601, 617, 641,
673`, all `≡ 1 (mod 8)`. -/
theorem tzPrimeSupply_8_three : TZPrimeSupply 8 (3 : ℝ) 8 := by
  refine ⟨?_⟩
  have hpow : ((8 : ℕ) : ℝ) ^ (3 : ℝ) = 512 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({521, 569, 577, 593, 601, 617, 641, 673} : Finset ℕ) ⊆ tzWindow 8 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (8 : ℕ)
      = ({521, 569, 577, 593, 601, 617, 641, 673} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 128, β = 2`.**  The window `[128², 2·128²] = [16384, 32768]`
contains the ten primes `17921, 18049, 18433, 19073, 19457, 19841, 20353, 21121, 21377, 22273`, all
`≡ 1 (mod 128)`.  (The supply ladder is now `4, 6, 6, 8, 10` across
`n = 8, 16, 32, 64, 128` — the `n^{β−1}`-type growth of the [TZ24] window, extending the
concrete ceiling toward larger `s`.) -/
theorem tzPrimeSupply_128_two : TZPrimeSupply 128 (2 : ℝ) 10 := by
  refine ⟨?_⟩
  have hpow : ((128 : ℕ) : ℝ) ^ (2 : ℝ) = 16384 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({17921, 18049, 18433, 19073, 19457, 19841, 20353, 21121, 21377, 22273} : Finset ℕ)
      ⊆ tzWindow 128 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (10 : ℕ)
      = ({17921, 18049, 18433, 19073, 19457, 19841, 20353, 21121, 21377, 22273} :
        Finset ℕ).card := by decide
    _ ≤ (tzWindow 128 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 256, β = 2`.**  The window `[256², 2·256²] = [65536, 131072]`
contains the ten primes `65537, 67073, 70657, 70913, 75521, 76289, 76801, 77569, 78593, 79873`, all
`≡ 1 (mod 256)`.  Supply ladder `4, 6, 6, 8, 10, 10` across `n = 8, 16, 32, 64, 128, 256`. -/
theorem tzPrimeSupply_256_two : TZPrimeSupply 256 (2 : ℝ) 10 := by
  refine ⟨?_⟩
  have hpow : ((256 : ℕ) : ℝ) ^ (2 : ℝ) = 65536 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({65537, 67073, 70657, 70913, 75521, 76289, 76801, 77569, 78593, 79873} : Finset ℕ)
      ⊆ tzWindow 256 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (10 : ℕ)
      = ({65537, 67073, 70657, 70913, 75521, 76289, 76801, 77569, 78593, 79873} :
        Finset ℕ).card := by decide
    _ ≤ (tzWindow 256 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 512, β = 2`.**  The window `[512², 2·512²] =
`[262144, 524288]` contains the twenty primes listed below, all `≡ 1 (mod 512)`.  This extends
the explicit β=2 supply ladder to the same smooth-domain rung as the concrete width-four
refuter `ZMod 262657`. -/
theorem tzPrimeSupply_512_two : TZPrimeSupply 512 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((512 : ℕ) : ℝ) ^ (2 : ℝ) = 262144 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({262657, 265729, 270337, 275969, 278017, 279553, 284161, 285697, 286721, 287233,
          288257, 295937, 299521, 301057, 302593, 303617, 306689, 307201, 310273, 319489} :
          Finset ℕ) ⊆ tzWindow 512 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({262657, 265729, 270337, 275969, 278017, 279553, 284161, 285697, 286721, 287233,
          288257, 295937, 299521, 301057, 302593, 303617, 306689, 307201, 310273, 319489} :
          Finset ℕ).card := by decide
    _ ≤ (tzWindow 512 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 1024, β = 2`.**  The window `[1024², 2·1024²] =
`[1048576, 2097152]` contains the twenty primes listed below, all `≡ 1 (mod 1024)`.  This keeps
the explicit β=2 supply ladder aligned with the `n = 1024` concrete width-four refuter. -/
theorem tzPrimeSupply_1024_two : TZPrimeSupply 1024 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((1024 : ℕ) : ℝ) ^ (2 : ℝ) = 1048576 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({1051649, 1053697, 1054721, 1062913, 1067009, 1070081, 1072129, 1073153, 1075201,
          1079297, 1082369, 1093633, 1094657, 1097729, 1103873, 1108993, 1113089, 1124353,
          1130497, 1139713} : Finset ℕ) ⊆ tzWindow 1024 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({1051649, 1053697, 1054721, 1062913, 1067009, 1070081, 1072129, 1073153, 1075201,
          1079297, 1082369, 1093633, 1094657, 1097729, 1103873, 1108993, 1113089, 1124353,
          1130497, 1139713} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 1024 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 2048, β = 2`.**  The window `[2048², 2·2048²] =
`[4194304, 8388608]` contains the twenty primes listed below, all `≡ 1 (mod 2048)`.  This extends
the explicit β=2 supply ladder to the same rung as the concrete `ZMod 4206593` width-four
refuter. -/
theorem tzPrimeSupply_2048_two : TZPrimeSupply 2048 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((2048 : ℕ) : ℝ) ^ (2 : ℝ) = 4194304 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({4206593, 4208641, 4263937, 4270081, 4274177, 4294657, 4300801, 4304897, 4319233,
          4323329, 4360193, 4366337, 4384769, 4417537, 4421633, 4423681, 4427777, 4435969,
          4452353, 4458497} : Finset ℕ) ⊆ tzWindow 2048 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({4206593, 4208641, 4263937, 4270081, 4274177, 4294657, 4300801, 4304897, 4319233,
          4323329, 4360193, 4366337, 4384769, 4417537, 4421633, 4423681, 4427777, 4435969,
          4452353, 4458497} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 2048 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 4096, β = 2`.**  The window `[4096², 2·4096²] =
`[16777216, 33554432]` contains the twenty primes listed below, all `≡ 1 (mod 4096)`. -/
theorem tzPrimeSupply_4096_two : TZPrimeSupply 4096 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((4096 : ℕ) : ℝ) ^ (2 : ℝ) = 16777216 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({16801793, 16863233, 16900097, 16957441, 16986113, 17006593, 17010689, 17059841,
          17129473, 17182721, 17231873, 17252353, 17264641, 17276929, 17367041, 17375233,
          17391617, 17416193, 17440769, 17448961} : Finset ℕ) ⊆ tzWindow 4096 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({16801793, 16863233, 16900097, 16957441, 16986113, 17006593, 17010689, 17059841,
          17129473, 17182721, 17231873, 17252353, 17264641, 17276929, 17367041, 17375233,
          17391617, 17416193, 17440769, 17448961} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 4096 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 8192, β = 2`.**  The window `[8192², 2·8192²] =
`[67108864, 134217728]` contains the twenty primes listed below, all `≡ 1 (mod 8192)`. -/
theorem tzPrimeSupply_8192_two : TZPrimeSupply 8192 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((8192 : ℕ) : ℝ) ^ (2 : ℝ) = 67108864 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({67239937, 67280897, 67411969, 67452929, 67502081, 67510273, 67584001, 67649537,
          67657729, 67731457, 67903489, 68018177, 68190209, 68362241, 68485121, 68558849,
          68567041, 68640769, 68681729, 68853761} : Finset ℕ) ⊆ tzWindow 8192 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({67239937, 67280897, 67411969, 67452929, 67502081, 67510273, 67584001, 67649537,
          67657729, 67731457, 67903489, 68018177, 68190209, 68362241, 68485121, 68558849,
          68567041, 68640769, 68681729, 68853761} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8192 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 16384, β = 2`.**  The window `[16384², 2·16384²] =
`[268435456, 536870912]` contains the twenty primes listed below, all `≡ 1 (mod 16384)`. -/
theorem tzPrimeSupply_16384_two : TZPrimeSupply 16384 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((16384 : ℕ) : ℝ) ^ (2 : ℝ) = 268435456 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({268582913, 268664833, 268730369, 268779521, 268861441, 269221889, 269402113,
          269844481, 269991937, 270237697, 270450689, 270499841, 270532609, 270581761,
          270794753, 271286273, 271532033, 271564801, 271728641, 271761409} : Finset ℕ)
        ⊆ tzWindow 16384 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({268582913, 268664833, 268730369, 268779521, 268861441, 269221889, 269402113,
          269844481, 269991937, 270237697, 270450689, 270499841, 270532609, 270581761,
          270794753, 271286273, 271532033, 271564801, 271728641, 271761409} : Finset ℕ).card :=
        by decide
    _ ≤ (tzWindow 16384 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 32768, β = 2`.**  The window `[32768², 2·32768²] =
`[1073741824, 2147483648]` contains the twenty primes listed below, all `≡ 1 (mod 32768)`. -/
theorem tzPrimeSupply_32768_two : TZPrimeSupply 32768 (2 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((32768 : ℕ) : ℝ) ^ (2 : ℝ) = 1073741824 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({1073872897, 1073971201, 1074266113, 1074429953, 1075937281, 1076002817,
          1076789249, 1076920321, 1077477377, 1077706753, 1077903361, 1077968897,
          1078296577, 1079443457, 1079672833, 1080360961, 1081212929, 1081507841,
          1081638913, 1082982401} : Finset ℕ) ⊆ tzWindow 32768 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({1073872897, 1073971201, 1074266113, 1074429953, 1075937281, 1076002817,
          1076789249, 1076920321, 1077477377, 1077706753, 1077903361, 1077968897,
          1078296577, 1079443457, 1079672833, 1080360961, 1081212929, 1081507841,
          1081638913, 1082982401} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 32768 (2 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 16, β = 3`** — in the faithful unconditional regime
`β > 12/5` of [TZ24].  The window `[16³, 2·16³] = [4096, 8192]` contains the ten primes
`4129, 4177, 4241, 4273, 4289, 4337, 4481, 4513, 4561, 4657`, all `≡ 1 (mod 16)`. -/
theorem tzPrimeSupply_16_three : TZPrimeSupply 16 (3 : ℝ) 10 := by
  refine ⟨?_⟩
  have hpow : ((16 : ℕ) : ℝ) ^ (3 : ℝ) = 4096 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({4129, 4177, 4241, 4273, 4289, 4337, 4481, 4513, 4561, 4657} : Finset ℕ)
      ⊆ tzWindow 16 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (10 : ℕ)
      = ({4129, 4177, 4241, 4273, 4289, 4337, 4481, 4513, 4561, 4657} :
        Finset ℕ).card := by decide
    _ ≤ (tzWindow 16 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 32, β = 3`** — another faithful `β > 12/5` row.  The window
`[32³, 2·32³] = [32768, 65536]` contains the twelve primes `32801, 32833, 32993, 33377, 33409,
33569, 33601, 33857, 33889, 34273, 34337, 34369`, all `≡ 1 (mod 32)`. -/
theorem tzPrimeSupply_32_three : TZPrimeSupply 32 (3 : ℝ) 12 := by
  refine ⟨?_⟩
  have hpow : ((32 : ℕ) : ℝ) ^ (3 : ℝ) = 32768 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({32801, 32833, 32993, 33377, 33409, 33569, 33601, 33857, 33889, 34273, 34337, 34369} :
          Finset ℕ) ⊆ tzWindow 32 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (12 : ℕ)
      = ({32801, 32833, 32993, 33377, 33409, 33569, 33601, 33857, 33889, 34273, 34337, 34369} :
          Finset ℕ).card := by decide
    _ ≤ (tzWindow 32 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 64, β = 3`.**  The window `[64³, 2·64³] =
`[262144, 524288]` contains the twenty primes listed below, all `≡ 1 (mod 64)`.  This extends
the faithful `β > 12/5` concrete ladder one smooth-domain rung past the `n = 32` row used by the
current canonical finite-exception bridge. -/
theorem tzPrimeSupply_64_three : TZPrimeSupply 64 (3 : ℝ) 20 := by
  refine ⟨?_⟩
  have hpow : ((64 : ℕ) : ℝ) ^ (3 : ℝ) = 262144 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({262337, 262657, 263489, 264577, 264769, 264961, 265729, 265921, 266177, 266369,
          266689, 267521, 267649, 267713, 268993, 269057, 269377, 269441, 269761, 269953} :
          Finset ℕ) ⊆ tzWindow 64 (3 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (20 : ℕ)
      = ({262337, 262657, 263489, 264577, 264769, 264961, 265729, 265921, 266177, 266369,
          266689, 267521, 267649, 267713, 268993, 269057, 269377, 269441, 269761, 269953} :
          Finset ℕ).card := by decide
    _ ≤ (tzWindow 64 (3 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 8, β = 4`** — deep in the faithful unconditional regime
`β > 12/5` of [TZ24] (the highest exponent in the concrete ladder).  The window
`[8⁴, 2·8⁴] = [4096, 8192]` contains the eight primes
`4129, 4153, 4177, 4201, 4217, 4241, 4273, 4289`, all `≡ 1 (mod 8)`. -/
theorem tzPrimeSupply_8_four : TZPrimeSupply 8 (4 : ℝ) 8 := by
  refine ⟨?_⟩
  have hpow : ((8 : ℕ) : ℝ) ^ (4 : ℝ) = 4096 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({4129, 4153, 4177, 4201, 4217, 4241, 4273, 4289} : Finset ℕ)
      ⊆ tzWindow 8 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (8 : ℕ)
      = ({4129, 4153, 4177, 4201, 4217, 4241, 4273, 4289} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8 (4 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 16, β = 4`** — the highest `(n, β)` in the concrete ladder.
The window `[16⁴, 2·16⁴] = [65536, 131072]` contains the ten primes
`65537, 65617, 65633, 65713, 65729, 65761, 65777, 65809, 65921, 66161`, all
`≡ 1 (mod 16)`.  (Demonstrates the concrete `TZPrimeSupply` route scales to `β = 4`, well
above [TZ24]'s `β > 12/5` faithfulness threshold; the asymptotic supply for general `n`
remains the open [TZ24] analytic input.) -/
theorem tzPrimeSupply_16_four : TZPrimeSupply 16 (4 : ℝ) 10 := by
  refine ⟨?_⟩
  have hpow : ((16 : ℕ) : ℝ) ^ (4 : ℝ) = 65536 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({65537, 65617, 65633, 65713, 65729, 65761, 65777, 65809, 65921, 66161} : Finset ℕ)
      ⊆ tzWindow 16 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (10 : ℕ)
      = ({65537, 65617, 65633, 65713, 65729, 65761, 65777, 65809, 65921, 66161} :
        Finset ℕ).card := by decide
    _ ≤ (tzWindow 16 (4 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 32, β = 4`.**  The window
`[32⁴, 2·32⁴] = [1048576, 2097152]` contains the sixteen primes
`1048609, 1048897, 1049057, 1049089,
1049281, 1049473, 1049537, 1049569, 1049857, 1049953, 1050241, 1050337, 1050593, 1050817,
1050913, 1050977`, all `≡ 1 (mod 32)`.  This extends the concrete high-exponent
Thorner-Zaman supply ladder beyond the `n = 16` β=4 row. -/
theorem tzPrimeSupply_32_four : TZPrimeSupply 32 (4 : ℝ) 16 := by
  refine ⟨?_⟩
  have hpow : ((32 : ℕ) : ℝ) ^ (4 : ℝ) = 1048576 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({1048609, 1048897, 1049057, 1049089, 1049281, 1049473, 1049537, 1049569,
          1049857, 1049953, 1050241, 1050337, 1050593, 1050817, 1050913, 1050977} :
          Finset ℕ) ⊆ tzWindow 32 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (16 : ℕ)
      = ({1048609, 1048897, 1049057, 1049089, 1049281, 1049473, 1049537, 1049569,
          1049857, 1049953, 1050241, 1050337, 1050593, 1050817, 1050913, 1050977} :
          Finset ℕ).card := by decide
    _ ≤ (tzWindow 32 (4 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 64, β = 4`.**  The window
`[64⁴, 2·64⁴] = [16777216, 33554432]` contains the sixteen primes listed below, all
`≡ 1 (mod 64)`.  This pushes the concrete high-exponent TZ ladder beyond the current exact
`n = 32` finite-exception row. -/
theorem tzPrimeSupply_64_four : TZPrimeSupply 64 (4 : ℝ) 16 := by
  refine ⟨?_⟩
  have hpow : ((64 : ℕ) : ℝ) ^ (4 : ℝ) = 16777216 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub :
      ({16777601, 16777729, 16778497, 16778561, 16778689, 16779713, 16780289, 16780417,
          16780609, 16780801, 16781441, 16781953, 16782209, 16782401, 16783873, 16784513} :
          Finset ℕ) ⊆ tzWindow 64 (4 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (16 : ℕ)
      = ({16777601, 16777729, 16778497, 16778561, 16778689, 16779713, 16780289, 16780417,
          16780609, 16780801, 16781441, 16781953, 16782209, 16782401, 16783873, 16784513} :
          Finset ℕ).card := by decide
    _ ≤ (tzWindow 64 (4 : ℝ)).card := Finset.card_le_card hsub

/-- **Concrete discharge for `n = 8, β = 5`** — completes the `β = 2, 3, 4, 5` tower for
the modulus `n = 8`.  The window `[8⁵, 2·8⁵] = [32768, 65536]` contains the eight primes
`32801, 32833, 32969, 32993, 33049, 33073, 33113, 33161`, all `≡ 1 (mod 8)`. -/
theorem tzPrimeSupply_8_five : TZPrimeSupply 8 (5 : ℝ) 8 := by
  refine ⟨?_⟩
  have hpow : ((8 : ℕ) : ℝ) ^ (5 : ℝ) = 32768 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({32801, 32833, 32969, 32993, 33049, 33073, 33113, 33161} : Finset ℕ)
      ⊆ tzWindow 8 (5 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (8 : ℕ)
      = ({32801, 32833, 32969, 32993, 33049, 33073, 33113, 33161} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 8 (5 : ℝ)).card := Finset.card_le_card hsub

/-! ## Axiom audit -/

#print axioms tzPrimeSupply_64_three
#print axioms tzPrimeSupply_32_four
#print axioms tzPrimeSupply_64_four
#print axioms tzPrimeSupply_512_two
#print axioms tzPrimeSupply_1024_two
#print axioms tzPrimeSupply_2048_two
#print axioms tzPrimeSupply_4096_two
#print axioms tzPrimeSupply_8192_two
#print axioms tzPrimeSupply_16384_two
#print axioms tzPrimeSupply_32768_two

end ArkLib.ProximityGap.KKH26
