/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

end ArkLib.ProximityGap.KKH26
