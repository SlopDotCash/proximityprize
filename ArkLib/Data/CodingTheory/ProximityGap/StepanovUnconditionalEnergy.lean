/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountDiagonalBound

/-!
# The first UNCONDITIONAL sub-cubic additive-energy bound for `μ_n` (#389)

Every in-tree additive-energy *upper* bound for a multiplicative subgroup is so far either the
trivial cube `E(G) ≤ |G|³`, conditional on the open Garcia–Voloch input `GVRepBound`
(`E(G) ≲ |G|^{8/3}`), or an exact value valid only in the tiny Sidon regime `n < log₂ q`
(`AdditiveEnergySidonModNeg`).  This file gives the first bound that is simultaneously
*unconditional*, *scale-free in `q`*, and *strictly below the cube* — by feeding the **complete
order-2 Stepanov representation bound** `r(c) ≤ (n+1)/2` (proven for *every* `c ≠ 0` in
`RepCountDiagonalBound`, unifying the off-diagonal auxiliary `Q(X)=(c−X)^{n+1}+X^{n+1}−c` with the
diagonal multiplicative symmetry) into the representation→energy reduction
`additiveEnergy_le_of_repBound`:

  `E(μ_n) ≤ (1 + (n+1)/2)·|G|²`   (`additiveEnergy_le_stepanov`).

For `|G| = n` this is `Θ(n³)`, a constant-factor `≈ 2×` below the trivial cube — it does **not**
reach the Heath-Brown–Konyagin `n^{5/2}` (that needs the multi-page confluent-Stepanov / Wronskian
degree-reduction; the generic engine provably *cannot* produce the saving, see
`StepanovGenericInsufficiency`), and the energy→supply `√`-loss (`T(G)² ≤ |G|·E(G)`) means it does
not advance the δ\* prize.  Its role is to **cap the order-2 lane honestly**: it pins the best the
explicit order-2 auxiliary can deliver as an energy statement, documenting exactly where the lane
stops and why the confluent construction is the only route below cubic order.

The side conditions (`Even n`, `2 ≠ 0`, `2^n ≠ 1`) hold automatically for NTT domains
`n = 2^k` in the deployed regime `1 < 2^n < q`; the `2^n ≠ 1` guard correctly excludes the
`F₁₇`/`μ₈` benchmark (`2^8 ≡ 1 (17)`), so there is no clash with the exact value there.

## Main results
* `additiveEnergy_le_stepanov` — `E(μ_n) ≤ (1 + (n+1)/2)·|G|²`.
* `two_mul_additiveEnergy_le_stepanov` — floor-free `2·E ≤ (n+3)·|G|²`.
* `additiveEnergy_lt_cube_stepanov` — `E(μ_n) < n³` for `n ≥ 4`, `|G| = n`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Unconditional sub-cubic additive-energy bound for `μ_n`.**  For `G = μ_n` with `n` even,
`2 ≠ 0`, `2^n ≠ 1` (all automatic in the deployed regime `p > 2^n`), the complete order-2
Stepanov bound `r(c) ≤ (n+1)/2` for every `c ≠ 0` feeds the representation→energy reduction:
`E(μ_n) ≤ (1 + (n+1)/2)·|G|²`.  Strictly below the trivial cube `|G|³` for `|G| = n`. -/
theorem additiveEnergy_le_stepanov {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1) :
    additiveEnergy G ≤ (1 + (n + 1) / 2) * G.card ^ 2 := by
  refine additiveEnergy_le_of_repBound G ((n + 1) / 2) (fun t ht => ?_)
  have h := repCount_two_mul_le hn hEven hGmem h2 h2n (c := t) ht
  omega

/-- The same bound, doubled, to avoid `Nat` floor division: `2·E(μ_n) ≤ (n+3)·|G|²`. -/
theorem two_mul_additiveEnergy_le_stepanov {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1) :
    2 * additiveEnergy G ≤ (n + 3) * G.card ^ 2 := by
  have h := additiveEnergy_le_stepanov hn hEven hGmem h2 h2n
  have hfloor : 2 * (1 + (n + 1) / 2) ≤ n + 3 := by omega
  calc 2 * additiveEnergy G
      ≤ 2 * ((1 + (n + 1) / 2) * G.card ^ 2) := by omega
    _ = (2 * (1 + (n + 1) / 2)) * G.card ^ 2 := by ring
    _ ≤ (n + 3) * G.card ^ 2 := Nat.mul_le_mul_right _ hfloor

/-- **Strictly sub-cubic:** when `|G| = n`, `2·E(μ_n) ≤ (n+3)·n² < 2·n³` for `n ≥ 4`, i.e.
`E(μ_n) < n³`. -/
theorem additiveEnergy_lt_cube_stepanov {G : Finset F} {n : ℕ} (hn4 : 4 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h2n : (2 : F) ^ n ≠ 1) :
    additiveEnergy G < n ^ 3 := by
  have h := two_mul_additiveEnergy_le_stepanov (by omega) hEven hGmem h2 h2n
  rw [hcard] at h
  nlinarith [h, sq_nonneg n]

end ArkLib.ProximityGap.AdditiveEnergyRepBound
