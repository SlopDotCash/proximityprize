/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountDiagonalBound
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The floor-free additive-energy bound for `μ_n` on the deployed 2-power (NTT) domain (#444)

`StepanovUnconditionalEnergy.lean` feeds the order-2 Stepanov rep bound `r(c) ≤ (n+1)/2`
(`RepCountDiagonalBound.repCount_two_mul_le` : `r(c)·2 ≤ n+1`, valid for every `c ≠ 0`, both the
off-diagonal `c^n ≠ 1` and the diagonal `c^n = 1` cases) into the representation→energy reduction
`additiveEnergy_le_of_repBound`, getting `E(μ_n) ≤ (1 + (n+1)/2)·|G|²` and the doubled form
`2·E(μ_n) ≤ (n+3)·|G|²`.

For the deployed NTT domains `μ_n` with **`n` even** (`n = 2^k`), `(n+1)/2 = n/2` in `ℕ`, so the
per-`c` bound `r(c)·2 ≤ n+1` already gives the **exact integer** uniform bound `r(c) ≤ n/2`. Feeding
`M = n/2` (rather than the floored `(n+1)/2`, which is the *same value* but is doubled with slack in
`two_mul_additiveEnergy_le_stepanov`) into the reduction removes the doubling floor-slack:

> `two_mul_additiveEnergy_le_stepanov_even` : `2·E(μ_n) ≤ (n+2)·|G|²` for `n` even,

**strictly below** the general route's `2·E ≤ (n+3)·|G|²`. The single saved unit is purely the
floor-division slack the general doubling `2·(1 + (n+1)/2) = n+3` incurs but the even-`n` exact
`2·(1 + n/2) = n+2` does not (it is *not* sourced from any individual `c` having `r(c)·2 ≤ n`; the
diagonal `c^n=1` case genuinely contributes `r(c)·2 ≤ n+1`, but `⌊(n+1)/2⌋ = n/2` absorbs it).

## Honest scope

This is a **one-unit, floor-free restatement** of the existing even-`n` order-2 energy bound — a
trivial-but-real tightening of the additive constant on the *doubled* form, NOT a change of order and
NOT a CORE lever. The floored bound `additiveEnergy_le_stepanov_even` is *numerically identical* to
`additiveEnergy_le_stepanov` for even `n`; only the doubled constant differs (`n+2` vs `n+3`). The
order-2 lane is `Θ(n³)` (≈ 2× below the trivial cube); reaching the Heath-Brown–Konyagin `n^{5/2}`
needs the confluent order-`~n^{1/3}` construction, which the generic engine provably cannot supply
(`StepanovGenericInsufficiency`). The energy→worst-period `√`-loss means the quartic bound this
yields (`‖η_b‖⁴ ≤ q·(1+n/2)|G|²`) is strictly **dominated** by the in-tree
`EtaQuarticUncond.eta_quartic_le_uncond` (`≤ n²(q−n)`). So this does **not** advance `δ*`. The prize
`M(μ_n) ≤ C·√(n·log(p/n))` stays open.

`sorry`-free, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

Issue #444 (the energy lane endpoint; the parent rep bound is #389).
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Even-`n` order-2 energy bound (floored form).** For `G = μ_n` with `n` even, feeding the exact
integer bound `r(c) ≤ n/2` (from the unified `repCount_two_mul_le`, `r(c)·2 ≤ n+1`, via
`(n+1)/2 = n/2` for even `n`) into the reduction gives `E(μ_n) ≤ (1 + n/2)·|G|²`. Numerically
**identical** to `additiveEnergy_le_stepanov` for even `n` (since `(n+1)/2 = n/2` in `ℕ`); restated
with the exact `n/2` constant so the doubled form below avoids floor slack. -/
theorem additiveEnergy_le_stepanov_even {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1) :
    additiveEnergy G ≤ (1 + n / 2) * G.card ^ 2 := by
  refine additiveEnergy_le_of_repBound G (n / 2) (fun t ht => ?_)
  -- The *unified* order-2 bound `repCount t * 2 ≤ n + 1` (off-diagonal sharpens to `n`, but the
  -- diagonal `t^n = 1` only gives `n + 1`); for **even** `n` this already yields `repCount t ≤ n/2`
  -- because `(n+1)/2 = n/2` in `ℕ`. The floor-free gain below comes from `M = n/2` being an exact
  -- integer, not from any individual case being `≤ n`.
  have h := repCount_two_mul_le hn hEven hGmem h2 h2n (c := t) ht
  obtain ⟨k, hk⟩ := hEven
  omega

/-- **The floor-free even-`n` energy bound:** `2·E(μ_n) ≤ (n+2)·|G|²`. Strictly below the general
route's `2·E ≤ (n+3)·|G|²` (`two_mul_additiveEnergy_le_stepanov`): the exact-integer `M = n/2` carries
no floor-division slack, so `2·(1 + n/2) = n+2`, whereas doubling the general floored `(n+1)/2` gives
`n+3`. The one saved unit is purely floor slack (the per-`c` bound is still `r(c)·2 ≤ n+1`, including
on the diagonal). The floor-free endpoint of the order-2 lane on the deployed 2-power NTT domain. -/
theorem two_mul_additiveEnergy_le_stepanov_even {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h2n : (2 : F) ^ n ≠ 1) :
    2 * additiveEnergy G ≤ (n + 2) * G.card ^ 2 := by
  have h := additiveEnergy_le_stepanov_even hn hEven hGmem h2 h2n
  -- `2·(1 + n/2) ≤ n + 2` exactly for even `n` (no floor slack).
  obtain ⟨k, hk⟩ := hEven
  have hfloor : 2 * (1 + n / 2) ≤ n + 2 := by omega
  calc 2 * additiveEnergy G
      ≤ 2 * ((1 + n / 2) * G.card ^ 2) := by omega
    _ = (2 * (1 + n / 2)) * G.card ^ 2 := by ring
    _ ≤ (n + 2) * G.card ^ 2 := Nat.mul_le_mul_right _ hfloor

/-- **Strictly sub-cubic, even `n`:** `2·E ≤ (n+2)·n²`, hence `E(μ_n) < n³` for `|G| = n`, `n ≥ 2`.
Sharper threshold than the general `additiveEnergy_lt_cube_stepanov` (which needs `n ≥ 4`): the
floor-free even bound already gives `2E ≤ (n+2)n² < 2n³` for `n ≥ 3`, so `E < n³` for every even
`n ≥ 4` (the smallest even NTT domain above the `2^n ≠ 1` benchmark exclusion). -/
theorem additiveEnergy_lt_cube_stepanov_even {G : Finset F} {n : ℕ} (hn4 : 4 ≤ n) (hEven : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h2n : (2 : F) ^ n ≠ 1) :
    additiveEnergy G < n ^ 3 := by
  have h := two_mul_additiveEnergy_le_stepanov_even (by omega) hEven hGmem h2 h2n
  rw [hcard] at h
  nlinarith [h, sq_nonneg n]

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_stepanov_even
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.two_mul_additiveEnergy_le_stepanov_even
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_lt_cube_stepanov_even
