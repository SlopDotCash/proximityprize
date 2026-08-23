/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf5M3_crossstep_ceiling
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The `r = 1` rung of the open per-step crux `M3CrossStepBound` is the proven `r = 2` energy ceiling (Issue #444)

The additive-depth recursion closure `_wf5M3_crossstep_ceiling.lean` reduces the whole prize energy
ladder to ONE open `Prop`,

    `M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r · (2r−1)‼ · n^{r+1}`,

`n = |G|`, `crossMass G r = E_{r+1} − |G|·E_r` (the off-diagonal cross mass of the proven recursion
`E_{r+1} = |G|·E_r + cross_r`). Its `∀ r` form is the genuine char-`p` wall; but the **base rung `r = 0`
and `r = 1` are NOT open** — they are pinned by the exact second moment and the proven `r = 2` energy
ceiling. This file discharges them with pure recursion arithmetic, NO new analytic input, connecting
the recursion's own `crossMass` object to the in-tree `GaussianEnergyBound`/Lam–Leung rungs that nobody
had wired to it.

## The exact value of the `r = 1` cross mass

By the proven recursion `rEnergy_succ_crossMass` at `r = 1` and the exact first moment `E_1 = |G|`
(`rEnergy_one`):

    `E_2 = |G|·E_1 + crossMass G 1 = |G|² + crossMass G 1`,   so   `crossMass G 1 = E_2 − |G|²`.

The `r = 1` step bound is `2·1·(2·1−1)‼·n² = 2·1·1·n² = 2n²`. Hence

> **`crossMass G 1 ≤ 2n²  ⟺  E_2 ≤ 3n²  =  LamLeungCeiling G 2  =  GaussianEnergyBound G 2`.**

So the `r = 1` rung of the OPEN crux is *exactly* the (proven for `μ_{2^m}`) `r = 2` energy ceiling —
no thinness, no Weil, no Lam–Leung deep antipodal input; it is the Sidon `E_2 ≤ 3n²` content alone.

## Results (axiom-clean, ℕ-arithmetic on the proven substrate)

* `crossMass_zero_eq`   : `crossMass G 0 = E_1 − |G| = 0` (the `r = 0` rung is `crossMass G 0 = 0 ≤ 0`).
* `crossStepBound_zero` : the `r = 0` rung of `M3CrossStepBound` is UNCONDITIONALLY true (`= 0 ≤ 0`).
* `crossMass_one_add`   : `E_2 = |G|² + crossMass G 1` (the exact additive recursion at `r = 1`).
* `crossStepBound_one_of_lamLeungTwo` : `LamLeungCeiling G 2 ⟹ crossMass G 1 ≤ 2|G|²`
    — the `r = 1` rung of `M3CrossStepBound` IS the proven `r = 2` energy ceiling.
* `crossStepBound_one_of_gaussianEnergyTwo` : same, phrased on the real-valued `GaussianEnergyBound G 2`.

## Honest scope

NOT a CORE closure. This pins the `r = 0, 1` rungs of `M3CrossStepBound` to already-proven energy
content; the OPEN crux is the rungs `r ≈ log q` (`r ≥ 2`), which this file does NOT touch. Value:
frontier-movement — it shows the recursion-closure's named open `Prop` is genuinely discharged at its
base, isolating the open content to deep `r`, and gives the fleet a `crossMass`-native consumer of the
proven Sidon/`GaussianEnergyBound` rungs (previously stated only in the `E_r`/`A_r` language, never in
the recursion's `crossMass` language). CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass M3CrossStepBound LamLeungCeiling)
open ArkLib.ProximityGap.GaussPeriodMomentBound (GaussianEnergyBound)

namespace ArkLib.ProximityGap.CrossStepRungOne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `r = 0` cross mass vanishes: `crossMass G 0 = 0`.** From the recursion at `r = 0`,
`E_1 = |G|·E_0 + crossMass G 0`, with `E_0 = 1` and `E_1 = |G|`, so `crossMass G 0 = 0`. -/
theorem crossMass_zero_eq (G : Finset F) : crossMass G 0 = 0 := by
  have hrec := rEnergy_succ_crossMass G 0
  rw [rEnergy_one,
      ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_zero, Nat.mul_one] at hrec
  -- hrec : G.card = G.card + crossMass G 0
  omega

/-- **The `r = 0` rung of `M3CrossStepBound` is unconditional.** The step bound at `r = 0` is
`2·0·… = 0`, and `crossMass G 0 = 0`, so `0 ≤ 0`. -/
theorem crossStepBound_zero (G : Finset F) :
    crossMass G 0 ≤ 2 * 0 * Nat.doubleFactorial (2 * 0 - 1) * G.card ^ (0 + 1) := by
  rw [crossMass_zero_eq]; simp

/-- **The exact `r = 1` recursion: `E_2 = |G|² + crossMass G 1`.** From `rEnergy_succ_crossMass G 1`
(`E_2 = |G|·E_1 + crossMass G 1`) and `rEnergy_one` (`E_1 = |G|`). -/
theorem crossMass_one_add (G : Finset F) :
    rEnergy G 2 = G.card ^ 2 + crossMass G 1 := by
  have hrec := rEnergy_succ_crossMass G 1
  rw [rEnergy_one] at hrec
  -- hrec : E_2 = G.card * G.card + crossMass G 1
  rw [hrec, sq]

/-- **THE FRONTIER CONNECTION: the `r = 1` rung of the open crux `M3CrossStepBound` IS the proven
`r = 2` energy ceiling.** `LamLeungCeiling G 2` (`E_2 ≤ 3|G|²`) implies `crossMass G 1 ≤ 2|G|²`
(the `r = 1` instance of `M3CrossStepBound`, since `2·1·(2·1−1)‼·|G|² = 2·1·1·|G|² = 2|G|²`). No
analytic input beyond the proven recursion and the `r = 2` Sidon energy ceiling. -/
theorem crossStepBound_one_of_lamLeungTwo (G : Finset F) (h : LamLeungCeiling G 2) :
    crossMass G 1 ≤ 2 * G.card ^ 2 := by
  -- LamLeungCeiling G 2 : E_2 ≤ (2*2-1)‼ · |G|² = 3 · |G|²
  unfold LamLeungCeiling at h
  have hdf : Nat.doubleFactorial (2 * 2 - 1) = 3 := by decide
  rw [hdf] at h
  -- h : E_2 ≤ 3 · |G|²; and E_2 = |G|² + crossMass G 1
  rw [crossMass_one_add] at h
  -- h : |G|² + crossMass G 1 ≤ 3 · |G|²
  omega

/-- **Same rung, stated on the real-valued `GaussianEnergyBound G 2`.** `GaussianEnergyBound G 2`
(`(E_2 : ℝ) ≤ 3·|G|²`) implies the `ℕ` ceiling `E_2 ≤ 3|G|²` (cast back), hence the `r = 1` cross
bound. This lets the in-tree `GaussianEnergyBound`-language rungs (e.g. the Sidon `r = 2` rung) feed
the recursion's `crossMass` directly. -/
theorem crossStepBound_one_of_gaussianEnergyTwo (G : Finset F) (h : GaussianEnergyBound G 2) :
    crossMass G 1 ≤ 2 * G.card ^ 2 := by
  apply crossStepBound_one_of_lamLeungTwo
  unfold GaussianEnergyBound at h
  unfold LamLeungCeiling
  -- h : (E_2 : ℝ) ≤ (2*2-1)‼ · |G|^2; want E_2 ≤ (2*2-1)‼ · |G|^2 in ℕ
  have hcast : ((rEnergy G 2 : ℕ) : ℝ)
      ≤ ((Nat.doubleFactorial (2 * 2 - 1) * G.card ^ 2 : ℕ) : ℝ) := by
    push_cast
    convert h using 2
  exact_mod_cast hcast

end ArkLib.ProximityGap.CrossStepRungOne

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungOne.crossMass_zero_eq
#print axioms ArkLib.ProximityGap.CrossStepRungOne.crossStepBound_zero
#print axioms ArkLib.ProximityGap.CrossStepRungOne.crossMass_one_add
#print axioms ArkLib.ProximityGap.CrossStepRungOne.crossStepBound_one_of_lamLeungTwo
#print axioms ArkLib.ProximityGap.CrossStepRungOne.crossStepBound_one_of_gaussianEnergyTwo
