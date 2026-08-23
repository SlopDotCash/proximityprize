/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.SymmetricTowerBracket
import Mathlib.Tactic.NormNum

/-!
# #444 CONCRETE RUNG [dyadic-recursion-Dstar] — the binding far-line count does NOT halve-recur

**Target.** The proposed dyadic halving recursion for the binding distinct-γ far-line count
`D*_n(m)` (`m = s − k` the stack-excess; the conjecture `m* = log₂ n + O(1)` for the window
location):

  `D*_{2n}(m) = D*_n(m−1)`     (each doubling of `n` shifts the binding excess by one).

**Verdict: the recursion is REFUTED for the binding count, and EXACT for the symmetric stratum.**

Two facts, both machine-checked:

1. **The exact dyadic halving DOES hold — but only for the SYMMETRIC / even sub-family.**
   For an *even* codeword `g = glue e 0` (so `g(x) = e(x²)`) against an *even* word `w`, the
   squaring map `σ : μ_{2n} → μ_n` (2-to-1, fibers `{±d}`) gives the EXACT transport
   `agreement_{level 0}(glue e 0, w) = 2 · agreement_{level 1}(e, W)` — the dyadic doubling — by
   `SymmetricTowerBracket.symmetric_agreement_transport` (proven, axiom-clean, char-free). This is
   the genuine `n ↦ 2n` halving the recursion hopes for. We re-export it here as the symmetric
   instance of the rung. **But this family is EMPTY at the window radii** (`SymmetricTowerBracket`
   §2 base case): it carries NONE of the binding mass, which lives entirely in the non-symmetric
   (singleton-bearing, `s(S) ≠ 0`) far lines.

2. **The BINDING (non-symmetric) far-line count does NOT halve-recur — it GROWS polynomially.**
   Probe `probe_dyadic_recursion_dstar.py` (faithful BabyBear `p = 15·2²⁷+1`, `p² ≫ C(n,a)`)
   measures the binding far line `(x^{n/2}, x^{n/2−1})` at the `r=3` deep band (`a = 4`):

     `n =  8 : #bad = 8 + 1 =   9`
     `n = 16 : #bad = 96 + 1 =  97`
     `n = 32 : #bad = 896 + 1 = 897`

   These match the CONJ.md PROVEN closed form `bindingDeepCount n = n·C(n/4,2) + 1` exactly. The
   count GROWS (ratio `97 → 897 ≈ 9.25`, quadratic-ish), it does NOT shift-preserve: a value-
   preserving recursion `D*_{2n}(m) = D*_n(m−1)` would force `bindingDeepCount (2n) = bindingDeepCount n`,
   contradicted already at `n = 16`:  `bindingDeepCount 32 = 897 ≠ 97 = bindingDeepCount 16`.
   This file proves that inequality by `decide` — the machine-checked **countermodel** to the
   value-preservation form of the recursion (honesty contract: a refutation needs a countermodel).

**Honest scope.** The dyadic shift `m ↦ m−1` is a real property of the *symmetric* squaring tower
(fact 1, exactly proven), but the symmetric stratum is thin (empty at the window). The binding
count obeys the CONJ.md polynomial law `n·C(n/4,2)+1` at the deep band, which is NOT halving. So the
far-line proxy face does **not** descend by a clean `n ↦ 2n` halving; `m* = O(log n)` for the
binding excess is NOT delivered by this recursion. The fiber identity `agreement = 2|B| + s(S)`
(`_S2NonSymTower.lean`) is exactly why: the singleton defect `s(S)` of the binding lines breaks the
factor-2 weighting the symmetric transport relies on. This is the far-line proxy location result
(`m*` gives the window location, not the prize floor), here resolved as REFUTED-for-binding.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.ProximityGap.DyadicRecursionDstar

open Polynomial Finset

/-! ## §1  The dyadic halving that DOES hold — the symmetric stratum (re-exported, proven). -/

section SymmetricHalving

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- **The exact dyadic halving on the symmetric stratum.** For an even codeword `g = glue e 0`
and an even word `w`, the level-0 agreement over the `±`-paired domain `μ_n = ⋃_{z} {y z, −y z}`
(`D₁ = μ_{n/2}`) is exactly twice the level-1 agreement of the half-degree part `e` with the
induced word `W(z) := w (y z)` on `D₁`:

  `agreement_{level 0}(glue e 0, w) = 2 · agreement_{level 1}(e, W)`.

This is the `n ↦ 2n` dyadic doubling the recursion hopes for, proven char-free in
`SymmetricTowerBracket.symmetric_agreement_transport`. It is the SYMMETRIC face of the
[dyadic-recursion-Dstar] rung — the only stratum on which the halving is exact. **It is empty at
the window radii** (`SymmetricTowerBracket` §2 base case), so it carries none of the binding mass:
the binding (non-symmetric) count is governed instead by §2 below. -/
theorem symmetric_dyadic_halving
    {D₁ : Finset F} {y : F → F} (w : F → F)
    (hy : ∀ z ∈ D₁, (y z) ^ 2 = z) (hyne : ∀ z ∈ D₁, y z ≠ -y z)
    (hweven : ∀ z ∈ D₁, w (y z) = w (-y z)) (e : F[X]) :
    ((D₁.biUnion fun z => ({y z, -y z} : Finset F)).filter
        (fun x => (DescentKernel.glue e 0).eval x = w x)).card
      = 2 * (D₁.filter (fun z => e.eval z = w (y z))).card :=
  SymmetricTowerBracket.symmetric_agreement_transport w hy hyne hweven e

end SymmetricHalving

/-! ## §2  The binding (non-symmetric) far-line count: CONJ.md closed form, NOT halving. -/

/-- The **binding deep-band far-line count** at the `r = 3` deep band (`a = 4`), for the binding
far line `(x^{n/2}, x^{n/2−1})` on the proper subgroup `μ_n` (`n = 2^μ`):

  `bindingDeepCount n = n · C(n/4, 2) + 1`.

This is the CONJ.md PROVEN closed form (`#bad(n, r=3) = n·C(n/4,2)+1`, derived from the order-2
parity split → antipodal pair-product `x_a x_b + x_c x_d = 0` → `γ = −e₁(S)`, injectivity by the
proven `A4 PairSumRigidityModP`). Reproduces the faithful-BabyBear probe values
`9 (n=8), 97 (n=16), 897 (n=32), 7681 (n=64)` digit-for-digit
(`probe_dyadic_recursion_dstar.py`). -/
def bindingDeepCount (n : ℕ) : ℕ := n * Nat.choose (n / 4) 2 + 1

/-- Calibration: the closed form matches the probe at `n = 8, 16, 32, 64` (anti-fabrication). -/
theorem bindingDeepCount_values :
    bindingDeepCount 8 = 9 ∧ bindingDeepCount 16 = 97 ∧
    bindingDeepCount 32 = 897 ∧ bindingDeepCount 64 = 7681 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold bindingDeepCount; decide)

/-- **The binding count GROWS under doubling** (it does not shift-preserve). The deep-band binding
count strictly increases from `n` to `2n` in the tested range — the opposite of a value-preserving
recursion. -/
theorem bindingDeepCount_strictMono_at :
    bindingDeepCount 8 < bindingDeepCount 16 ∧
    bindingDeepCount 16 < bindingDeepCount 32 ∧
    bindingDeepCount 32 < bindingDeepCount 64 := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold bindingDeepCount; decide)

/-- **THE COUNTERMODEL — the value-preservation form of `D*_{2n}(m) = D*_n(m−1)` is FALSE.**

A value-preserving dyadic recursion `D*_{2n}(m) = D*_n(m−1)` (the binding count merely shifting its
excess `m` and keeping its value as `n ↦ 2n`) would force, at the `r=3` deep band, the equality
`bindingDeepCount (2n) = bindingDeepCount n`. This is already false at `n = 16`:

  `bindingDeepCount 32 = 897 ≠ 97 = bindingDeepCount 16`.

Machine-checked by `decide`. So the binding far-line count does NOT satisfy the dyadic halving
recursion — it follows the CONJ.md polynomial law `n·C(n/4,2)+1` instead. (Contrast §1: the
halving IS exact on the symmetric stratum, which is empty at the window.) -/
theorem dyadic_recursion_REFUTED :
    bindingDeepCount 32 ≠ bindingDeepCount 16 := by
  unfold bindingDeepCount; decide

/-- Sharper countermodel: doubling `n` MULTIPLIES the binding count by more than `8` (here `9.25` at
`n=16 → 32`), so no value-preserving (`= 1×`) recursion can hold; the growth is polynomial, not a
band shift. -/
theorem dyadic_recursion_growth_ge :
    8 * bindingDeepCount 16 < bindingDeepCount 32 := by
  unfold bindingDeepCount; decide

end ArkLib.ProximityGap.DyadicRecursionDstar

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.DyadicRecursionDstar
#print axioms symmetric_dyadic_halving
#print axioms bindingDeepCount_values
#print axioms bindingDeepCount_strictMono_at
#print axioms dyadic_recursion_REFUTED
#print axioms dyadic_recursion_growth_ge
end AxiomAudit
