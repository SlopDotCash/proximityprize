/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyFromPairing
import ArkLib.Data.CodingTheory.ProximityGap.EnergyBoundImplication
import ArkLib.Data.CodingTheory.ProximityGap.PrizeSupNormHeadline

/-!
# The proven-regime prize sup-norm bound (#407)

Chaining the in-tree Lam–Leung pairing proof (`gaussianEnergyBound_of_pairing`) through the DC
correction (`dcEnergyBound_of_gaussianEnergyBound`) and the optimized headline (`prize_supNorm_bound`)
gives the prize sup-norm bound UNCONDITIONALLY under the pairing hypotheses (the char-0 / proven-regime
`q > (2r)^{|G|/2}` input, where every mod-`p` vanishing `2r`-sum is a genuine antipodal pairing):

> **`prize_supNorm_of_pairing`** — under the three pairing conditions at `r = ⌈ln q⌉`, every `b ≠ 0`
> satisfies `‖η_b‖² ≤ 2e·|G|·⌈ln q⌉`.

So the entire corrected reduction is *unconditional* in the proven regime; the prize regime (`q < 2^|G|`)
is exactly where the pairing hypothesis `H` fails (non-antipodal mod-`p` vanishing sums = the anomaly),
which is the BGK content. This brick certifies the corrected chain composes with the in-tree input.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound ArkLib.ProximityGap.GaussianEnergyFromPairing
open ArkLib.ProximityGap.EnergyBoundImplication ArkLib.ProximityGap.PrizeSupNormHeadline
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.PrizeSupNormFromPairing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Proven-regime prize sup-norm bound.** Under the Lam–Leung pairing conditions at `r = ⌈ln q⌉`
(`E_r = zeroSumCount`, `#pairings ≤ (2r−1)‼`, and every vanishing `2r`-sum is a pairing), the corrected
chain yields `‖η_b‖² ≤ 2e·|G|·⌈ln q⌉` for every `b ≠ 0` — unconditionally. -/
theorem prize_supNorm_of_pairing {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hqc : 1 < Fintype.card F)
    (henergy : rEnergy G ⌈Real.log (Fintype.card F)⌉₊
        = zeroSumCount G (2 * ⌈Real.log (Fintype.card F)⌉₊))
    (hcount : (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (2 * ⌈Real.log (Fintype.card F)⌉₊)) => IsPairing σ)).card
        ≤ Nat.doubleFactorial (2 * ⌈Real.log (Fintype.card F)⌉₊ - 1))
    (H : ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * ⌈Real.log (Fintype.card F)⌉₊) => G),
        (∑ i, c i = 0) → ∃ σ : Equiv.Perm (Fin (2 * ⌈Real.log (Fintype.card F)⌉₊)),
          IsPairing σ ∧ ∀ i, c (σ i) = - c i)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2
      ≤ 2 * Real.exp 1 * (G.card : ℝ) * (⌈Real.log (Fintype.card F)⌉₊ : ℝ) :=
  prize_supNorm_bound hψ hqc
    (dcEnergyBound_of_gaussianEnergyBound
      (gaussianEnergyBound_of_pairing G _ henergy hcount H)) hb

end ArkLib.ProximityGap.PrizeSupNormFromPairing
#print axioms ArkLib.ProximityGap.PrizeSupNormFromPairing.prize_supNorm_of_pairing
