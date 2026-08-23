/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyFromPairing
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyEssential

/-!
# The antipodal-pairing residual `H` FAILS at the prize scale (#407)

`GaussianEnergyFromPairing.gaussianEnergyBound_of_pairing` derives the raw Wick energy bound
`GaussianEnergyBound G r : E_r(G) ≤ (2r−1)‼·|G|^r` from three inputs: the unconditional negation-closure
identity `henergy : rEnergy G r = zeroSumCount G (2r)`, the unconditional matching count
`hcount : #{pairings} ≤ (2r−1)‼`, and the genuine open input

> `H` — the **antipodal-pairing residual**: *every* zero-sum `2r`-tuple of `G` is antipodally paired
> (`∀ c, ∑ c i = 0 → ∃ σ pairing, ∀ i, c (σ i) = −c i`).

The 2026-06-14 ★★ correction (`DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt`) PROVES the
conclusion `GaussianEnergyBound G r` is **FALSE** whenever the DC term beats Wick, i.e. when
`q·(2r−1)‼ < |G|^r` (the prize regime: `n ≥ 64` at `r ≈ log q`, since `|G|^{2r}/q ≫ Wick`). By modus
tollens, holding the two unconditional combinatorial inputs fixed, **`H` itself must be false there**:

> **`not_pairing_residual_of_card_pow_gt`** — under `henergy` and `hcount`, if `q·(2r−1)‼ < |G|^r`
> then `¬H`: there EXISTS a zero-sum `2r`-tuple of `G` that is NOT antipodally paired.

This locates precisely where the K1 / pairing (char-0 Lam–Leung) route breaks at the prize: the
above-threshold antipodal-pairing structure — true in char 0 and at small `n` — is destroyed by the
char-`p` anomaly at `n ≥ 64`, `r ≈ log q`. The non-antipodal zero-sum tuples are exactly the char-`p`
extra solutions the DC term counts (`E_r ≥ |G|^{2r}/q ≫ Wick`). So the pairing route cannot supply the
prize carrier `E_r ≤ Wick` at prize scale; only the DC-subtracted `A_r ≤ Wick` survives (the genuinely
thinness-essential object). A mapped wall, not a closure.

Axiom-clean (`propext, Classical.choice, Quot.sound`).

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.GaussianEnergyFromPairing

namespace ArkLib.ProximityGap.PairingResidualFailsAtPrize

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The antipodal-pairing residual `H` fails at the prize scale.** Under the two unconditional
combinatorial inputs of `gaussianEnergyBound_of_pairing` (`henergy`: the negation-closure energy↔zero-sum
identity; `hcount`: the matching count bound), if the DC term beats Wick (`q·(2r−1)‼ < |G|^r`, the prize
regime `n ≥ 64`, `r ≈ log q`), then the antipodal-pairing residual `H` is FALSE: some zero-sum `2r`-tuple
of `G` is NOT antipodally paired. Proof: `gaussianEnergyBound_of_pairing` would give
`GaussianEnergyBound G r`, but `not_gaussianEnergyBound_of_card_pow_gt` refutes it (contradiction). -/
theorem not_pairing_residual_of_card_pow_gt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ)
    (henergy : rEnergy G r = zeroSumCount G (2 * r))
    (hcount : (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)).card
        ≤ Nat.doubleFactorial (2 * r - 1))
    (hqpos : (0 : ℝ) < Fintype.card F) (hGpos : (0 : ℝ) < G.card)
    (hq : (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) < (G.card : ℝ) ^ r) :
    ¬ (∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G), (∑ i, c i = 0) →
        ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i) := by
  intro H
  have hbound : GaussianEnergyBound G r := gaussianEnergyBound_of_pairing G r henergy hcount H
  exact DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt hψ G r hqpos hGpos hq hbound

end ArkLib.ProximityGap.PairingResidualFailsAtPrize

#print axioms ArkLib.ProximityGap.PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt
