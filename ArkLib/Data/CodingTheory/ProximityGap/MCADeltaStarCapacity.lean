/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAUpToCapacityFalse

/-!
# The concrete MCA threshold is below near-capacity (#232, MCA Grand Challenge)

Companion to the list-decoding envelope, on the *other* Grand Challenge. The faithful continuous
MCA threshold `mcaDeltaStar C ε* = sSup {δ | ε_mca(C, δ) ≤ ε*}` is capped strictly below
near-capacity:

  `rs_mcaDeltaStar_le_capacity` — for `RS[F, domain, k]` (`1 ≤ k ≤ n`) over a field with
  `|F| < (n−k)·2^128`, `mcaDeltaStar(RS, 2^{-128}) ≤ 1 − (k+1)/n`.

Direct from `mcaDeltaStar_le_of_bad` fed by the near-capacity MCA refutation
`rs_mca_uptoCapacity_false_of_smallField` (`ε_mca(RS, 1−(k+1)/n) > ε*`). Combined with the
unique-decoding lower witness `rs_mcaLowerWitness_udr` (`δ* ≳ (1−ρ)/3`), this two-sided-traps the
*concrete* MCA threshold `(1−ρ)/3 ≲ δ*_mca ≤ 1 − (k+1)/n` — the MCA analog of the list-decoding
bracket. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

The MCA→Johnson refinement (tightening the lower side to `1 − √ρ`) is the BCIKS20 *bivariate*
line-decoding argument — genuinely harder than the list-decoding Johnson bound (which counts
codewords in a single ball), and MCA→capacity is the open prize core.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap.MCAThresholdLedger

open scoped NNReal ENNReal
open ProximityGap

/-- **The concrete MCA threshold is below near-capacity.** For `RS[F, domain, k]` with `1 ≤ k ≤ n`
over a field with `|F| < (n−k)·2^128`, the faithful MCA threshold satisfies
`mcaDeltaStar(RS, 2^{-128}) ≤ 1 − (k+1)/n` — so the Grand MCA threshold does not reach capacity. -/
theorem rs_mcaDeltaStar_le_capacity {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n] (domain : Fin n ↪ F) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hsmall : (Fintype.card F : ℝ) < ((n - k : ℕ) : ℝ) * 2 ^ 128) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain k : Set (Fin n → F)) (ENNReal.ofReal (1 / 2 ^ 128))
      ≤ 1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0) :=
  mcaDeltaStar_le_of_bad (F := F) (A := F) _ _
    (ProximityGap.MCANearCapacityGK.rs_mca_uptoCapacity_false_of_smallField
      domain k hk1 hkn hsmall)

#print axioms rs_mcaDeltaStar_le_capacity

end ProximityGap.MCAThresholdLedger
