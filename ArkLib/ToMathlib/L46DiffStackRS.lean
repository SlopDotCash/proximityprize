/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw
-/

import ArkLib.ToMathlib.L46GSLowerBound
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# ABF26 Lemma 4.6 for Reed–Solomon codes (the difference-stack residual, discharged)

This file delivers the **Reed–Solomon instantiation** of ABF26 Lemma 4.6's hard direction. It sits
on top of two in-tree results:

* the abstract-code *chaining* lemma `ProximityGap.diffStackMCAResidualBelowUDR_of_epsCA_ge`
  (`ProximityGap.Errors`): under UDR `2·δ·n < δ_min(C)` with `[NoZeroSMulDivisors F A]`, the numeric
  dominance `⌊δ·n⌋/|F| ≤ ε_ca(C, δ, δ)` implies the per-stack difference-stack residual
  `diffStackMCAResidualBelowUDR C δ`;
* the Guruswami–Sudan *lower bound* `ProximityGap.L46GS.floorCount_le_epsCA_of_gsWitness`
  (`ArkLib.ToMathlib.L46GSLowerBound`): the explicit BCIKS20-style witness existence
  `GSWitnessLowerBound C δ ⌊δ·n⌋` supplies exactly that numeric dominance.

## Why the Reed–Solomon form is the faithful statement (and the abstract form is false)

The numeric dominance `(★) : ⌊δ·n⌋/|F| ≤ ε_ca(C, δ, δ)` is **false for bare abstract codes**: a
`Submodule`/`Set` code with no non-jointly-close near-codewords has `ε_ca = 0` while `⌊δ·n⌋/|F|` can
be positive, and the per-coordinate double-coverage route that would prove it is kernel-refuted by
`ProximityGap.LineDecodingCounting.double_coverage_counterexample`. So `(★)` is *not* a theorem
about the abstract `epsCA`; it is a consequence of the explicit good-`γ`-set existence
`L46GS.GSWitnessLowerBound C δ ⌊δ·n⌋` ([BCIKS20, Prop 1.1] / [ACFY25, Lemma 4.10]).

For Reed–Solomon codes that witness **exists**: a `δ`-close non-codeword (deep hole) lies in a
list-decoding ball, and each close codeword in the line `u 0 + γ·u 1`'s decoding list contributes a
distinct good combiner `γ`, the Guruswami–Sudan degree structure both producing and capping the
count at `⌊δ·n⌋`. The honest residual surface for the RS results below is therefore the single named
hypothesis `L46GS.GSWitnessLowerBound (ReedSolomon.code domain deg) δ ⌊δ·n⌋` — exactly the BCIKS20
witness construction, no abstract dominance smuggled in.

## Deliverables

* `diffStackMCAResidualBelowUDR_rs` — the per-stack difference-stack residual for an RS code,
  consuming the GS-witness lower bound and the UDR hypothesis.
* `epsMCA_eq_epsCA_below_udr_rs` — **ABF26 Lemma 4.6 for Reed–Solomon**: `ε_mca = ε_ca` below UDR,
  reduced to the single named GS-witness hypothesis. This is the issue's real goal.
* `diffStackMCAResidualBelowUDR_rs_of_two_mul_lt_card_sub` and
  `epsMCA_eq_epsCA_below_udr_rs_of_two_mul_lt_card_sub` — the same, with the UDR hypothesis stated
  *numerically in the RS distance* `card ι − deg + 1` (via `ReedSolomon.dist_eq'`), so callers need
  not unfold `Code.dist` for the RS code.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed–Solomon Codes*.
* [ACFY25] / [Hab25] — the Guruswami–Sudan exceptional-`γ` rearrangement.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace L46GS

section

-- Same universe discipline as `ProximityGap.Errors` (PMF forces `Type 0`); for Reed–Solomon the
-- symbol space is `A = F` itself, so `[NoZeroSMulDivisors F F]` (a field has no zero divisors) is
-- automatic and no extra hypothesis is needed.
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {deg : ℕ} (domain : ι ↪ F)

/-- **The difference-stack residual for a Reed–Solomon code (PROVEN, GS-witness route).**

For `C = ReedSolomon.code domain deg`, under the unique-decoding regime `2·δ·n < δ_min(C)`, the
explicit GS-witness lower bound on the floor count discharges the abstract per-stack residual
`diffStackMCAResidualBelowUDR C δ` that `Errors.lean` carries as ABF26 Lemma 4.6's hard-direction
obligation.

This is the RS instantiation of `diffStackMCAResidualBelowUDR_of_epsCA_ge`: the GS-witness
hypothesis supplies the numeric dominance `⌊δ·n⌋/|F| ≤ ε_ca` (`floorCount_le_epsCA_of_gsWitness`),
and the abstract chaining lemma turns that into the residual. The `[NoZeroSMulDivisors F F]`
instance the chaining lemma needs is automatic for the field symbol space `A = F`.

**Genuine hypotheses.**
* `h_udr : 2·δ·n < δ_min(C)` — the unique-decoding regime (the paper's `δ < δ_min(C)/2`).
* `h_gs : GSWitnessLowerBound C δ ⌊δ·n⌋` — the BCIKS20-style explicit witness existence (a deep-hole
  word stack with `⌊δ·n⌋`-many good combiners), the faithful and *only* route to `(★)` for RS. -/
theorem diffStackMCAResidualBelowUDR_rs (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
      (Code.dist ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F)
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    diffStackMCAResidualBelowUDR (F := F) (A := F) (ReedSolomon.code domain deg) δ :=
  diffStackMCAResidualBelowUDR_of_epsCA_ge (ReedSolomon.code domain deg) δ h_udr
    (floorCount_le_epsCA_of_gsWitness
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ h_gs)

/-- **ABF26 Lemma 4.6 for Reed–Solomon codes (PROVEN reduction) — the issue's real goal.**

For `C = ReedSolomon.code domain deg`, in the unique-decoding regime `2·δ·n < δ_min(C)`, the full
equality `ε_mca(C, δ) = ε_ca(C, δ, δ)` holds, reduced to the **single** named GS-witness hypothesis
`GSWitnessLowerBound C δ ⌊δ·n⌋` (the BCIKS20 Prop 1.1-style witness existence for RS).

Proof: this is `epsMCA_eq_epsCA_below_udr_of_gsWitness` specialised to `A = F` (where the required
`[NoZeroSMulDivisors F F]` instance is automatic for the field symbol space). The hard direction
`ε_mca ≤ ε_ca` collapses the in-tree UDR upper bound `ε_mca ≤ max(ε_ca, ⌊δ·n⌋/|F|)` using the
GS-witness lower bound `⌊δ·n⌋/|F| ≤ ε_ca`; the easy direction `ε_ca ≤ ε_mca` is
`epsCA_le_epsMCA`. -/
theorem epsMCA_eq_epsCA_below_udr_rs (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
      (Code.dist ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F)
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ =
      epsCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ δ :=
  epsMCA_eq_epsCA_below_udr_of_gsWitness (ReedSolomon.code domain deg) δ h_udr h_gs

/-- The RS distance is `card ι − deg + 1` ([Reed–Solomon MDS], `ReedSolomon.dist_eq'`), so the UDR
hypothesis can be stated as the bare numeric inequality `2·δ·n < card ι − deg + 1`. This convenience
lemma rewrites that numeric form into the `Code.dist` form `diffStackMCAResidualBelowUDR_rs`
expects, so RS callers never need to unfold `Code.dist`. Requires `[NeZero deg]` and `deg ≤ card ι`
(the RS distance formula's hypotheses). -/
theorem diffStackMCAResidualBelowUDR_rs_of_two_mul_lt_card_sub [NeZero deg]
    (h_deg : deg ≤ Fintype.card ι) (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
      ((Fintype.card ι - deg + 1 : ℕ) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F)
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    diffStackMCAResidualBelowUDR (F := F) (A := F) (ReedSolomon.code domain deg) δ := by
  refine diffStackMCAResidualBelowUDR_rs domain δ ?_ h_gs
  rwa [ReedSolomon.dist_eq' (α := domain) h_deg]

/-- ABF26 Lemma 4.6 for Reed–Solomon with the UDR hypothesis stated numerically in the RS distance
`card ι − deg + 1` (via `ReedSolomon.dist_eq'`). See `epsMCA_eq_epsCA_below_udr_rs`. -/
theorem epsMCA_eq_epsCA_below_udr_rs_of_two_mul_lt_card_sub [NeZero deg]
    (h_deg : deg ≤ Fintype.card ι) (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
      ((Fintype.card ι - deg + 1 : ℕ) : ℝ≥0))
    (h_gs : GSWitnessLowerBound (F := F)
      ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ
      (Nat.floor (δ * (Fintype.card ι : ℝ≥0)))) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ =
      epsCA (F := F) (A := F)
        ((ReedSolomon.code domain deg : Submodule F (ι → F)) : Set (ι → F)) δ δ := by
  refine epsMCA_eq_epsCA_below_udr_rs domain δ ?_ h_gs
  rwa [ReedSolomon.dist_eq' (α := domain) h_deg]

end

end L46GS

end ProximityGap
