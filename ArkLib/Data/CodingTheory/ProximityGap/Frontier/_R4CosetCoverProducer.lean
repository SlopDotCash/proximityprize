/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

/-!
# R4 coset-cover producer for the direct `δ*` attack (#464)

The R4 route in the workbench says the non-BGK way to prove the lower pin is:

* show that, for every stack, the bad scalars are covered by only `K = O(1)` cyclotomic
  cosets/orbits;
* each such coset has size `S` (or at most `S`, typically `S = n / gcd(b-a,n)`);
* choose the prize budget so `K*S/q ≤ ε*`.

This file turns that route into the exact producer contract consumed by
`OpenCoreConditionalPin.WorstCaseIncidenceBounded`.  It does not assert that such a
cover exists; it proves that such a cover, if supplied by a future symmetric-function
rigidity theorem, is already enough to pin `δ ≤ δ*`.

The content is intentionally small and direct: no moment estimates, no Gauss sums, no
analytic number theory.  The only inequality is the finite-set union bound
`#bad ≤ #pieces * maxPieceSize`.
-/

open Finset
open scoped ENNReal NNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger Code

namespace ProximityGap.Frontier.R4CosetCover

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-- The bad-scalar set for one stack, in the exact form used by
`WorstCaseIncidenceBounded`. -/
noncomputable def badScalarSet (F A ι : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (C : Set (ι → A)) (δ : ℝ≥0)
    (u : WordStack A (Fin 2) ι) : Finset F :=
  Finset.univ.filter (fun γ : F => mcaEvent (F := F) C δ (u 0) (u 1) γ)

/-- **R4 cover certificate.**

For every stack, the bad scalars are covered by at most `K` finite pieces, each of
cardinality at most `S`.  In the intended R4 application, the pieces are the
`μ_{n'}`-cosets forced by dilation of the symmetric-function readout. -/
structure BadScalarCover (F A ι : Type) [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (C : Set (ι → A)) (δ : ℝ≥0) (K S : ℕ) where
  /-- The cover pieces for a stack. -/
  cover : WordStack A (Fin 2) ι → Finset (Finset F)
  /-- At most `K` pieces. -/
  cover_card_le : ∀ u, (cover u).card ≤ K
  /-- Every piece has size at most `S`. -/
  piece_card_le : ∀ u T, T ∈ cover u → T.card ≤ S
  /-- The bad scalars are contained in the union of the pieces. -/
  bad_subset_cover : ∀ u, badScalarSet F A ι C δ u
    ⊆ (cover u).biUnion (fun T => T)

/-- **Cover-to-count.**  If a stack's bad scalars are covered by at most `K` pieces
of size at most `S`, then its bad-scalar count is at most `K*S`. -/
theorem badScalarSet_card_le_of_cover {C : Set (ι → A)} {δ : ℝ≥0} {K S : ℕ}
    (hcover : BadScalarCover F A ι C δ K S)
    (u : WordStack A (Fin 2) ι) :
    (badScalarSet F A ι C δ u).card ≤ K * S := by
  classical
  calc
    (badScalarSet F A ι C δ u).card
        ≤ ((hcover.cover u).biUnion (fun T => T)).card :=
          by simpa using Finset.card_le_card (hcover.bad_subset_cover u)
    _ ≤ ∑ T ∈ hcover.cover u, T.card := Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ hcover.cover u, S := by
          exact Finset.sum_le_sum (fun T hT => hcover.piece_card_le u T hT)
    _ = (hcover.cover u).card * S := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ K * S := Nat.mul_le_mul_right S (hcover.cover_card_le u)

/-- **R4 cover producer for the open core.**

A uniform `K`-by-`S` cover of the bad scalars for every stack discharges
`WorstCaseIncidenceBounded` with budget `K*S`. -/
theorem worstCaseIncidenceBounded_of_badScalarCover
    (C : Set (ι → A)) {δ : ℝ≥0} {K S : ℕ}
    (hcover : BadScalarCover F A ι C δ K S) :
    OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := A) C δ (K * S) := by
  intro u
  exact badScalarSet_card_le_of_cover hcover u

/-- **R4 cover producer for the `δ*` lower pin.**

If the future symmetric-function/coset-rigidity theorem supplies a uniform cover by
`K` pieces of size `S`, and the normalized cover budget `K*S/q` is within `ε*`,
then `δ ≤ mcaDeltaStar C ε*`. -/
theorem worstCaseIncidence_pin_of_badScalarCover
    (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {K S : ℕ}
    (hδ : δ ≤ 1)
    (hcover : BadScalarCover F A ι C δ K S)
    (hbudget : ((K * S : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar :=
  OpenCoreConditionalPin.worstCaseIncidence_pin (F := F) (A := A) C εstar hδ
    (worstCaseIncidenceBounded_of_badScalarCover (F := F) (A := A) C hcover)
    hbudget

/-- Budget-specialized form: a `K`-by-`S` cover pins the radius for target error
`ε* = K*S/q`. -/
theorem worstCaseIncidence_pin_budget_of_badScalarCover
    (C : Set (ι → A)) {δ : ℝ≥0} {K S : ℕ}
    (hδ : δ ≤ 1)
    (hcover : BadScalarCover F A ι C δ K S) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C
      (((K * S : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  worstCaseIncidence_pin_of_badScalarCover (F := F) (A := A) C _ hδ hcover le_rfl

end ProximityGap.Frontier.R4CosetCover

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.R4CosetCover.badScalarSet_card_le_of_cover
#print axioms ProximityGap.Frontier.R4CosetCover.worstCaseIncidenceBounded_of_badScalarCover
#print axioms ProximityGap.Frontier.R4CosetCover.worstCaseIncidence_pin_of_badScalarCover
#print axioms ProximityGap.Frontier.R4CosetCover.worstCaseIncidence_pin_budget_of_badScalarCover
