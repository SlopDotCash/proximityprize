/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Research.ProximityGap.Hab25Johnson
import ArkLib.Research.ProximityGap.Hab25AlgebraicBridge
import ArkLib.Research.ProximityGap.Hab25MultiplicityBridge

/-!
# Hab25 Johnson numeric residual from S11 cardinality scaling

This file provides the final lightweight adapter from the proven S11 scaling bridge into the
Hab25 residual bundle's `JohnsonNumericBound` field (which is definitionally the full
`ε_mca` Johnson bound, see the honesty note in `Hab25Johnson.lean`). It does not prove the
m-multiplicity bad-scalar count; it only states the exact way that future cardinality bound,
together with the remaining real numerator comparison, discharges the named numeric residual.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap
open Classical NNReal Code Finset
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Constructor for the Hab25 numeric residual from cardinality data.** A uniform bound
`N` on the bad-scalar set of every word-stack, plus real arithmetic
`(N : ℝ) ≤ B` and `B / |F| ≤ johnsonBoundReal`, gives the exact `JohnsonNumericBound`
field consumed by `Hab25JohnsonResiduals`.

This is pure plumbing from the proven S11 scaling theorem into the residual bundle:
the hard theorem remains the m-multiplicity proof of the per-stack bad-scalar cardinality
bound and the closed-form numerator comparison. -/
theorem JohnsonNumericBound.of_card_le
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_card_le
      domain k η δ N B hB hNB hBdiv hN

/-- Natural-numerator constructor for the Hab25 numeric residual.  This is the common S11
endgame shape where the bad-scalar count bound and the real numerator are the same natural number
`N`, leaving only the scaled comparison `(N : ℝ) / |F| ≤ johnsonBoundReal`. -/
theorem JohnsonNumericBound.of_card_le_nat
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_card_le_nat
      domain k η δ N hNdiv hN

/-- **Constructor for the Hab25 numeric residual from algebraic covers.** If every stack's
actual bad-scalar set is covered by the `Edis` field of Hab25 algebraic data, and the proven
integer endgame bound `ell * n` is uniformly bounded by `N`, then the S11 scaling bridge gives
the exact `JohnsonNumericBound`.

The hard theorem remains producing the per-stack GS-over-`F(Z)` algebraic covers and the
closed-form numerator comparison. -/
theorem JohnsonNumericBound.of_algebraic_cover
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hη : 0 < η)
    (hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι₀ ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover
      domain k η δ N B hη hδ hB hNB hBdiv hAlg

/-- Natural-numerator constructor for the algebraic-cover Hab25 numeric residual. This is the
common endgame shape where the same natural `N` bounds `A.ℓ * n` and appears in the scaled
comparison `(N : ℝ) / |F| ≤ johnsonBoundReal`. -/
theorem JohnsonNumericBound.of_algebraic_cover_nat
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ)
    (hη : 0 < η)
    (hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι₀ ≤ N) :
    JohnsonNumericBound domain k η δ := by
  refine JohnsonNumericBound.of_algebraic_cover
    domain k η δ N (N : ℝ) hη hδ ?_ ?_ hNdiv hAlg
  · exact_mod_cast Nat.zero_le N
  · exact le_rfl

/-! ## Composition with the Hab25 consumers

Earlier revisions of this file also carried roughly forty wrappers
(`Hab25JohnsonResiduals.ofAlgebraicData_*`, `mca_johnson_of_algebraicData_*`,
`mcaLowerWitness_of_algebraicData_*`, the lattice threshold/bracket/adjacent variants, ...)
that each took an algebraic datum `A : Hab25JohnsonAlgebraicData` and fed it to
`Hab25JohnsonResiduals.ofAlgebraicData A (JohnsonNumericBound.of_* ...)`. Since
`mca_johnson_of_residuals` is exactly the `hNumeric` field, `A` was irrelevant to every one of
those conclusions (audit CW-B19-06), so they were removed. To reach the same endpoints, build
`JohnsonNumericBound` with one of the four constructors above and pass it (as
`JohnsonNumericBound` is definitionally the `ε_mca` bound) to the generic consumers such as
`GrandChallenges.MCALowerWitness.ofLe` and the `GrandChallengesLattice` threshold lemmas. -/

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_algebraic_cover_nat
