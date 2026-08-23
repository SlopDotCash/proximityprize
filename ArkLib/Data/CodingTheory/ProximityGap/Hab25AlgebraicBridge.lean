/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson
import ArkLib.Data.CodingTheory.ProximityGap.Hab25MultiplicityBridge

/-!
# Hab25 algebraic-data cover to S11 cardinality bridge

`Hab25Johnson.lean` exposes the opened Hab25 algebraic data and proves the integer endgame
`Hab25JohnsonAlgebraicData.disagree_card_le`: the residual factor/Hensel cover gives
`|Edis| ≤ ell * n`.

`Hab25MultiplicityBridge.lean` exposes the S11 scaling theorem in the shape needed by the
public Johnson front doors: a uniform per-stack bad-scalar cardinality bound gives
`epsMCA ≤ johnsonBoundReal`.

This file stitches those two checked pieces together.  It does not construct the
GS-over-`F(Z)` factorisation/Hensel data; it says that once each stack's actual bad scalars
are covered by the `Edis` field of such data, the existing S11 bridge can be applied directly.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Classical Finset NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The actual bad-scalar finset for one Reed-Solomon word-stack at radius `δ`. -/
noncomputable def hab25McaBadScalars (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) ι) : Finset F :=
  Finset.univ.filter
    (fun γ : F =>
      mcaEvent ((ReedSolomon.code domain k : Set (ι → F))) δ (u 0) (u 1) γ)

/-- One Hab25 algebraic-data cover bounds the actual bad scalars for a fixed word stack by
the algebraic endgame budget `ell * n`. -/
theorem hab25_badScalars_card_le_of_algebraic_data_cover
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (u : WordStack F (Fin 2) ι)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (hcover : hab25McaBadScalars domain k δ u ⊆ A.Edis) :
    (hab25McaBadScalars domain k δ u).card ≤ A.ℓ * Fintype.card ι :=
  le_trans (Finset.card_le_card hcover)
    (Hab25JohnsonAlgebraicData.disagree_card_le A)

/-- A one-stack Hab25 algebraic-data cover also gives any larger advertised cardinality
budget `N`. -/
theorem hab25_badScalars_card_le_of_algebraic_data_cover_le
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (N : ℕ)
    (u : WordStack F (Fin 2) ι)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (hcover : hab25McaBadScalars domain k δ u ⊆ A.Edis)
    (hAN : A.ℓ * Fintype.card ι ≤ N) :
    (hab25McaBadScalars domain k δ u).card ≤ N :=
  le_trans
    (hab25_badScalars_card_le_of_algebraic_data_cover
      domain k η δ hη hδ u A hcover)
    hAN

/-- If every stack's actual bad-scalar set is covered by the `Edis` field of Hab25 algebraic
data whose integer endgame bound is at most `N`, then the S11 per-stack cardinality hypothesis
holds.

The hard residual remains the `hAlg` input: producing the factor/Hensel data and proving that
its `Edis` covers the actual bad scalars for each stack. -/
theorem hab25_badScalars_card_le_of_algebraic_cover
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (N : ℕ)
    (hAlg : ∀ u : WordStack F (Fin 2) ι,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι ≤ N) :
    ∀ u : WordStack F (Fin 2) ι,
      (hab25McaBadScalars domain k δ u).card ≤ N := by
  intro u
  obtain ⟨A, hcover, hAN⟩ := hAlg u
  exact hab25_badScalars_card_le_of_algebraic_data_cover_le
    domain k η δ hη hδ N u A hcover hAN

/-- Hab25 algebraic-data covers feed the proven S11 scaling theorem and therefore the exact
Johnson numeric inequality. -/
theorem epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F : ℝ) ≤ johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F (Fin 2) ι,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι ≤ N) :
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal (johnsonBoundReal domain k η δ) := by
  have hCard := hab25_badScalars_card_le_of_algebraic_cover
    domain k η δ hη hδ N hAlg
  exact epsMCA_rs_le_johnsonBoundReal_of_card_le domain k η δ N B hB hNB hBdiv
    (fun u => by simpa [hab25McaBadScalars] using hCard u)

/-- Hab25 algebraic-data covers feed the public BCHKS25/Hab25 T4.12 front door after the
remaining real numerator comparison. -/
theorem rs_epsMCA_johnson_range_bchks25_of_algebraic_cover
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F : ℝ) ≤ johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F (Fin 2) ι,
      ∃ A : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        hab25McaBadScalars domain k δ u ⊆ A.Edis ∧
          A.ℓ * Fintype.card ι ≤ N) :
    CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη
      (by
        simpa [CodingTheory.rs_epsMCA_johnson_range_condition, InJohnsonRange] using hδ) :=
  CodingTheory.rs_epsMCA_johnson_range_bchks25_of_bound domain k η δ hη
    (by
      simpa [CodingTheory.rs_epsMCA_johnson_range_condition, InJohnsonRange] using hδ)
    (epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover
      domain k η δ N B hη hδ hB hNB hBdiv hAlg)

end ProximityGap

#print axioms ProximityGap.hab25_badScalars_card_le_of_algebraic_data_cover
#print axioms ProximityGap.hab25_badScalars_card_le_of_algebraic_data_cover_le
#print axioms ProximityGap.hab25_badScalars_card_le_of_algebraic_cover
#print axioms ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover
#print axioms ProximityGap.rs_epsMCA_johnson_range_bchks25_of_algebraic_cover
