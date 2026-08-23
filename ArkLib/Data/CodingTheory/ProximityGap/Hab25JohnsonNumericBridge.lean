/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AlgebraicBridge
import ArkLib.Data.CodingTheory.ProximityGap.Hab25MultiplicityBridge

/-!
# Hab25 Johnson numeric residual from S11 cardinality scaling

This file provides the final lightweight adapter from the proven S11 scaling bridge into the
opened Hab25 residual bundle's `JohnsonNumericBound` field. It does not prove the
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

This is pure plumbing from the proven S11 scaling theorem into the opened residual bundle:
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

/-- **Full Hab25 residual bundle from algebraic data plus S11 count data.** If the
GS-over-`F(Z)` algebraic datum has already been supplied, then a uniform bad-scalar count
bound and the remaining real numerator comparison produce the complete
`Hab25JohnsonResiduals` bundle.

This is only residual packaging: it does not prove the GS algebraic datum, the per-stack
cardinality theorem, or the closed-form numerator comparison. -/
def Hab25JohnsonResiduals.ofAlgebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_card_le domain k η δ N B hB hNB hBdiv hN)

/-- Natural-numerator form of `Hab25JohnsonResiduals.ofAlgebraicData_card_le`.  It packages an
algebraic datum plus the S11 count bound when the numerator comparison is already stated with the
same natural `N` that bounds the bad-scalar count. -/
def Hab25JohnsonResiduals.ofAlgebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_card_le_nat domain k η δ N hNdiv hN)

/-- **Full Hab25 residual bundle from algebraic data plus per-stack algebraic covers.** This
combines an already-supplied GS-over-`F(Z)` datum with the algebraic-cover-to-S11 bridge:
per-stack covers of the actual bad scalars, a uniform `ell * n ≤ N` bound, and the remaining
real numerator comparison produce the complete `Hab25JohnsonResiduals` bundle.

This is only the final packaging edge for future GS-cover proofs; it does not construct the
covers or prove the closed-form numerator comparison. -/
def Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_algebraic_cover
      domain k η δ N B hη hδ hB hNB hBdiv hAlg)

/-- Natural-numerator form of `Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover`. -/
def Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (JohnsonNumericBound.of_algebraic_cover_nat
      domain k η δ N hη hδ hNdiv hAlg)

/-- **Hab25 Johnson bound from algebraic data plus S11 count data.** This is the direct
consumer-facing form of `Hab25JohnsonResiduals.ofAlgebraicData_card_le`: once an algebraic datum,
uniform bad-scalar cardinality bound, and numerator comparison are supplied, the Johnson-range
`ε_mca` bound follows. -/
theorem mca_johnson_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_card_le A N B hB hNB hBdiv hN)

/-- Natural-numerator form of `mca_johnson_of_algebraicData_card_le`.  This is the direct Hab25
Johnson bound when the S11 numerator comparison is already `(N : ℝ) / |F| ≤ johnsonBoundReal`. -/
theorem mca_johnson_of_algebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_card_le_nat A N hNdiv hN)

/-- **Hab25 Johnson bound from per-stack algebraic covers.** This composes the algebraic-cover
residual constructor with `mca_johnson_of_residuals`, exposing the final `ε_mca` bound directly
from the future GS-over-`F(Z)` cover target plus the remaining numerator comparison. -/
theorem mca_johnson_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover A N B hB hNB hBdiv hAlg)

/-- Natural-numerator form of `mca_johnson_of_algebraicData_algebraic_cover`. -/
theorem mca_johnson_of_algebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal
        (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ) :=
  mca_johnson_of_residuals domain k η δ hη hδ
    (Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover_nat A N hNdiv hAlg)

/-- **Grand-MCA lower witness from algebraic data plus S11 count data.** This is the
prize-facing consumer form of `Hab25JohnsonResiduals.ofAlgebraicData_card_le`: after the same
count/numerator inputs prove the Hab25 Johnson bound, any enclosing `ε*` bound produces an
`MCALowerWitness`. -/
def mcaLowerWitness_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  mcaLowerWitness_of_residuals domain k η δ ε_star hη hδ hδ_le_one
    (Hab25JohnsonResiduals.ofAlgebraicData_card_le A N B hB hNB hBdiv hN) hle

/-- Natural-numerator form of `mcaLowerWitness_of_algebraicData_card_le`. This is the
Grand-MCA lower-witness front door when the S11 numerator comparison is already stated as
`(N : ℝ) / |F| ≤ johnsonBoundReal`. -/
def mcaLowerWitness_of_algebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  mcaLowerWitness_of_residuals domain k η δ ε_star hη hδ hδ_le_one
    (Hab25JohnsonResiduals.ofAlgebraicData_card_le_nat A N hNdiv hN) hle

/-- **Grand-MCA lower witness from per-stack algebraic covers.** This is the direct lower-witness
consumer for the future GS-over-`F(Z)` cover target plus numerator comparison. -/
def mcaLowerWitness_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  mcaLowerWitness_of_residuals domain k η δ ε_star hη hδ hδ_le_one
    (Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover A N B hB hNB hBdiv hAlg) hle

/-- Natural-numerator form of `mcaLowerWitness_of_algebraicData_algebraic_cover`. -/
def mcaLowerWitness_of_algebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  mcaLowerWitness_of_residuals domain k η δ ε_star hη hδ hδ_le_one
    (Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover_nat A N hNdiv hAlg) hle

/-- **Grand-MCA threshold existence from algebraic data plus S11 count data.** This packages
`mcaLowerWitness_of_algebraicData_card_le` through the generic lattice threshold constructor,
so callers with the count/numerator inputs can enter the lattice layer without manually naming
the intermediate lower witness. -/
theorem mcaThresholdExists_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallengesLattice.mcaThresholdExists
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle)

/-- Natural-numerator form of `mcaThresholdExists_of_algebraicData_card_le`. -/
theorem mcaThresholdExists_of_algebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallengesLattice.mcaThresholdExists
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle)

/-- **Grand-MCA threshold existence from per-stack algebraic covers.** This is the
threshold-layer companion to `mcaLowerWitness_of_algebraicData_algebraic_cover`, preserving the
future GS-over-`F(Z)` cover and numerator comparison as explicit inputs. -/
theorem mcaThresholdExists_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallengesLattice.mcaThresholdExists
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle)

/-- Natural-numerator form of `mcaThresholdExists_of_algebraicData_algebraic_cover`. -/
theorem mcaThresholdExists_of_algebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    GrandChallengesLattice.mcaThresholdExists
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
  GrandChallengesLattice.mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle)

/-- The faithful MCA threshold created from algebraic data plus S11 count data satisfies the
MCA bound. This is the spec companion to `mcaThresholdExists_of_algebraicData_card_le`. -/
theorem mcaThreshold_spec_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.mcaSatisfies
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
      (GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne) :=
  GrandChallengesLattice.mcaThreshold_spec
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle)

/-- Natural-numerator form of `mcaThreshold_spec_of_algebraicData_card_le`. -/
theorem mcaThreshold_spec_of_algebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle
    GrandChallengesLattice.mcaSatisfies
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
      (GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne) :=
  GrandChallengesLattice.mcaThreshold_spec
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle)

/-- The faithful MCA threshold created from per-stack algebraic covers satisfies the MCA bound.
This is the spec companion to `mcaThresholdExists_of_algebraicData_algebraic_cover`. -/
theorem mcaThreshold_spec_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.mcaSatisfies
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
      (GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne) :=
  GrandChallengesLattice.mcaThreshold_spec
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle)

/-- Natural-numerator form of `mcaThreshold_spec_of_algebraicData_algebraic_cover`. -/
theorem mcaThreshold_spec_of_algebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.mcaSatisfies
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
      (GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne) :=
  GrandChallengesLattice.mcaThreshold_spec
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle)

/-- The Hab25 lower witness from algebraic data plus S11 count data gives a direct lower
bracket on the faithful MCA lattice threshold at `⌊δ * n⌋`. -/
theorem latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ hδ_le_one ≤
      GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne := by
  exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle)
    (mcaLowerWitness_of_algebraicData_card_le
      hδ_le_one A N B hB hNB hBdiv hN hle)

/-- Natural-numerator form of `latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le`. -/
theorem latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ hδ_le_one ≤
      GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne := by
  exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle)
    (mcaLowerWitness_of_algebraicData_card_le_nat
      hδ_le_one A N hNdiv hN hle)

/-- The Hab25 lower witness from per-stack algebraic covers gives a direct lower bracket on
the faithful MCA lattice threshold at `⌊δ * n⌋`. -/
theorem latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ hδ_le_one ≤
      GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne := by
  exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle)
    (mcaLowerWitness_of_algebraicData_algebraic_cover
      hδ_le_one A N B hB hNB hBdiv hAlg hle)

/-- Natural-numerator form of
`latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover`. -/
theorem latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover_nat
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ}
    (hδ_le_one : δ ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
        ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ hδ_le_one ≤
      GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne := by
  exact GrandChallengesLattice.MCALowerWitness_le_mcaThreshold
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle)
    (mcaLowerWitness_of_algebraicData_algebraic_cover_nat
      hδ_le_one A N hNdiv hAlg hle)

/-- Hab25 algebraic data plus S11 count data and a capacity-side `ε_ca` upper witness bracket
the faithful MCA lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_epsCAGt
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi := by
  refine ⟨?_, ?_⟩
  · exact latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle
  · exact GrandChallengesLattice.mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_of_algebraicData_card_le
        hδlo_le_one A N B hB hNB hBdiv hN hle)
      hhi hδhi

/-- Natural-numerator form of
`mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_epsCAGt`. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_card_le_nat_and_epsCAGt
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi := by
  refine ⟨?_, ?_⟩
  · exact latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle
  · exact GrandChallengesLattice.mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_of_algebraicData_card_le_nat
        hδlo_le_one A N hNdiv hN hle)
      hhi hδhi

/-- Hab25 per-stack algebraic covers and a capacity-side `ε_ca` upper witness bracket the
faithful MCA lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_epsCAGt
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi := by
  refine ⟨?_, ?_⟩
  · exact latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle
  · exact GrandChallengesLattice.mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_of_algebraicData_algebraic_cover
        hδlo_le_one A N B hB hNB hBdiv hAlg hle)
      hhi hδhi

/-- Natural-numerator form of
`mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_epsCAGt`. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_nat_and_epsCAGt
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi := by
  refine ⟨?_, ?_⟩
  · exact latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle
  · exact GrandChallengesLattice.mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_of_algebraicData_algebraic_cover_nat
        hδlo_le_one A N hNdiv hAlg hle)
      hhi hδhi

/-- Hab25 algebraic data plus S11 count data and any packaged upper witness bracket the
faithful MCA lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_upperWitness
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi :=
  GrandChallengesLattice.mcaThresholdLattice_bracketed
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle)
    (mcaLowerWitness_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle)
    whi hδhi

/-- Natural-numerator form of
`mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_upperWitness`. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_card_le_nat_and_upperWitness
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi :=
  GrandChallengesLattice.mcaThresholdLattice_bracketed
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle)
    (mcaLowerWitness_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle)
    whi hδhi

/-- Hab25 per-stack algebraic covers and any packaged upper witness bracket the faithful MCA
lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_upperWitness
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi :=
  GrandChallengesLattice.mcaThresholdLattice_bracketed
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle)
    (mcaLowerWitness_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle)
    whi hδhi

/-- Natural-numerator form of
`mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_upperWitness`. -/
theorem mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_nat_and_upperWitness
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one ≤
        GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne ∧
      GrandChallengesLattice.mcaThreshold
          (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne <
        GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi :=
  GrandChallengesLattice.mcaThresholdLattice_bracketed
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle)
    (mcaLowerWitness_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle)
    whi hδhi

/-- Hab25 algebraic data plus S11 count data and an adjacent packaged upper witness identify
the faithful MCA lattice threshold exactly. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_upperWitness_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one :=
  GrandChallengesLattice.mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle)
    whi hδhi hadj

/-- Natural-numerator form of
`mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_upperWitness_adjacent`. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_nat_and_upperWitness_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one :=
  GrandChallengesLattice.mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle)
    whi hδhi hadj

/-- Hab25 per-stack algebraic covers and an adjacent packaged upper witness identify the faithful
MCA lattice threshold exactly. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_upperWitness_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one :=
  GrandChallengesLattice.mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle)
    whi hδhi hadj

/-- Natural-numerator form of
`mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_upperWitness_adjacent`. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_nat_and_upperWitness_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star)
    (hδhi : whi.δ ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one :=
  GrandChallengesLattice.mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star
    (mcaLowerWitness_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle)
    whi hδhi hadj

/-- Capacity-side `ε_ca` adjacent upper data identifies the Hab25 count-data lattice threshold. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_epsCAGt_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le
      hδlo_le_one A N B hB hNB hBdiv hN hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one := by
  let whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
    GrandChallenges.MCAUpperWitness.ofEpsCAGt
      (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  have hδhi' : whi.δ ≤ 1 := by
    simpa [whi] using hδhi
  have hadj' :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi').val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1 := by
    simpa [whi] using hadj
  simpa [whi, hδhi'] using
    (mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_upperWitness_adjacent
      hδlo_le_one A N B hB hNB hBdiv hN hle whi hδhi' hadj')

/-- Natural-numerator form of
`mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_epsCAGt_adjacent`. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_nat_and_epsCAGt_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ_lo (u 0) (u 1) γ)
        Finset.univ).card ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_card_le_nat
      hδlo_le_one A N hNdiv hN hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one := by
  let whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
    GrandChallenges.MCAUpperWitness.ofEpsCAGt
      (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  have hδhi' : whi.δ ≤ 1 := by
    simpa [whi] using hδhi
  have hadj' :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi').val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1 := by
    simpa [whi] using hadj
  simpa [whi, hδhi'] using
    (mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_nat_and_upperWitness_adjacent
      hδlo_le_one A N hNdiv hN hle whi hδhi' hadj')

/-- Capacity-side `ε_ca` adjacent upper data identifies the Hab25 algebraic-cover lattice
threshold. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_epsCAGt_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover
      hδlo_le_one A N B hB hNB hBdiv hAlg hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one := by
  let whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
    GrandChallenges.MCAUpperWitness.ofEpsCAGt
      (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  have hδhi' : whi.δ ≤ 1 := by
    simpa [whi] using hδhi
  have hadj' :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi').val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1 := by
    simpa [whi] using hadj
  simpa [whi, hδhi'] using
    (mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_upperWitness_adjacent
      hδlo_le_one A N B hB hNB hBdiv hAlg hle whi hδhi' hadj')

/-- Natural-numerator form of
`mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_epsCAGt_adjacent`. -/
theorem mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_nat_and_epsCAGt_adjacent
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ_lo δ_hi ε_star : ℝ≥0}
    {hη : 0 < η}
    {hδ : CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.InJohnsonRange domain k η δ_lo}
    (hδlo_le_one : δ_lo ≤ 1)
    (A : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ)
    (N : ℕ)
    (hNdiv : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
    (hAlg : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ A' : Hab25JohnsonAlgebraicData domain k η δ_lo hη hδ,
        _root_.ProximityGap.hab25McaBadScalars domain k δ_lo u ⊆ A'.Edis ∧
          A'.ℓ * Fintype.card ι₀ ≤ N)
    (hle : ENNReal.ofReal
      (CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ_lo)
        ≤ (ε_star : ENNReal))
    (hhi :
      epsCA (F := F₀) (A := F₀) (ReedSolomon.code domain k : Set (ι₀ → F₀))
        δ_hi δ_hi > (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_hi hδhi).val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_of_algebraicData_algebraic_cover_nat
      hδlo_le_one A N hNdiv hAlg hle
    GrandChallengesLattice.mcaThreshold
        (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star hne =
      GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one := by
  let whi : GrandChallenges.MCAUpperWitness
      (ReedSolomon.code domain k : Set (ι₀ → F₀)) ε_star :=
    GrandChallenges.MCAUpperWitness.ofEpsCAGt
      (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  have hδhi' : whi.δ ≤ 1 := by
    simpa [whi] using hδhi
  have hadj' :
      (GrandChallengesLattice.latticeIndexOf (ι := ι₀) whi.δ hδhi').val =
        (GrandChallengesLattice.latticeIndexOf (ι := ι₀) δ_lo hδlo_le_one).val + 1 := by
    simpa [whi] using hadj
  simpa [whi, hδhi'] using
    (mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_nat_and_upperWitness_adjacent
      hδlo_le_one A N hNdiv hAlg hle whi hδhi' hadj')

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_algebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaLowerWitness_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaLowerWitness_of_algebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaLowerWitness_of_algebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaLowerWitness_of_algebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdExists_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdExists_of_algebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdExists_of_algebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdExists_of_algebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_spec_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_spec_of_algebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_spec_of_algebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_spec_of_algebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.latticeIndexOf_le_mcaThreshold_of_algebraicData_card_le_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.latticeIndexOf_le_mcaThreshold_of_algebraicData_algebraic_cover_nat
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_epsCAGt
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_card_le_nat_and_epsCAGt
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_epsCAGt
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_nat_and_epsCAGt
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_card_le_and_upperWitness
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_card_le_nat_and_upperWitness
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_and_upperWitness
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThresholdLattice_bracketed_of_algebraicData_algebraic_cover_nat_and_upperWitness
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_upperWitness_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_nat_and_upperWitness_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_upperWitness_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_nat_and_upperWitness_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_and_epsCAGt_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_card_le_nat_and_epsCAGt_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_and_epsCAGt_adjacent
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaThreshold_eq_latticeIndexOf_algebraicData_algebraic_cover_nat_and_epsCAGt_adjacent
