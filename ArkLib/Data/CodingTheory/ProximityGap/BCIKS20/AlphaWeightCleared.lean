/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# Cleared base wrappers for the BCIKS20 Appendix-A weight invariant

`AlphaWeight.lean` contains the corrected order-zero cleared predicates. This small companion keeps
fixed-base convenience wrappers out of that near-cap file.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Package the proved beta-side base weight bound into the corrected cleared div-weight
predicate. -/
theorem DivWeightLe_zero_cleared.of_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  DivWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH
    (βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD)

/-- Standalone spelling of the corrected cleared div-weight base witness. -/
theorem divWeight_zero_cleared_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  DivWeightLe_zero_cleared.of_fixed H x₀ R hHyp hH hd hD

/-- Div-weight-oriented symmetry for the corrected cleared base alpha/div-weight equivalence. -/
theorem divWeight_zero_cleared_iff_alphaWeight_zero_cleared
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D ↔
      AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  (alphaWeight_zero_cleared_iff_divWeight_zero_cleared H x₀ R hHyp hH D).symm

/-- Corrected case split for the alpha-side P1 residual: the order-zero target is the
cleared-base predicate, while successors retain the original carved regularity targets. -/
def AlphaGenuineRegularWeightLe_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D ∧
    ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t

/-- Corrected case split for the div-weight P1 residual: the order-zero target is the
cleared-base predicate, while successors retain the original divisibility targets. -/
def DivWeightLe_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  DivWeightLe_zero_cleared H x₀ R hHyp hH D ∧
    ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t

/-- Assemble the corrected alpha-side case split from its cleared base and successor cases. -/
theorem AlphaGenuineRegularWeightLe_clearedBaseCases.of_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D :=
  ⟨h0, hsucc⟩

/-- Project the corrected alpha-side cleared base case. -/
theorem AlphaGenuineRegularWeightLe_clearedBaseCases.zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  hα.1

/-- Project a corrected alpha-side successor case. -/
theorem AlphaGenuineRegularWeightLe_clearedBaseCases.succ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  hα.2 t

/-- Assemble the corrected div-weight case split from its cleared base and successor cases. -/
theorem DivWeightLe_clearedBaseCases.of_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (h0 : DivWeightLe_zero_cleared H x₀ R hHyp hH D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D :=
  ⟨h0, hsucc⟩

/-- Project the corrected div-weight cleared base case. -/
theorem DivWeightLe_clearedBaseCases.zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  hdiv.1

/-- Project a corrected div-weight successor case. -/
theorem DivWeightLe_clearedBaseCases.succ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    DivWeightLe_succ H x₀ R hHyp hH D t :=
  hdiv.2 t

/-- Convert corrected alpha-side cases to corrected div-weight cases using only successor-order
lift identities. The cleared base is transported by the corrected base equivalence. -/
theorem DivWeightLe_clearedBaseCases.of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D := by
  refine DivWeightLe_clearedBaseCases.of_cases H x₀ R hHyp hH D ?_ ?_
  · exact DivWeightLe_zero_cleared.of_alphaWeight_zero_cleared H x₀ R hHyp hH hα.1
  · intro t
    exact DivWeightLe_succ.of_alphaWeight_succ H x₀ R hHyp hH D t
      (hliftSucc t) (hα.2 t)

/-- Convert corrected div-weight cases to corrected alpha-side cases using only successor-order
lift identities. The cleared base is transported by the corrected base equivalence. -/
theorem AlphaGenuineRegularWeightLe_clearedBaseCases.of_divWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D := by
  refine AlphaGenuineRegularWeightLe_clearedBaseCases.of_cases H x₀ R hHyp hH D ?_ ?_
  · exact AlphaGenuineRegularWeightLe_zero_cleared.of_divWeight_zero_cleared
      H x₀ R hHyp hH hdiv.1
  · intro t
    exact AlphaGenuineRegularWeightLe_succ.of_divWeight_succ H x₀ R hHyp hH D t
      (hliftSucc t) (hdiv.2 t)

/-- Under successor-order lift identities, the corrected alpha-side and div-weight case splits are
equivalent. The order-zero leg uses the corrected cleared-base equivalence, not the false
un-cleared base case. -/
theorem alphaWeight_clearedBaseCases_iff_divWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      DivWeightLe_clearedBaseCases H x₀ R hHyp hH D :=
  ⟨DivWeightLe_clearedBaseCases.of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH D hliftSucc,
    AlphaGenuineRegularWeightLe_clearedBaseCases.of_divWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH D hliftSucc⟩

/-- Build the repaired alpha-side case split from the proved corrected base case and successor
residuals. -/
theorem AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D :=
  AlphaGenuineRegularWeightLe_clearedBaseCases.of_cases H x₀ R hHyp hH D
    (AlphaGenuineRegularWeightLe_zero_cleared.of_fixed H x₀ R hHyp hH hd hD) hsucc

/-- With the corrected base case fixed, the repaired alpha-side case split is exactly its
successor family. -/
theorem alphaWeight_clearedBaseCases_iff_successors_of_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  ⟨fun hα => hα.2,
    AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD⟩

/-- Build the repaired div-weight case split from the proved corrected base case and successor
residuals. -/
theorem DivWeightLe_clearedBaseCases.of_fixed_successors
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D :=
  DivWeightLe_clearedBaseCases.of_cases H x₀ R hHyp hH D
    (DivWeightLe_zero_cleared.of_fixed H x₀ R hHyp hH hd hD) hsucc

/-- With the corrected base case fixed, the repaired div-weight case split is exactly its
successor family. -/
theorem divWeight_clearedBaseCases_iff_successors_of_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  ⟨fun hdiv => hdiv.2,
    DivWeightLe_clearedBaseCases.of_fixed_successors H x₀ R hHyp hH hd hD⟩

/-- Lift the pointwise successor alpha/div-weight equivalence to the whole successor family. -/
theorem alphaWeight_successors_iff_divWeight_successors_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    (∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t := by
  constructor
  · intro hα t
    exact (alphaWeight_succ_iff_divWeight_succ_of_succLift
      H x₀ R hHyp hH D hliftSucc t).1 (hα t)
  · intro hdiv t
    exact (alphaWeight_succ_iff_divWeight_succ_of_succLift
      H x₀ R hHyp hH D hliftSucc t).2 (hdiv t)

/-- With the corrected alpha-side base fixed, the repaired alpha case split is equivalent to the
div-weight successor family under successor-order lift identities. -/
theorem alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fixed_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  (alphaWeight_clearedBaseCases_iff_successors_of_fixed
    H x₀ R hHyp hH hd hD).trans
    (alphaWeight_successors_iff_divWeight_successors_succLift
      H x₀ R hHyp hH D hliftSucc)

/-- With the corrected div-weight base fixed, the repaired div-weight case split is equivalent to
the alpha-side successor family under successor-order lift identities. -/
theorem divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fixed_succLift
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  (divWeight_clearedBaseCases_iff_successors_of_fixed H x₀ R hHyp hH hd hD).trans
    (alphaWeight_successors_iff_divWeight_successors_succLift
      H x₀ R hHyp hH D hliftSucc).symm

/-- Structured beta-weight bound from the repaired cleared-base div-weight case split.  The
zero order uses the corrected cleared base directly; successor orders use the existing
divisibility factors. -/
theorem βHensel_weight_structured_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (l : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
      ≤ WithBot.some
          (1 + (l + 1) * (H.leadingCoeff).natDegree
            + (2 * l - 1)
              * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
  cases l with
  | zero =>
      exact (DivWeightLe_zero_cleared.betaWeight H x₀ R hHyp hH hdiv.1).trans
        (by exact_mod_cast
          (by omega :
            1 ≤ 1 + (0 + 1) * (H.leadingCoeff).natDegree
              + (2 * 0 - 1)
                * ((Bivariate.natDegreeY R - 1)
                  * (D - Bivariate.natDegreeY H + 1))))
  | succ t =>
      obtain ⟨a, hfact, ha_wt⟩ := hdiv.2 t
      rw [hfact]
      refine (weight_Λ_over_𝒪_mul_le H hH hDH _ _).trans ?_
      refine le_trans (add_le_add (weight_Λ_over_𝒪_mul_le H hH hDH _ _) (le_refl _)) ?_
      have hW_pow : weight_Λ_over_𝒪 hH ((W𝒪 H) ^ (t + 1 + 1)) D
          ≤ WithBot.some ((t + 1 + 1) * (H.leadingCoeff).natDegree) := by
        refine (weight_Λ_over_𝒪_pow_le H hH hDH (W𝒪 H) (t + 1 + 1)).trans ?_
        exact nsmul_withBot_le (t + 1 + 1) _ (weight_Λ_over_𝒪_W H hH hDH)
      have hξ_pow : weight_Λ_over_𝒪 hH
            ((ClaimA2.ξ x₀ R H hHyp) ^ (2 * (t + 1) - 1)) D
          ≤ WithBot.some
              ((2 * (t + 1) - 1)
                * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) := by
        refine (weight_Λ_over_𝒪_pow_le H hH hDH (ClaimA2.ξ x₀ R H hHyp)
          (2 * (t + 1) - 1)).trans ?_
        exact nsmul_withBot_le (2 * (t + 1) - 1) _ hξ
      refine le_trans (add_le_add (add_le_add ha_wt hW_pow) hξ_pow) ?_
      rw [← WithBot.coe_add, ← WithBot.coe_add]

/-- Prefix structured invariant from the repaired cleared-base div-weight case split. -/
theorem βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  intro l _hl
  exact βHensel_weight_structured_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdiv hξ l

/-- Prefix structured invariant from repaired cleared-base div-weight cases, with the `ξ` bound
discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Prefix structured invariant from the repaired alpha-side cleared-base cases, transported to the
div-weight side by successor-order lift identities. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH
    (DivWeightLe_clearedBaseCases.of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH D hliftSucc hα)
    hξ k

/-- Prefix structured invariant from repaired alpha-side cleared-base cases, with the `ξ` bound
discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hliftSucc hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Loose P1 beta-weight bound from the repaired cleared-base div-weight case split. -/
theorem βHensel_weight_bound_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hstructured := βHensel_weight_structured_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdiv hξ t
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-- Loose P1 beta-weight bound from repaired cleared-base div-weight cases, with the `ξ` bound
discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHensel_weight_bound_of_divWeight_clearedBaseCases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- Loose P1 beta-weight bound from repaired alpha-side cleared-base cases, transported by
successor-order lift identities. -/
theorem βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight_clearedBaseCases H x₀ R hHyp hH hDH
    hdR2 hdHR hW
    (DivWeightLe_clearedBaseCases.of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH D hliftSucc hα)
    hξ t

/-- Loose P1 beta-weight bound from repaired alpha-side cleared-base cases, with the `ξ` bound
discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hdR2 hdHR hW hliftSucc hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-! ### The fully-cleared all-orders weight predicate (`natDegreeY R`-budget)

The cleared base machinery above repairs only the order-`0` face. This section assembles the
base-cleared and ALL successor-cleared targets into one predicate with the genuine
`natDegreeY R`-budget `(2t+1)·natDegreeY R·D`, and shows that — unlike the un-cleared
`AlphaGenuineRegularWeightLe`, false for non-monic `H` — the fully-cleared predicate carries NO
divisibility/regularity content at any order: it is EXACTLY the per-order loose weight-bound family
on `βHensel`, valid for general (possibly non-monic) `H`. The witness at every order is
`βHensel _` itself (kept integral by clearing the `W^{t+1}·ξ^{2t-1}` denominator), so the cleared
#138 invariant reduces to PURELY the weight wall. -/

/-- **The fully-cleared all-orders P1 weight predicate (`natDegreeY R`-budget).**
At order `0` the cleared base coefficient `W · αGenuine 0 = T` has an `𝒪`-witness of
`Λ_𝒪`-weight `≤ 1`; at each successor order `t+1` the fully-cleared coefficient
`αGenuine (t+1)·W^{t+2}·ξ^{2t+1}` has an `𝒪`-witness of weight `≤ (2(t+1)+1)·natDegreeY R·D`.
Clearing keeps the witness `βHensel _` integral at every order, so this predicate carries NO
`α₀ = T/W` integrality obstruction (the obstruction that makes the un-cleared invariant false for
non-monic `H`). -/
def FullyClearedWeightLe (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D ∧
    ∀ t : ℕ, AlphaGenuineRegularWeightLe_succ_cleared H x₀ R hHyp hH D t
      ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D)

/-- **The fully-cleared predicate carries NO divisibility content: it is EXACTLY the per-order
loose weight bounds on `βHensel`.**  Given the per-order lift identities (P2, automatic in the
monic regime via `P2_closed_of_leadingCoeff_one`), `FullyClearedWeightLe` is logically equivalent
to `Λ_𝒪(βHensel 0) ≤ 1` together with the successor weight family
`∀ t, Λ_𝒪(βHensel (t+1)) ≤ (2(t+1)+1)·natDegreeY R·D`.  This is the honest content of the cleared
restatement: clearing the `W^{t+1}·ξ^{2t-1}` denominator removes the `α₀ = T/W` regularity
obstruction at every order, so the cleared #138 reduces to PURELY the weight wall (no integrality
residual), for general `H`. -/
theorem fullyClearedWeightLe_iff_betaWeights (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) :
    FullyClearedWeightLe H x₀ R hHyp hH D ↔
      (weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 ∧
        ∀ t : ℕ, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp (t + 1)) D
          ≤ WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D)) := by
  constructor
  · rintro ⟨h0, hsucc⟩
    refine ⟨(alphaWeight_zero_cleared_iff_betaWeight_zero H x₀ R hHyp hH D).1 h0, fun t => ?_⟩
    obtain ⟨a, ha_eq, ha_wt⟩ := hsucc t
    have hβ : a = βHensel H x₀ R hHyp (t + 1) := by
      apply embeddingOf𝒪Into𝕃_injective hH
      rw [ha_eq, hlift t]
    simpa [hβ] using ha_wt
  · rintro ⟨h0, hsucc⟩
    refine ⟨(alphaWeight_zero_cleared_iff_betaWeight_zero H x₀ R hHyp hH D).2 h0, fun t => ?_⟩
    exact AlphaGenuineRegularWeightLe_succ_cleared.of_lift H x₀ R hHyp hH t (hlift t) (hsucc t)

/-- **The fully-cleared base case is UNCONDITIONAL.**  `βHensel 0 = mk X` discharges the cleared
base coefficient directly (no carve, no divisibility), for general `H` with `2 ≤ deg H`,
`D ≤ deg H`. -/
theorem fullyClearedWeightLe_base (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  AlphaGenuineRegularWeightLe_zero_cleared.of_fixed H x₀ R hHyp hH hd hD

/-- **Reduction of the fully-cleared all-orders predicate to its successor weight bounds.**
The base case is discharged unconditionally (`fullyClearedWeightLe_base`); the only remaining
content is the per-order successor weight bound on `βHensel (t+1)` — the documented per-term WALL —
with the genuine `natDegreeY R`-budget. Valid for general (possibly non-monic) `H`. -/
theorem fullyClearedWeightLe_of_succ_betaWeights (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hsucc : ∀ t : ℕ, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp (t + 1)) D
          ≤ WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D)) :
    FullyClearedWeightLe H x₀ R hHyp hH D :=
  ⟨fullyClearedWeightLe_base H x₀ R hHyp hH hd hD,
    fun t => AlphaGenuineRegularWeightLe_succ_cleared.of_lift H x₀ R hHyp hH t (hlift t) (hsucc t)⟩

/-- Project the order-zero beta-weight bound from the fully-cleared predicate. -/
theorem FullyClearedWeightLe.betaWeight_zero
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hfull : FullyClearedWeightLe H x₀ R hHyp hH D) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 :=
  ((fullyClearedWeightLe_iff_betaWeights H x₀ R hHyp hH D hlift).1 hfull).1

/-- Project a successor beta-weight bound from the fully-cleared predicate. This is the direct
consumer API for the remaining per-order weight wall, without unpacking the equivalence theorem. -/
theorem FullyClearedWeightLe.succ_betaWeight
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hfull : FullyClearedWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp (t + 1)) D
      ≤ WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D) :=
  ((fullyClearedWeightLe_iff_betaWeights H x₀ R hHyp hH D hlift).1 hfull).2 t

/-- Forward projection of the fully-cleared predicate to both beta-weight families. -/
theorem FullyClearedWeightLe.betaWeights
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hfull : FullyClearedWeightLe H x₀ R hHyp hH D) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1 ∧
      ∀ t : ℕ, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp (t + 1)) D
        ≤ WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D) :=
  (fullyClearedWeightLe_iff_betaWeights H x₀ R hHyp hH D hlift).1 hfull

/-- Build the fully-cleared predicate from the projected beta-weight family shape. -/
theorem FullyClearedWeightLe.of_betaWeights
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp (t + 1)) D
      ≤ WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D)) :
    FullyClearedWeightLe H x₀ R hHyp hH D :=
  (fullyClearedWeightLe_iff_betaWeights H x₀ R hHyp hH D hlift).2 ⟨h0, hsucc⟩

end AlphaWeight
end BCIKS20.HenselNumerator

namespace BCIKS20.HenselNumerator.AlphaWeight

#print axioms DivWeightLe_zero_cleared.of_fixed
#print axioms divWeight_zero_cleared_fixed
#print axioms divWeight_zero_cleared_iff_alphaWeight_zero_cleared
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases
#print axioms DivWeightLe_clearedBaseCases
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases.of_cases
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases.zero
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases.succ
#print axioms DivWeightLe_clearedBaseCases.of_cases
#print axioms DivWeightLe_clearedBaseCases.zero
#print axioms DivWeightLe_clearedBaseCases.succ
#print axioms DivWeightLe_clearedBaseCases.of_alphaWeight_clearedBaseCases_succLift
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases.of_divWeight_clearedBaseCases_succLift
#print axioms alphaWeight_clearedBaseCases_iff_divWeight_clearedBaseCases_succLift
#print axioms AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
#print axioms alphaWeight_clearedBaseCases_iff_successors_of_fixed
#print axioms DivWeightLe_clearedBaseCases.of_fixed_successors
#print axioms divWeight_clearedBaseCases_iff_successors_of_fixed
#print axioms alphaWeight_successors_iff_divWeight_successors_succLift
#print axioms alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fixed_succLift
#print axioms divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fixed_succLift
#print axioms βHensel_weight_structured_of_divWeight_clearedBaseCases
#print axioms βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases
#print axioms βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases'
#print axioms βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift
#print axioms βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift'
#print axioms βHensel_weight_bound_of_divWeight_clearedBaseCases
#print axioms βHensel_weight_bound_of_divWeight_clearedBaseCases'
#print axioms βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift
#print axioms βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift'
#print axioms FullyClearedWeightLe
#print axioms fullyClearedWeightLe_iff_betaWeights
#print axioms fullyClearedWeightLe_base
#print axioms fullyClearedWeightLe_of_succ_betaWeights
#print axioms FullyClearedWeightLe.betaWeight_zero
#print axioms FullyClearedWeightLe.succ_betaWeight
#print axioms FullyClearedWeightLe.betaWeights
#print axioms FullyClearedWeightLe.of_betaWeights

end BCIKS20.HenselNumerator.AlphaWeight
