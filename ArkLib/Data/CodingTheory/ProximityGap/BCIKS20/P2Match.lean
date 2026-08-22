/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close

/-!
# BCIKS20 Appendix A.4 — P2 finale, part 2: the restricted Faà-di-Bruno match

Wipe-proof companion: works ONLY against the built `P2Close`/`HenselNumerator` oleans.

This file isolates the LAST genuinely unformalized content of BCIKS20 A.4 (`P2`) — the carved
core `RestrictedFaaDiBrunoMatch` of `P2Close.lean` — and proves it is *equivalent*, by the
PROVEN Newton-linearization defect reduction, to the single combinatorial vanishing of the
FULL (unrestricted) order-`(t+1)` Faà-di-Bruno sum of `eval (βHenselAssembled) Q`.  That full
vanishing is `FaaDiBrunoFullSumVanishes` here — the genuine "the assembled (A.1) numerator is a
root of `Q`" statement.  The match then follows *with no new axioms* from that single named
identity.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The **full** (unrestricted) order-`n` Faà-di-Bruno sum of `eval (βHenselAssembled) Q`:
the value of `coeff n (eval (βHenselAssembled) Q)` laid bare by the PROVEN expansion
`coeff_eval_Q_faaDiBruno`.  (Same shape as `restrictedFaaDiBrunoSum` but WITHOUT the
`(n) ∉ m` guard.) -/
def faaDiBrunoFullSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (n : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ ab ∈ Finset.antidiagonal n,
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
      * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                (valueMultiset (Finset.range i)),
          (Multiset.countPerms m) •
            ((m.map (fun j =>
              PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))

/-- `faaDiBrunoFullSum n` is exactly `coeff n (eval (βHenselAssembled) Q)` (PROVEN, from the
proven Faà-di-Bruno expansion `coeff_eval_Q_faaDiBruno`). -/
theorem faaDiBrunoFullSum_eq_coeff (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (n : ℕ) :
    faaDiBrunoFullSum H x₀ R hHyp n
      = PowerSeries.coeff n (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) := by
  rw [faaDiBrunoFullSum, coeff_eval_Q_faaDiBruno]

/-! ## The Newton split: full = restricted + ζ-linear response (PROVEN, axiom-clean)

The `(t+1) ∈ m` terms of the full Faà-di-Bruno sum collect, by the PROVEN Newton linearization
`coeff_succ_eval_defect_reduction`, into exactly `ζ · coeff (t+1) (βHenselAssembled)`; the
remaining `(t+1) ∉ m` terms are `restrictedFaaDiBrunoSum`.  No new content: this is the proven
defect reduction read through the two proven expansions. -/

/-- **The full/restricted Newton split (PROVEN, axiom-clean).**
`faaDiBrunoFullSum (t+1) = restrictedFaaDiBrunoSum t + ζ · coeff (t+1) (βHenselAssembled)`. -/
theorem faaDiBrunoFullSum_succ_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    faaDiBrunoFullSum H x₀ R hHyp (t + 1)
      = restrictedFaaDiBrunoSum H x₀ R hHyp t
        + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) := by
  rw [faaDiBrunoFullSum_eq_coeff, coeff_succ_eval_defect_reduction,
    trunc_defect_eq_restrictedFaaDiBrunoSum]

/-- **The full vanishing statement (the genuine A.4 combinatorial core).**
For every order, the FULL (unrestricted) order-`(t+1)` Faà-di-Bruno sum of
`eval (βHenselAssembled) Q` vanishes — i.e. the (A.1)-assembled numerator series is a root of `Q`
at every positive order.  This is the single genuinely-unformalized identity of BCIKS20 A.4. -/
def FaaDiBrunoFullSumVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, faaDiBrunoFullSum H x₀ R hHyp (t + 1) = 0

/-- The legacy explicit-successor-sum formulation of the same residual as
`FaaDiBrunoFullSumVanishes`.  This is the exact statement shape of
`faaDiBruno_succ_sum_eq_zero` in `HenselNumerator.lean`, recorded as a `Prop` so the old
frontier and the newer full-vanishing frontier can be compared without hiding any proof debt. -/
def FaaDiBrunoSuccSumsVanish (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ,
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        ∑ ab ∈ Finset.antidiagonal (t + 1),
          (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
          * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                    (ArkLib.PowerSeriesComposition.valueMultiset (Finset.range i)),
              (Multiset.countPerms m) •
                ((m.map (fun j =>
                  PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))) = 0

/-- The named full-vanishing residual and the legacy explicit successor-sum residual are
definitionally the same statement.  This bridge is axiom-clean; it does not consume the admitted
`faaDiBruno_succ_sum_eq_zero` theorem. -/
theorem fullVanishes_iff_succSumsVanish (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp ↔ FaaDiBrunoSuccSumsVanish H x₀ R hHyp := by
  rfl

/-- Compatibility bridge from the older explicit residual to the newer full-vanishing residual.
Its only non-kernel content is exactly the explicit hypothesis `FaaDiBrunoSuccSumZeroResidual`; the
equivalence above is axiom-clean. -/
theorem fullVanishes_of_faaDiBruno_succ_sum_eq_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (fullVanishes_iff_succSumsVanish H x₀ R hHyp).mpr
    (fun t => faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero t)

/-- **THE EQUIVALENCE (PROVEN, axiom-clean).**  The carved core `RestrictedFaaDiBrunoMatch` of
`P2Close.lean` is *exactly* the full-sum vanishing `FaaDiBrunoFullSumVanishes`, with the
difference accounted for entirely by the PROVEN Newton split.  Neither direction introduces any
new axiom: the `(t+1) ∈ m` terms are handled by `coeff_succ_eval_defect_reduction`. -/
theorem restrictedMatch_iff_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔ FaaDiBrunoFullSumVanishes H x₀ R hHyp := by
  constructor
  · intro hmatch t
    rw [faaDiBrunoFullSum_succ_eq, hmatch t]
    ring
  · intro hvan t
    have h := hvan t
    rw [faaDiBrunoFullSum_succ_eq] at h
    linear_combination h

/-- The carved core, OBTAINED from the full-vanishing identity (forward direction, PROVEN
axiom-clean). -/
theorem restrictedFaaDiBrunoMatch_of_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  (restrictedMatch_iff_fullVanishes H x₀ R hHyp).mpr hvan

/-! ## End-to-end: P2 closes from the single full-vanishing identity (PROVEN reductions)

Chaining the equivalence into `P2Close.lean`'s proven reductions: the full-vanishing identity
`FaaDiBrunoFullSumVanishes` (the genuine A.4 root statement) discharges the carved core, hence
the assembled series is the genuine Hensel root and the repaired lift identity holds for all
orders.  Everything else of P2 is PROVEN. -/

/-- **P2 root from the full-vanishing identity (PROVEN reduction).** -/
theorem assembledSeries_isRoot_of_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_match H x₀ R hHyp
    (restrictedFaaDiBrunoMatch_of_fullVanishes H x₀ R hHyp hvan)

/-- **`P2_closed` from the single full-vanishing identity (PROVEN reduction).**
The ENTIRE remaining mathematical content of BCIKS20 A.4's P2 is `FaaDiBrunoFullSumVanishes`
(equivalently `RestrictedFaaDiBrunoMatch`): given it, the assembled series is the genuine Hensel
root AND the repaired lift identity holds for all orders. -/
theorem P2_closed_of_fullVanishes (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp (restrictedFaaDiBrunoMatch_of_fullVanishes H x₀ R hHyp hvan)

/-- **Legacy P2 capstone from the explicit successor-sum residual.**
This is the compatibility endpoint for the older theorem
`faaDiBruno_succ_sum_eq_zero` in `HenselNumerator.lean`: the explicit successor-sum residual is the
only mathematical content consumed here, while every bridge from the explicit sums to the P2 root
and lift identity is proven above. -/
theorem P2_closed_of_faaDiBruno_succ_sum_eq_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_fullVanishes H x₀ R hHyp
    (fullVanishes_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero)

/-- The carved restricted Faà-di-Bruno match follows directly from the legacy explicit
successor-sum residual.  This is the tight compatibility form for callers that need the
`P2Close.lean` core rather than the final paired capstone. -/
theorem restrictedFaaDiBrunoMatch_of_faaDiBruno_succ_sum_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_of_fullVanishes H x₀ R hHyp
    (fullVanishes_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero)

/-- The assembled numerator series is a root of `Q` directly from the legacy explicit
successor-sum residual. -/
theorem assembledSeries_isRoot_of_faaDiBruno_succ_sum_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  (P2_closed_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero).1

/-- The repaired P2 lift identity, exposed per order, directly from the legacy explicit
successor-sum residual. -/
theorem βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  (P2_closed_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero).2 t

-- In-file axiom audit (edited, unbuilt source: must audit IN-FILE, not via import).
section AxiomAudit
#print axioms faaDiBrunoFullSum_eq_coeff
#print axioms faaDiBrunoFullSum_succ_eq
#print axioms fullVanishes_iff_succSumsVanish
#print axioms restrictedMatch_iff_fullVanishes
#print axioms restrictedFaaDiBrunoMatch_of_fullVanishes
#print axioms assembledSeries_isRoot_of_fullVanishes
#print axioms P2_closed_of_fullVanishes
#print axioms restrictedFaaDiBrunoMatch_of_faaDiBruno_succ_sum_eq_zero
#print axioms assembledSeries_isRoot_of_faaDiBruno_succ_sum_eq_zero
#print axioms βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero
end AxiomAudit

end BCIKS20.HenselNumerator
