/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# BCIKS20 Appendix A.4 — P2 finale: the truncated-defect Faà-di-Bruno restriction

Wipe-proof companion file: works ONLY against the built `HenselNumerator` olean.

This file re-derives the wiped w14 lemma `trunc_defect_eq_faaDiBruno_assembled_restricted`
(STEP 1, fully PROVEN) and carves the final residual `trunc_defect_cancel_assembled` (STEP 2) to
the single named combinatorial core `RestrictedFaaDiBrunoMatch`, from which the entire remaining
content of P2 (root + lift identity) follows by the imported, PROVEN reductions.
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

/-! ## STEP 0 — value-multiset bookkeeping -/

/-- A part of a multiset with `m.sum ≤ t+1` and `(t+1) ∉ m` is `≤ t`. -/
theorem part_le_of_notMem_succ {t : ℕ} {m : Multiset ℕ} (hsum : m.sum ≤ t + 1)
    (hnotmem : (t + 1) ∉ m) {l : ℕ} (hl : l ∈ m) : l ≤ t := by
  have hle : l ≤ m.sum := Multiset.le_sum_of_mem hl
  have hne : l ≠ t + 1 := fun h => hnotmem (h ▸ hl)
  omega

/-- **Product vanishing on the killed terms.**  If `(t+1) ∈ m` then the truncated coefficient
product over `m` is `0`, because the `(t+1)`-coefficient of the `t`-truncation is `0`. -/
theorem prod_map_coeff_trunc_eq_zero_of_mem (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) {m : Multiset ℕ} (hmem : (t + 1) ∈ m) :
    (m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod = 0 := by
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  exact ⟨t + 1, hmem, coeff_βHenselTrunc_succ H x₀ R hHyp t⟩

/-- **Product agreement on the surviving terms.**  If `m.sum ≤ t+1` and `(t+1) ∉ m`, every part is
`≤ t`, so the truncated and assembled coefficient products over `m` coincide. -/
theorem prod_map_coeff_trunc_eq_assembled_of_notMem (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) {m : Multiset ℕ}
    (hsum : m.sum ≤ t + 1) (hnotmem : (t + 1) ∉ m) :
    (m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod
      = (m.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod := by
  congr 1
  refine Multiset.map_congr rfl (fun l hl => ?_)
  exact coeff_βHenselTrunc_of_le H x₀ R hHyp (part_le_of_notMem_succ hsum hnotmem hl)

/-- Every value-multiset in the image `(finsuppAntidiag (range i) s).image (valueMultiset …)`
has multiset-sum exactly `s`. -/
theorem image_valueMultiset_sum {i s : ℕ} {m : Multiset ℕ}
    (hm : m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image (valueMultiset (Finset.range i))) :
    m.sum = s := by
  rw [Finset.mem_image] at hm
  obtain ⟨l, hl, rfl⟩ := hm
  rw [Finset.mem_finsuppAntidiag] at hl
  rw [valueMultiset_sum]
  exact hl.1

/-- **STEP 1 — the per-(i, ab) inner-sum restriction (PROVEN).** -/
theorem inner_sum_trunc_eq_restricted_assembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i : ℕ) {s : ℕ} (hs : s ≤ t + 1) :
    (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image
              (valueMultiset (Finset.range i)),
        (Multiset.countPerms m) •
          ((m.map (fun j => PowerSeries.coeff j (βHenselTrunc H x₀ R hHyp t))).prod))
      = ∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) s).image
                (valueMultiset (Finset.range i)),
          (if (t + 1) ∈ m then 0
            else (Multiset.countPerms m) •
              ((m.map (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)) := by
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hsum : m.sum = s := image_valueMultiset_sum hm
  by_cases hmem : (t + 1) ∈ m
  · rw [if_pos hmem, prod_map_coeff_trunc_eq_zero_of_mem H x₀ R hHyp t hmem]
    simp
  · rw [if_neg hmem,
      prod_map_coeff_trunc_eq_assembled_of_notMem H x₀ R hHyp t (by rw [hsum]; exact hs) hmem]

/-- **STEP 1 (the wiped w14 lemma, RE-DERIVED, PROVEN).**
`trunc_defect_eq_faaDiBruno_assembled_restricted` — the order-`(t+1)` coefficient of
`eval (βHenselTrunc t) Q` equals the assembled Faà-di-Bruno partition/`countPerms` sum
**restricted** to value-multisets `m` with `(t+1) ∉ m`. -/
theorem trunc_defect_eq_faaDiBruno_assembled_restricted (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                      (valueMultiset (Finset.range i)),
                (if (t + 1) ∈ m then 0
                  else (Multiset.countPerms m) •
                    ((m.map (fun j =>
                      PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod))) := by
  rw [coeff_eval_Q_faaDiBruno]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun ab hab => ?_)
  have hab2 : ab.2 ≤ t + 1 := by
    rw [Finset.mem_antidiagonal] at hab
    omega
  rw [inner_sum_trunc_eq_restricted_assembled H x₀ R hHyp t i hab2]

/-! ## STEP 2 — the truncated-defect cancellation -/

/-- Abbreviation for the restricted Faà-di-Bruno sum of STEP 1 (the order-`(t+1)` truncated
defect, laid bare). -/
def restrictedFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ ab ∈ Finset.antidiagonal (t + 1),
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
      * (∑ m ∈ (Finset.finsuppAntidiag (Finset.range i) ab.2).image
                (valueMultiset (Finset.range i)),
          (if (t + 1) ∈ m then 0
            else (Multiset.countPerms m) •
              ((m.map (fun j =>
                PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))

/-- STEP 1, repackaged: the order-`(t+1)` truncated defect equals `restrictedFaaDiBrunoSum`. -/
theorem trunc_defect_eq_restrictedFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      = restrictedFaaDiBrunoSum H x₀ R hHyp t :=
  trunc_defect_eq_faaDiBruno_assembled_restricted H x₀ R hHyp t

/-- **THE SINGLE NAMED COMBINATORIAL CORE of P2 (the carved residual), as a `Prop`.**
`RestrictedFaaDiBrunoMatch`: the restricted Faà-di-Bruno sum equals
`−ζ · coeff(t+1)(βHenselAssembled)` at every order.  This is the genuine BCIKS20 A.4 match:
bijecting the restricted value-multisets `m` (entries = orders, zeros allowed, `card = i`,
`(t+1) ∉ m`) against the `(A.1)` index pairs `(i1, λ)` — X-Taylor order `ab.1 = i1`, positive
entries forming `λ ⊢ ab.2`, zero-slot count `i − card λ` the Y-degree bookkeeping — matching
`countPerms m` against the positive-part `prefactor = λ.parts.countPerms` together with the
Y-Hasse binomial from `hasseDerivY_coeff`, the per-term values via `coeff_Q_eq_B`
  + `partitionProd_coeff_assembled`, and clearing the `W`/`ξ` telescopes with
  the `ζ` sign/denominator conventions.
THIS is the last genuinely unformalized content of P2; everything else of P2 is PROVEN. -/
def RestrictedFaaDiBrunoMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
  restrictedFaaDiBrunoSum H x₀ R hHyp t
    = - (ClaimA2.ζ R x₀ H
          * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))

/-- The all-orders carved P2 core, kept in its original equation form. -/
def RestrictedFaaDiBrunoMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, restrictedFaaDiBrunoSum H x₀ R hHyp t
    = - (ClaimA2.ζ R x₀ H
          * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))

/-- The carved core is exactly its family of single-order residuals. -/
theorem restrictedFaaDiBrunoMatch_iff_forall_at (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      ∀ t : ℕ, RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  Iff.rfl

/-- Projection from the all-orders carved P2 core to a fixed order. -/
theorem RestrictedFaaDiBrunoMatch.at (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  hmatch t

/-- Assemble the all-orders carved P2 core from its single-order family. -/
theorem RestrictedFaaDiBrunoMatch.of_forallAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  hat

/-- **STEP 2 — the truncated-defect cancellation, reduced to the single named core (PROVEN
from `RestrictedFaaDiBrunoMatch`).** -/
theorem trunc_defect_cancel_assembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp) = 0 := by
  rw [trunc_defect_eq_restrictedFaaDiBrunoSum H x₀ R hHyp t, hmatch t]
  ring

/-- Fixed-order truncated-defect cancellation from the single-order carved core. -/
theorem trunc_defect_cancel_assembled_at (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 := by
  rw [trunc_defect_eq_restrictedFaaDiBrunoSum H x₀ R hHyp t]
  unfold RestrictedFaaDiBrunoMatchAt at hmatch
  rw [hmatch]
  ring

/-- Fixed-order assembled-series coefficient vanishing from the single-order carved core. -/
theorem coeff_succ_eval_βHenselAssembled_of_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_of_trunc_defect_cancel H x₀ R hHyp t
    (trunc_defect_cancel_assembled_at H x₀ R hHyp t hmatch)

/-- **P2 root, conditional on the carved core (PROVEN reduction).** -/
theorem assembledSeries_isRoot_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  assembledSeries_isRoot_of_trunc_defect_cancel H x₀ R hHyp
    (fun t => trunc_defect_cancel_assembled H x₀ R hHyp hmatch t)

/-- **P2 lift identity, conditional on the carved core (PROVEN reduction).** -/
theorem βHensel_lift_identity_of_match (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  βHensel_lift_identity_of_trunc_defect_cancel H x₀ R hHyp
    (fun t => trunc_defect_cancel_assembled H x₀ R hHyp hmatch t) t

/-- **`P2_closed` — the residual statement of P2 (PROVEN reduction).**
The ENTIRE remaining mathematical content of BCIKS20 A.4's P2 is `RestrictedFaaDiBrunoMatch`:
given it, the assembled series is the genuine Hensel root AND the repaired lift identity holds for
all orders.  Everything else of P2 — STEP 1, the order-`0` base, the Newton linearization, the
`PowerSeries.ext` assembly, the denominator clearing, and the uniqueness reduction to
`gammaGenuine` — is PROVEN (here and upstream).

WIRE-IN (not made here): the legacy `faaDiBruno_succ_sum_eq_zero`/`FaaDiBrunoSuccSumZeroResidual`
frontier is discharged from `RestrictedFaaDiBrunoMatch` via
`coeff_succ_eval_defect_reduction` + `trunc_defect_cancel_assembled`; the genuinely open step is
still proving the `B_coeff` prefactor re-keying that supplies `RestrictedFaaDiBrunoMatch`. -/
theorem P2_closed (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  ⟨assembledSeries_isRoot_of_match H x₀ R hHyp hmatch,
    βHensel_lift_identity_of_match H x₀ R hHyp hmatch⟩

/-! ## STEP 3 — equivalence with the successor-sum P2 residual

The carved restricted form and the legacy `FaaDiBrunoSuccSumZeroResidual` carry identical
mathematical content. Both reduce through the proven Newton-defect identity
`coeff_succ_eval_defect_reduction` to the vanishing of
`coeff (t+1) (eval (βHenselAssembled) Q)` for every `t`. -/

/-- `FaaDiBrunoSuccSumZeroResidual` implies the carved restricted match. -/
theorem restrictedFaaDiBrunoMatch_of_faaDiBrunoSuccSumZero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  intro t
  have hdefect := coeff_succ_eval_defect_reduction H x₀ R hHyp t
  have hroot := coeff_succ_eval_βHenselAssembled H x₀ R hHyp hzero t
  have htrunc := trunc_defect_eq_restrictedFaaDiBrunoSum H x₀ R hHyp t
  rw [← htrunc]
  linear_combination hroot - hdefect

/-- The carved restricted match implies `FaaDiBrunoSuccSumZeroResidual`. -/
theorem faaDiBrunoSuccSumZero_of_restrictedFaaDiBrunoMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  intro t
  have hcancel := trunc_defect_cancel_assembled H x₀ R hHyp hmatch t
  have hroot := coeff_succ_eval_of_trunc_defect_cancel H x₀ R hHyp t hcancel
  rw [← coeff_eval_Q_faaDiBruno H x₀ R (βHenselAssembled H x₀ R hHyp) (t + 1)]
  exact hroot

/-- The two named P2 residuals are equivalent. -/
theorem restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  ⟨faaDiBrunoSuccSumZero_of_restrictedFaaDiBrunoMatch H x₀ R hHyp,
    restrictedFaaDiBrunoMatch_of_faaDiBrunoSuccSumZero H x₀ R hHyp⟩

-- In-file axiom audit for the carved P2 core and its conditional endpoint reductions.
section AxiomAudit
#print axioms RestrictedFaaDiBrunoMatchAt
#print axioms RestrictedFaaDiBrunoMatch
#print axioms restrictedFaaDiBrunoMatch_iff_forall_at
#print axioms RestrictedFaaDiBrunoMatch.at
#print axioms RestrictedFaaDiBrunoMatch.of_forallAt
#print axioms restrictedFaaDiBrunoMatch_of_faaDiBrunoSuccSumZero
#print axioms faaDiBrunoSuccSumZero_of_restrictedFaaDiBrunoMatch
#print axioms restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero
#print axioms trunc_defect_eq_restrictedFaaDiBrunoSum
#print axioms trunc_defect_cancel_assembled
#print axioms trunc_defect_cancel_assembled_at
#print axioms coeff_succ_eval_βHenselAssembled_of_restrictedMatchAt
#print axioms assembledSeries_isRoot_of_match
#print axioms βHensel_lift_identity_of_match
#print axioms P2_closed
end AxiomAudit

end BCIKS20.HenselNumerator
