/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ16Claim58Truncation
import ArkLib.ToMathlib.XDegreeBudgetProbe
import ArkLib.ToMathlib.WeightLambdaCalculus
import ArkLib.ToMathlib.GenuineTruncationFin

/-!
# SYZ17 — the #138 `X`-degree budget on the T-loaded representative, in its provable form

## The object

SYZ16 isolated the sole Claim 5.8 residual to `GammaGenuineTailPolynomial` and identified its
non-degenerate content with the **#138 ground `X`-degree budget**: `degreeX` bounds on the
components `P₀, P₁` of the corrected (T-loaded) representative
(`GenuinePpolyConverter`: "the corrected analogue of the old `hdegX : degreeX Ppoly ≤ 1`
companion … is NOT produced by the converter").  This file proves the budget **in the form the
Hensel recursion actually supports** — an explicit, `t`-graded budget telescoped through the
`(A.1)` per-step degree growth — and pins, with in-tree kernel-checked evidence, why the paper's
*absolute* (weight-1) form is out of reach for every bookkeeping route.

## The degree-accounting argument (found, and how far it goes)

For monic `H` the genuine coefficient `αGenuine t` has the *unique* integral preimage
`βHensel t · (ξ⁻¹)^(2t−1)` (`P1MonicIntegrality`: `ξ` is a unit by separability; uniqueness by
`embeddingOf𝒪Into𝕃_injective`).  The two factors are exactly the recursion's numerator and the
denominator's inverse, and both sides are `Λ`-weight-controlled:

* the numerator obeys the **graded per-step growth bound** already telescoped in-tree,
  `GenuineTruncationFin.weight_βHensel_le_graded`:
  `Λ(βHensel t) ≤ (n_R·(D−d+1) + D + (D−d+1))·(2t−1) + (D−d+1)` — linear in `t`, with slope an
  explicit function of `deg_X R` (through the grading `hR`), `D`, and `d_H`;
* the `(A.1)` division by `W·ξ²` per step contributes `(2t−1)` factors of `ξ⁻¹`
  (monic: `W = 1`), each costing one fixed weight `Λ(ξ⁻¹) ≤ W_ξ` by submultiplicativity
  (`WeightLambdaCalculus`).

Hence (`alpha_preimage_weight_le_graded`) **every** integral preimage of `αGenuine t` has
`Λ`-weight `≤ alphaGradedBudget t := B(t) + (2t−1)·W_ξ`, and — through the weight → `X`-degree
extraction `XDegreeBudgetProbe.natDegree_coeff_canonicalRep_le_of_weight_le` — its
canonical-representative coefficients have `X`-degree `≤ alphaGradedBudget t`.  Feeding these
canonical coefficients into the converter yields the **budgeted T-loaded representative**
(`exists_budgeted_corrected_representative`): support in `[0, k)` AND
`degreeX P₀, degreeX P₁ ≤ alphaGradedBudget (k−1)` — the #138 `degreeX P₀/P₁` bounds, explicit in
`deg_X R` (via `D`), the truncation length `k`, `d_H`, and the single fixed constant `W_ξ`.

## The honest wall (twofold, both machine-checked)

1. **The absolute (weight-1) #138 budget is NOT reachable by this — or any — degree bookkeeping.**
   `XDegreeBudgetProbe.graded_rescue_dead` (in-tree, kernel-checked): the
   `P1MonicWeightRefutation` witness satisfies monicity, the paper grading
   `degreeX (R.coeff j) ≤ D − j`, the strongest pointwise trivariate grading, and every other
   graded side condition at the pinned `D = 2`, yet the budget `deg_X c₀ ≤ 1 ∧ (D+1−d_H) +
   deg_X c₁ ≤ 1` FAILS at `t = 1`.  So the `t`-graded budget proven here is optimal-in-kind:
   the gap to the paper's absolute form is genuinely GS-*geometric* (the agreement structure
   tying the `Z`-direction of `R` to codewords), not recursive degree accounting.
   Re-exported below as `weight_one_budget_wall`.

2. **The `ξ⁻¹`-weight supply is the one fixed constant the accounting does not produce.**  The
   recursion divides by `ξ` (monic `W = 1` kills the `W`-division, but not the `ξ`-division);
   `ξ⁻¹` exists (`isUnit_ξ_of_monic`) but its canonical-representative degree is not controlled
   by the in-tree calculus.  It is a SINGLE element (not `t`-dependent), so it enters the budget
   as one named parameter `W_ξ` with hypothesis `hbw : Λ(ξ⁻¹) ≤ W_ξ` — the minimal residual
   `XiInverseWeightSupply` shape.  (Mathematically `W_ξ ≤ deg_X ξ + (D − d_H)`-ish via
   norm/conjugate for `d_H = 2`; the norm calculus is not in-tree.)

## What this does and does not change for Claim 5.8

The budget here consumes the truncation identity (through the converter), so it does **not**
produce `GammaGenuineTailPolynomial` — SYZ16's residual is unchanged.  What it adds: once the
tail residual is granted, the T-loaded representative of the §5 branch field is now **fully
explicit** — support `[0, k)` and `X`-degrees bounded by a closed-form budget — which is the #138
`degreeX P₀/P₁` open statement in its provable rendering
(`branch_field_budgeted_of_graded_disc_tail` upgrades SYZ16's non-vacuity witness with the
degree bounds).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Prop. 5.5, Claims 5.8/5.9, Appendix A.4 (weight induction).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000

noncomputable section

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open ArkLib

namespace BCIKS20.CellPencilJohnson.SYZ17

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## 1. The explicit budget -/

/-- **The `t`-graded #138 `X`-degree budget.**  `B(t) + (2t−1)·W_ξ`, where `B(t)` is the in-tree
telescoped graded weight bound on the `(A.1)` numerator `βHensel t`
(`GenuineTruncationFin.weight_βHensel_le_graded`, slope explicit in `n_R = natDegreeY R`, `D`
(which dominates `deg_X R` through the grading) and `d = d_H`), and `(2t−1)·W_ξ` is the cost of
the recursion's `ξ`-divisions (one fixed constant `W_ξ ≥ Λ(ξ⁻¹)` per division). -/
def alphaGradedBudget (nR D d t Wxi : ℕ) : ℕ :=
  ((nR * (D - d + 1) + D + (D - d + 1)) * (2 * t - 1) + (D - d + 1)) + (2 * t - 1) * Wxi

/-- The budget is monotone in the order `t` (so a uniform budget over `t < k` is the budget at
`k − 1`). -/
lemma alphaGradedBudget_mono {nR D d Wxi : ℕ} {t t' : ℕ} (h : t ≤ t') :
    alphaGradedBudget nR D d t Wxi ≤ alphaGradedBudget nR D d t' Wxi := by
  unfold alphaGradedBudget
  have h2 : 2 * t - 1 ≤ 2 * t' - 1 := by omega
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul le_rfl h2) _)
    (Nat.mul_le_mul h2 le_rfl)

/-! ## 2. The unique integral preimage is the recursion numerator over the `ξ`-divisions -/

/-- **The forced shape of every integral preimage (monic).**  Any `a : 𝒪 H` with
`embed a = αGenuine t` equals `βHensel t · b^(2t−1)` for any `ξ`-inverse `b` — the `(A.1)`
numerator times the accumulated division inverses.  Uniqueness is
`embeddingOf𝒪Into𝕃_injective`; the identity is the monic lift identity
(`βHensel_lift_identity`, `W = 1`). -/
theorem alpha_preimage_eq_βHensel_mul_pow {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hlc : H.leadingCoeff = 1)
    {b : 𝒪 H} (hb : b * ClaimA2.ξ x₀ R H hHyp = 1) (t : ℕ) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t) :
    a = βHensel H x₀ R hHyp t * b ^ (2 * t - 1) := by
  have hzero := faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one H x₀ R hHyp hlc
  have hlift := βHensel_lift_identity H x₀ R hHyp hzero t
  rw [hlc, map_one, one_pow, mul_one] at hlift
  refine embeddingOf𝒪Into𝕃_injective hH ?_
  rw [ha, map_mul, map_pow, hlift, mul_assoc, ← mul_pow, ← map_mul,
    mul_comm (ClaimA2.ξ x₀ R H hHyp) b, hb, map_one, one_pow, mul_one]

/-- **The recursion budget telescoped through the `ξ`-division (the positive face of #138).**
Every integral preimage of `αGenuine t` has `Λ`-weight bounded by the explicit `t`-graded budget:
the graded per-step numerator growth (`weight_βHensel_le_graded`) plus `(2t−1)` copies of the
fixed `ξ⁻¹`-weight `W_ξ`, by submultiplicativity.  This is the honest telescoped form of the
brief's "per-step degree growth is bounded" induction — the growth is linear in `t`, NOT
absolute (see `weight_one_budget_wall`). -/
theorem alpha_preimage_weight_le_graded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {b : 𝒪 H} (hb : b * ClaimA2.ξ x₀ R H hHyp = 1)
    {Wxi : ℕ} (hbw : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some Wxi : WithBot ℕ))
    (t : ℕ) {a : 𝒪 H} (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t) :
    weight_Λ_over_𝒪 hH a D
      ≤ (WithBot.some (alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree t Wxi) : WithBot ℕ) := by
  rw [alpha_preimage_eq_βHensel_mul_pow hHyp hH hmonic.leadingCoeff hb t ha]
  exact ArkLib.weight_Λ_over_𝒪_mul_le_of_le hD hH
    (ArkLib.GenuineTruncationFin.weight_βHensel_le_graded H hHyp hD hH hmonic hd2 hdHD
      hD_Rx0 hR t)
    (ArkLib.weight_Λ_over_𝒪_pow_le_of_le hD hH hbw (2 * t - 1))

/-- **Per-order `X`-degrees of the canonical representative obey the budget** — the weight →
`X`-degree extraction applied to the telescoped bound: every `Y`-coefficient of the canonical
representative of the (unique) integral preimage of `αGenuine t` has `X`-degree
`≤ alphaGradedBudget t`. -/
theorem alpha_canonicalRep_coeff_natDegree_le_graded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {b : 𝒪 H} (hb : b * ClaimA2.ξ x₀ R H hHyp = 1)
    {Wxi : ℕ} (hbw : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some Wxi : WithBot ℕ))
    (t : ℕ) {a : 𝒪 H} (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t) (n : ℕ) :
    ((canonicalRepOf𝒪 hH a).coeff n).natDegree
      ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree t Wxi :=
  ArkLib.XDegreeBudgetProbe.natDegree_coeff_canonicalRep_le_of_weight_le hH
    (alpha_preimage_weight_le_graded hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR hb hbw t ha) n

/-! ## 3. The budgeted T-loaded representative — the #138 `degreeX P₀/P₁` bounds -/

/-- **The #138 `X`-degree budget on the T-loaded representative (T-dependent form, PROVEN).**
For monic `d_H ≤ 2`, from the truncation identity at `k`, the graded data, and the fixed
`ξ⁻¹`-weight supply, the corrected representative exists with BOTH coordinate-wise supports in
`[0, k)` AND the explicit `X`-degree bounds
`degreeX P₀, degreeX P₁ ≤ alphaGradedBudget (k−1)` — exactly the `degreeX P₀/P₁` companion the
converter could not produce (`GenuinePpolyConverter`, "the open #138 residual"), delivered here
in the `t`-graded form the recursion supports. -/
theorem exists_budgeted_corrected_representative {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hd2H : H.natDegree ≤ 2)
    {b : 𝒪 H} (hb : b * ClaimA2.ξ x₀ R H hHyp = 1)
    {Wxi : ℕ} (hbw : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some Wxi : WithBot ℕ))
    {k : ℕ}
    (htrunc : gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H))) :
    ∃ P₀ P₁ : F[X][Y],
      ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp
      ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0)
      ∧ Bivariate.degreeX P₀
          ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree (k - 1) Wxi
      ∧ Bivariate.degreeX P₁
          ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree (k - 1) Wxi := by
  classical
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hzero := faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one H x₀ R hHyp hlc
  -- per-order integral preimages
  choose aa haa using fun t => alphaGenuine_regular_of_monic H x₀ R hHyp hzero hlc t
  set c₀ : ℕ → F[X] := fun t => (canonicalRepOf𝒪 hH (aa t)).coeff 0 with hc₀
  set c₁ : ℕ → F[X] := fun t => (canonicalRepOf𝒪 hH (aa t)).coeff 1 with hc₁
  -- the per-order T-form on the canonical coefficients
  have hT : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (c₁ t) := fun t => by
    rw [← haa t, embed_zLinear_of_monic_natDegree_le_two H hH hlc hd2H (aa t)]
  -- the per-order X-degree budget, uniformized over t < k
  have hdeg : ∀ t, t < k → ∀ n,
      ((canonicalRepOf𝒪 hH (aa t)).coeff n).natDegree
        ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree (k - 1) Wxi := by
    intro t ht n
    exact le_trans
      (alpha_canonicalRep_coeff_natDegree_le_graded hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
        hb hbw t (haa t) n)
      (alphaGradedBudget_mono (by omega))
  refine ⟨PowerSeries.trunc k (PowerSeries.mk c₀), PowerSeries.trunc k (PowerSeries.mk c₁),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- the representative identity (the converter's construction on canonical witnesses)
    ext t
    rw [ArkLib.GenuinePpolyConverter.coeff_polyToPowerSeries𝕃T,
      PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    by_cases ht : t < k
    · rw [if_pos ht, if_pos ht, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        show PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) = αGenuine H x₀ R hHyp t from rfl]
      exact (hT t).symm
    · rw [if_neg ht, if_neg ht, map_zero, mul_zero, add_zero]
      conv_rhs => rw [htrunc]
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg ht]
  · intro t ht
    rw [PowerSeries.coeff_trunc, if_neg (not_lt.mpr ht)]
  · intro t ht
    rw [PowerSeries.coeff_trunc, if_neg (not_lt.mpr ht)]
  · -- degreeX P₀ ≤ budget (k − 1)
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro n hn
    rw [Polynomial.mem_support_iff] at hn
    by_cases hnk : n < k
    · rw [show (PowerSeries.trunc k (PowerSeries.mk c₀)).coeff n = c₀ n by
        rw [PowerSeries.coeff_trunc, if_pos hnk, PowerSeries.coeff_mk]]
      exact hdeg n hnk 0
    · exact absurd (by rw [PowerSeries.coeff_trunc, if_neg hnk]) hn
  · -- degreeX P₁ ≤ budget (k − 1)
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro n hn
    rw [Polynomial.mem_support_iff] at hn
    by_cases hnk : n < k
    · rw [show (PowerSeries.trunc k (PowerSeries.mk c₁)).coeff n = c₁ n by
        rw [PowerSeries.coeff_trunc, if_pos hnk, PowerSeries.coeff_mk]]
      exact hdeg n hnk 1
    · exact absurd (by rw [PowerSeries.coeff_trunc, if_neg hnk]) hn

/-! ## 4. Wiring into SYZ16: the fully budgeted branch field -/

section Wiring

variable [Fintype F] [DecidableEq F]
variable (H) in
/-- **SYZ16's non-vacuity witness, upgraded with the #138 `X`-degree budget.**  At a monic
quadratic curve, from finite geometric data + the minimal tail residual
`GammaGenuineTailPolynomial` (SYZ16) + the fixed `ξ⁻¹`-weight supply: the ground representative
field is EMPTY (F6), while the T-loaded field is inhabited by a representative that is now
**fully explicit** — support in `[0, k)` AND `degreeX P₀, degreeX P₁ ≤ alphaGradedBudget (k−1)`.
The truncation identity is derived internally (`SYZ16.gammaGenuine_eq_trunc_of_graded_disc_tail`)
and fed to the budgeted converter. -/
theorem branch_field_budgeted_of_graded_disc_tail
    (hdegH : H.natDegree = 2) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmonic : H.Monic)
    {D k T : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (htail : BCIKS20.CellPencilJohnson.SYZ16.GammaGenuineTailPolynomial x₀ R hHyp T)
    {b : 𝒪 H} (hb : b * ClaimA2.ξ x₀ R H hHyp = 1)
    {Wxi : ℕ} (hbw : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some Wxi : WithBot ℕ))
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T
        + disc.natDegree < Fintype.card F) :
    (¬ ∃ Ppoly : F[X][Y],
        polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
      ∧ (∃ P₀ P₁ : F[X][Y],
        ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp
        ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0)
        ∧ Bivariate.degreeX P₀
            ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree (k - 1) Wxi
        ∧ Bivariate.degreeX P₁
            ≤ alphaGradedBudget (Bivariate.natDegreeY R) D H.natDegree (k - 1) Wxi) := by
  have htrunc := BCIKS20.CellPencilJohnson.SYZ16.gammaGenuine_eq_trunc_of_graded_disc_tail
    hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR htail hvanish hdisc hcover hbig
  exact ⟨ArkLib.GenuinePpolyConverter.hrepG_unsat_of_two_le_natDegree H
      (le_of_eq hdegH.symm) hHyp,
    exists_budgeted_corrected_representative hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
      (le_of_eq hdegH) hb hbw htrunc⟩

end Wiring

/-! ## 5. The wall, re-exported: the absolute (weight-1) budget is dead for bookkeeping -/

open BCIKS20.HenselNumerator.WeightWitness in
/-- **The absolute #138 budget cannot follow from the accounting above** (re-export of the
kernel-checked `XDegreeBudgetProbe.graded_rescue_dead`): the `P1MonicWeightRefutation` witness
satisfies EVERY graded hypothesis consumed by `alpha_preimage_weight_le_graded` at the pinned
`D = 2`, yet the absolute budget `deg_X c₀ ≤ 1 ∧ (D+1−d_H) + deg_X c₁ ≤ 1` fails at `t = 1`.
So the `t`-graded budget of this file is optimal-in-kind for degree-bookkeeping routes; the gap
to the paper's weight-1 invariant is GS-geometric. -/
theorem weight_one_budget_wall (hH : 0 < myH.natDegree) :
    (myH.Monic
      ∧ Bivariate.totalDegree myH ≤ 2
      ∧ myH.natDegree ≤ 2
      ∧ 2 ≤ Bivariate.natDegreeY myR
      ∧ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C (0 : K)) myR) ≤ 2
      ∧ (∀ j, Bivariate.degreeX (myR.coeff j) ≤ 2 - j))
    ∧ ¬ (∀ t : ℕ, ∀ a : 𝒪 myH, embeddingOf𝒪Into𝕃 myH a = αGenuine myH 0 myR myHyp t →
        ((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
          ∧ (2 + 1 - Bivariate.natDegreeY myH)
              + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) :=
  ArkLib.XDegreeBudgetProbe.graded_rescue_dead hH

end BCIKS20.CellPencilJohnson.SYZ17

end

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.SYZ17.alphaGradedBudget_mono
#print axioms BCIKS20.CellPencilJohnson.SYZ17.alpha_preimage_eq_βHensel_mul_pow
#print axioms BCIKS20.CellPencilJohnson.SYZ17.alpha_preimage_weight_le_graded
#print axioms BCIKS20.CellPencilJohnson.SYZ17.alpha_canonicalRep_coeff_natDegree_le_graded
#print axioms BCIKS20.CellPencilJohnson.SYZ17.exists_budgeted_corrected_representative
#print axioms BCIKS20.CellPencilJohnson.SYZ17.branch_field_budgeted_of_graded_disc_tail
#print axioms BCIKS20.CellPencilJohnson.SYZ17.weight_one_budget_wall
