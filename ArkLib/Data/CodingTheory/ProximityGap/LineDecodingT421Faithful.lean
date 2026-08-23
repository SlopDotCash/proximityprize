/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import Mathlib.Tactic.Linarith

/-!
# Faithful ABF26 Theorem 4.21 — genuine GS list-size bound on the MCA bad-scalar count (#140)

The black-box form of ABF26 Theorem 4.21 (`lineDecodable_imp_epsMCA_le_target`) is
**mathematically false** and is *proven* refuted in-tree (`LineDecodingRefutation.lean`).

The first repair attempt routed the conclusion `ε_mca C δ = 0` through the hypothesis
`MCAForallDoubleCover C δ` (per-coordinate "double cover" by two distinct scalars). That repair
is **circular**: two distinct scalars pin a degree-`≤1` line, so the double cover collapses to
joint agreement, and the in-tree theorem `epsMCA_eq_zero_iff_MCAForallDoubleCover` proves

  `MCAForallDoubleCover C δ ↔ epsMCA C δ = 0`.

The "repaired" hypothesis is therefore *goal-equivalent* to the conclusion — it assumes (an exact
restatement of) what it sets out to prove, so it carries no content.

This module gives the **non-circular** repair. The genuine open Guruswami–Sudan content is
exposed as honest interpolation data — a *single* candidate codeword-pair `v = (v₀, v₁) ∈ C²`
whose affine line `v₀ + γ·v₁` `µ`-agrees (weight `≥ α`) with the received line `u₀ + γ·u₁` at
*every* bad scalar `γ` — together with the genuine failure of correlated agreement for that pair.
This hypothesis is **strictly weaker** than `epsMCA = 0`: it asserts the existence of a shared
low-degree interpolant covering the bad scalars, *not* the absence of bad scalars. From it the
**proven** BCIKS20 list-agreement-on-a-curve bound
(`WeightedAgreement.sufficiently_large_list_agreement_on_curve_implies_correlated_agreement`)
delivers a real list-size cap on the bad-scalar count:

  `mcaBadCount C δ u₀ u₁ < M·n + 1`,

i.e. per stack `ε_mca`-contribution `< (M·n + 1)/|F|` — the authentic `a/|F|` shape of T4.21
(`l = 0` for the affine line, `M` the common denominator of the weight profile `µ`, `n = |ι|`).
Contrapositive of the curve bound: were there `≥ M·n + 1` bad scalars sharing the interpolant,
the curve lemma would force correlated agreement, contradicting its failure.

The remaining genuinely-open content is *constructing* the GS interpolant `v` (the
Guruswami–Sudan list decoder of `u₀ + Z·u₁` over `F(Z)`); this module faithfully isolates that
as the explicit, non-circular hypothesis `hcover`/`hfail`, with the extraction itself proven.

## References

- [ABF26] Arnon-Boneh-Fenzi. Theorem 4.21. *Open Problems in List Decoding and Correlated
  Agreement.*
- [GG25] Goyal-Guruswami; [BCIKS20] Ben-Sasson et al. (the curve list-agreement bound).
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal

namespace ProximityGap

open WeightedAgreement

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Faithful ABF26 Theorem 4.21 core — genuine GS list-size bound on the MCA bad-scalar count.**

The *non-circular* replacement for the refuted black-box `lineDecodable_imp_epsMCA_le_target` and
for the circular `MCAForallDoubleCover` repair (whose hypothesis is provably equivalent to the
conclusion `ε_mca = 0` via `epsMCA_eq_zero_iff_MCAForallDoubleCover`). The open Guruswami–Sudan
content is exposed as genuine interpolation data — a *single* candidate codeword-pair
`v = (v₀, v₁) ∈ C²` whose affine line `v₀ + γ·v₁` `µ`-agrees (weight `≥ α`) with the received
line `u₀ + γ·u₁` at *every* bad scalar `γ` — together with the genuine failure of correlated
agreement for that pair. From this the **proven** BCIKS20 list-agreement-on-a-curve bound
(`sufficiently_large_list_agreement_on_curve_implies_correlated_agreement`) gives the real
list-size cap

  `mcaBadCount C δ u₀ u₁ < M·n + 1`,

i.e. per-stack `ε_mca`-contribution `< (M·n + 1)/|F|`, the genuine `a/|F|` shape of T4.21
(`l = 0` for the affine line; `M` the common denominator of the weight profile `µ`, `n = |ι|`).

The hypothesis is strictly weaker than the conclusion: it asserts a shared low-degree interpolant
covering the bad scalars, **not** the absence of bad scalars. Contrapositive of the curve bound:
were there `≥ M·n + 1` bad scalars, the curve lemma would force correlated agreement,
contradicting `hfail`. -/
theorem mcaBadCount_lt_of_gs_curve_cover
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (μ : ι → Set.Icc (0 : ℚ) 1) (M : ℕ) (hM : 0 < M)
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    (α : ℝ≥0) (v : Fin 2 → ι → F)
    (hcover : ∀ γ : F, mcaEvent C δ u₀ u₁ γ →
        (α : ℝ) ≤ agree μ (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u₀, u₁] γ x)
                    (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x))
    (hfail : mu_set μ { x : ι | ∀ i, (![u₀, u₁] : Fin 2 → ι → F) i x = v i x } < (α : ℝ)) :
    mcaBadCount (F := F) C δ u₀ u₁ < M * Fintype.card ι + 1 := by
  classical
  by_contra hge
  push Not at hge
  -- `S'` is exactly the bad-scalar set; `mcaBadCount = S'.card`.
  set S' : Finset F := univ.filter (fun γ : F => mcaEvent C δ u₀ u₁ γ) with hS'
  have hcard : mcaBadCount (F := F) C δ u₀ u₁ = S'.card := rfl
  rw [hcard] at hge
  -- size hypotheses for the curve lemma, `l = 0`
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hMn : 2 ≤ M * Fintype.card ι + 1 := by
    have : 1 ≤ M * Fintype.card ι := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h1 : S'.card > 0 + 1 := by omega
  have h2 : S'.card ≥ (M * Fintype.card ι + 1) * (0 + 1) := by simpa using hge
  -- the cover gives curve-agreement at every bad scalar `z ∈ S'`
  have hagree : ∀ z ∈ S',
      (α : ℝ) ≤ agree μ
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u₀, u₁] z x)
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) := by
    intro z hz
    exact hcover z (Finset.mem_filter.mp hz).2
  -- proven BCIKS20 curve bound forces correlated agreement
  have hcorr :
      mu_set μ { x : ι | ∀ i, (![u₀, u₁] : Fin 2 → ι → F) i x = v i x } ≥ (α : ℝ) :=
    sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
      (l := 0) (u := ![u₀, u₁]) (μ := μ) (α := α) (M := M) hμ (v := v) (S' := S')
      h1 h2 hagree
  exact absurd hcorr (not_le.mpr hfail)

/-- Uniform `ε_mca` wrapper for the faithful T4.21 repair.

If every received affine-line stack admits genuine GS curve-cover data, the per-stack bound from
`mcaBadCount_lt_of_gs_curve_cover` lifts through the exact bad-count formula to
`ε_mca C δ ≤ (M * |ι| + 1) / |F|`. This is only a packaging step: the open interpolation content
remains precisely the supplied `hcover`. -/
theorem epsMCA_le_of_forall_gs_curve_cover
    (C : Set (ι → F)) (δ : ℝ≥0)
    (μ : ι → Set.Icc (0 : ℚ) 1) (M : ℕ) (hM : 0 < M)
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    (α : ℝ≥0)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι, ∃ v : Fin 2 → ι → F,
      (∀ γ : F, mcaEvent C δ (u 0) (u 1) γ →
          (α : ℝ) ≤ agree μ
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u 0, u 1] γ x)
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x)) ∧
      mu_set μ { x : ι | ∀ i, (![u 0, u 1] : Fin 2 → ι → F) i x = v i x } <
        (α : ℝ)) :
    epsMCA (F := F) (A := F) C δ ≤
      ((M * Fintype.card ι + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  refine ENNReal.div_le_div_right ?_ _
  refine iSup_le fun u => ?_
  rcases hcover u with ⟨v, hcov, hfail⟩
  have hlt :
      mcaBadCount (F := F) C δ (u 0) (u 1) < M * Fintype.card ι + 1 :=
    mcaBadCount_lt_of_gs_curve_cover C δ (u 0) (u 1) μ M hM hμ α v hcov hfail
  exact_mod_cast Nat.le_of_lt hlt

/-- Package the faithful uniform GS cover as an `MCALowerWitness` once the usual budget comparison
against the target threshold is available. -/
noncomputable def GrandChallenges.MCALowerWitness.of_forall_gs_curve_cover
    (C : Set (ι → F)) {δ ε_star : ℝ≥0}
    (μ : ι → Set.Icc (0 : ℚ) 1) (M : ℕ) (hM : 0 < M)
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    (α : ℝ≥0)
    (hδ : δ ≤ 1)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι, ∃ v : Fin 2 → ι → F,
      (∀ γ : F, mcaEvent C δ (u 0) (u 1) γ →
          (α : ℝ) ≤ agree μ
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u 0, u 1] γ x)
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x)) ∧
      mu_set μ { x : ι | ∀ i, (![u 0, u 1] : Fin 2 → ι → F) i x = v i x } <
        (α : ℝ))
    (hbudget :
      ((M * Fintype.card ι + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
        (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (F := F) C ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ
    (le_trans
      (epsMCA_le_of_forall_gs_curve_cover C δ μ M hM hμ α hcover)
      hbudget)

/-- Existential projection of the faithful GS-cover lower witness, preserving the certified
radius. -/
theorem GrandChallenges.exists_mcaLowerWitness_of_forall_gs_curve_cover
    (C : Set (ι → F)) {δ ε_star : ℝ≥0}
    (μ : ι → Set.Icc (0 : ℚ) 1) (M : ℕ) (hM : 0 < M)
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    (α : ℝ≥0)
    (hδ : δ ≤ 1)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι, ∃ v : Fin 2 → ι → F,
      (∀ γ : F, mcaEvent C δ (u 0) (u 1) γ →
          (α : ℝ) ≤ agree μ
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u 0, u 1] γ x)
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x)) ∧
      mu_set μ { x : ι | ∀ i, (![u 0, u 1] : Fin 2 → ι → F) i x = v i x } <
        (α : ℝ))
    (hbudget :
      ((M * Fintype.card ι + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
        (ε_star : ENNReal)) :
    ∃ w : GrandChallenges.MCALowerWitness (F := F) C ε_star, w.δ = δ := by
  refine ⟨GrandChallenges.MCALowerWitness.of_forall_gs_curve_cover
    C μ M hM hμ α hδ hcover hbudget, rfl⟩

/-- `Nonempty` projection of the faithful GS-cover lower witness. -/
theorem GrandChallenges.nonempty_mcaLowerWitness_of_forall_gs_curve_cover
    (C : Set (ι → F)) {δ ε_star : ℝ≥0}
    (μ : ι → Set.Icc (0 : ℚ) 1) (M : ℕ) (hM : 0 < M)
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    (α : ℝ≥0)
    (hδ : δ ≤ 1)
    (hcover : ∀ u : Code.WordStack F (Fin 2) ι, ∃ v : Fin 2 → ι → F,
      (∀ γ : F, mcaEvent C δ (u 0) (u 1) γ →
          (α : ℝ) ≤ agree μ
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) ![u 0, u 1] γ x)
            (fun x => Curve.polynomialCurveEval (F := F) (A := F) v γ x)) ∧
      mu_set μ { x : ι | ∀ i, (![u 0, u 1] : Fin 2 → ι → F) i x = v i x } <
        (α : ℝ))
    (hbudget :
      ((M * Fintype.card ι + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
        (ε_star : ENNReal)) :
    Nonempty (GrandChallenges.MCALowerWitness (F := F) C ε_star) :=
  ⟨GrandChallenges.MCALowerWitness.of_forall_gs_curve_cover
    C μ M hM hμ α hδ hcover hbudget⟩

end ProximityGap

/-! ### `#print axioms` verification anchor -/

#print axioms ProximityGap.mcaBadCount_lt_of_gs_curve_cover
#print axioms ProximityGap.epsMCA_le_of_forall_gs_curve_cover
#print axioms ProximityGap.GrandChallenges.MCALowerWitness.of_forall_gs_curve_cover
#print axioms ProximityGap.GrandChallenges.exists_mcaLowerWitness_of_forall_gs_curve_cover
#print axioms ProximityGap.GrandChallenges.nonempty_mcaLowerWitness_of_forall_gs_curve_cover
