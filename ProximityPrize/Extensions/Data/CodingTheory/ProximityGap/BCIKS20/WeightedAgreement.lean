/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound

/-!
# BCIKS20 weighted agreement on polynomial curves

This file develops the weighted (`μ`-fractional) agreement bookkeeping behind the [BCIKS20]
proximity-gap argument on polynomial curves.  It collects the basic facts about a weight
function `μ : ι → [0,1]` and the curve difference polynomial (`diffPoly_natDegree_le`,
`diffPoly_eval`, `diffPoly_ne_zero`), bounds the number of coordinates on which two curves
match (`badCoord_match_card_le`, `card_le_natDegree_of_eval_zero`), and proves that list
agreement along a curve forces a correlated-agreement bound
(`list_agreement_on_curve_implies_correlated_agreement_bound` and its sufficiently-large
list variant).
-/

namespace ProximityGap

namespace WeightedAgreement

-- Decidability instances are threaded through the sections for the agreement machinery;
-- several statement-level lemmas do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory ReedSolomon Uniform
open scoped BigOperators Pointwise ProbabilityTheory

section ProbabilityTheorems

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

instance {domain : ι ↪ F} {deg : ℕ} : Nonempty (finCarrier domain deg) := by
  rcases Submodule.nonempty (ReedSolomon.code domain deg) with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simpa [ReedSolomon.finCarrier, Set.mem_toFinset] using hv

end ProbabilityTheorems

section ListAgreementLemmas

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [DecidableEq F]

omit [Fintype ι] [Nonempty ι] in
/-- Each weight `(μ i).1` is nonnegative. -/
lemma mu_nonneg (μ : ι → Set.Icc (0 : ℚ) 1) (i : ι) : 0 ≤ (μ i).1 := (μ i).2.1

omit [Fintype ι] [Nonempty ι] in
/-- Each weight `(μ i).1` is at most one. -/
lemma mu_le_one (μ : ι → Set.Icc (0 : ℚ) 1) (i : ι) : (μ i).1 ≤ 1 := (μ i).2.2

omit [Field F] [Nonempty ι] in
/-- `μ`-agreement equals the `μ`-measure of the agreement subdomain. -/
lemma agree_eq_mu_set_filter (μ : ι → Set.Icc (0 : ℚ) 1) (a b : ι → F) :
    agree μ a b = mu_set μ (univ.filter (fun i => a i = b i)) := by
  unfold agree mu_set; rfl

omit [Fintype ι] [Nonempty ι] [DecidableEq F] in
/-- Evaluating a polynomial curve (with `A = F`) at parameter `z` and coordinate `x` is the
pointwise power sum `∑ i, z ^ i * u i x`. -/
lemma polynomialCurveEval_apply {l : ℕ} (u : Fin (l + 2) → ι → F) (z : F) (x : ι) :
    Curve.polynomialCurveEval (F := F) (A := F) u z x = ∑ i : Fin (l + 2), z ^ (i : ℕ) * u i x := by
  unfold Curve.polynomialCurveEval; rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply, smul_eq_mul])

omit [Fintype ι] [Nonempty ι] [DecidableEq F] in
/-- The coordinate-wise difference polynomial
`P_x(z) = ∑ i, (u i x - v i x) * z ^ i` has degree at most `l + 1`. -/
lemma diffPoly_natDegree_le {l : ℕ} (u v : Fin (l + 2) → ι → F) (x : ι) :
    (∑ i : Fin (l + 2), Polynomial.C (u i x - v i x) * Polynomial.X ^ (i : ℕ)).natDegree
      ≤ l + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc (Polynomial.C (u i x - v i x) * Polynomial.X ^ (i : ℕ)).natDegree
      ≤ (i : ℕ) := by refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_; simp
    _ ≤ l + 1 := by omega

omit [Fintype ι] [Nonempty ι] [DecidableEq F] in
/-- Evaluating the difference polynomial at `z` recovers
`w x z - wtilde x z`, the gap between the two curve evaluations at coordinate `x`. -/
lemma diffPoly_eval {l : ℕ} (u v : Fin (l + 2) → ι → F) (x : ι) (z : F) :
    (∑ i : Fin (l + 2), Polynomial.C (u i x - v i x) * Polynomial.X ^ (i : ℕ)).eval z
      = Curve.polynomialCurveEval (F := F) (A := F) u z x
        - Curve.polynomialCurveEval (F := F) (A := F) v z x := by
  rw [polynomialCurveEval_apply, polynomialCurveEval_apply, Polynomial.eval_finset_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring)

omit [Fintype ι] [Nonempty ι] [DecidableEq F] in
/-- At a coordinate `x` where the lists disagree in some component, the difference
polynomial is not identically zero. -/
lemma diffPoly_ne_zero {l : ℕ} (u v : Fin (l + 2) → ι → F) (x : ι)
    (hx : ¬ (∀ i, u i x = v i x)) :
    (∑ i : Fin (l + 2), Polynomial.C (u i x - v i x) * Polynomial.X ^ (i : ℕ)) ≠ 0 := by
  intro hzero; apply hx; intro i
  have hcoeff :
      (∑ j : Fin (l + 2), Polynomial.C (u j x - v j x) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ)
        = u i x - v i x := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]; simp
    · intro j _ hji
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact sub_eq_zero.mp hcoeff.symm

omit [Nonempty ι] [DecidableEq F] in
/-- A nonzero polynomial has at most `natDegree`-many roots inside any finite set. -/
lemma card_le_natDegree_of_eval_zero (p : Polynomial F) (hp : p ≠ 0) (S : Finset F)
    (hS : ∀ z ∈ S, p.eval z = 0) : S.card ≤ p.natDegree := by
  classical
  have hsub : S ⊆ p.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hS z hz
  calc S.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

omit [Fintype ι] [Nonempty ι] in
/-- **Key fiber bound.** At a coordinate `x` where the two lists disagree in some component,
the number of curve parameters `z ∈ S'` at which the two curve evaluations agree is at most
`l + 1` (the degree bound of the difference polynomial). -/
lemma badCoord_match_card_le {l : ℕ} (u v : Fin (l + 2) → ι → F) (x : ι)
    (hx : ¬ (∀ i, u i x = v i x)) (S' : Finset F) :
    (S'.filter (fun z => Curve.polynomialCurveEval (F := F) (A := F) u z x
        = Curve.polynomialCurveEval (F := F) (A := F) v z x)).card ≤ l + 1 := by
  set p := ∑ i : Fin (l + 2), Polynomial.C (u i x - v i x) * Polynomial.X ^ (i : ℕ) with hp_def
  have hp_ne : p ≠ 0 := diffPoly_ne_zero u v x hx
  have hroots : ∀ z ∈ S'.filter (fun z => Curve.polynomialCurveEval (F := F) (A := F) u z x
        = Curve.polynomialCurveEval (F := F) (A := F) v z x), p.eval z = 0 := by
    intro z hz; rw [Finset.mem_filter] at hz; rw [hp_def, diffPoly_eval, hz.2, sub_self]
  calc (S'.filter _).card ≤ p.natDegree := card_le_natDegree_of_eval_zero p hp_ne _ hroots
    _ ≤ l + 1 := diffPoly_natDegree_le u v x

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- Double-counting (Fubini) identity: summing a weight `g` over the agreement set
`{x | R x z}` and then over `z ∈ S'` equals summing, over each coordinate `x`, the weight
`g x` times the number of parameters `z ∈ S'` at which the relation `R x z` holds. -/
lemma sum_filter_sum_eq (S' : Finset F) (R : ι → F → Prop)
    [∀ x, DecidablePred (R x)] (g : ι → ℝ) :
    (∑ z ∈ S', ∑ x ∈ univ.filter (fun x => R x z), g x)
      = ∑ x : ι, g x * (S'.filter (fun z => R x z)).card := by
  have step1 : ∀ z ∈ S', (∑ x ∈ univ.filter (fun x => R x z), g x)
      = ∑ x : ι, (if R x z then g x else 0) := fun z _ => by rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Nonempty ι] in
/-- With integral weights (each `μ i` a multiple of `1/M`), the `μ`-measure `mu_set μ s` is a
multiple of `1 / (M * card ι)`: explicitly `(∑_{i ∈ s} n i) / (M * card ι)`, where
`μ i = n i / M`. -/
lemma mu_set_eq_div (μ : ι → Set.Icc (0 : ℚ) 1) {M : ℕ}
    (n : ι → ℤ) (hn : ∀ i, (μ i).1 = (n i : ℚ) / (M : ℚ)) (s : Finset ι) :
    mu_set μ s = ((∑ i ∈ s, n i : ℤ) : ℝ) / ((M : ℝ) * (Fintype.card ι : ℝ)) := by
  have hsum : (∑ i ∈ s, (μ i).1) = ((∑ i ∈ s, n i : ℤ) : ℚ) / (M : ℚ) := by
    rw [Finset.sum_congr rfl (fun i _ => hn i), ← Finset.sum_div]; push_cast; rfl
  unfold mu_set
  rw [hsum]; push_cast
  rw [div_mul_eq_div_div_swap]; ring

end ListAgreementLemmas

end WeightedAgreement

end ProximityGap
