/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.CS25DeepHoleFinish

/-!
# CS25 "Claim 3" Deep-Hole Probability Accounting

This module completes the proof of the proximity gap reduction step for Reed-Solomon codes,
specifically
discharging the probabilistic residual (`DeepHoleProbResidual`) from Theorem 2 ("Claim 3") of [CS25]
(Crites–Stewart, 2025). We show that the probabilistic bound is controlled by a single geometric
condition: the "joint-far" property of the deep-hole stack.

## Mathematical Formulation

Let $\iota$ be a finite set of evaluation points, $F$ a finite field, and $C = \mathrm{RS}[k]
\subset F^\iota$
be the Reed-Solomon code of rate $k/n$. Let $u: \iota \to F$ be a received word, and $a \in F
\setminus \mathrm{range}(\text{domain})$
be a deep hole. Let $\{p_j\}_{j=1}^L \subset F[X]$ be a list of polynomials of degree less than
$k+1$
whose evaluations are close to $u$ in relative Hamming distance.

The **deep-hole stack** $u_{\mathrm{dh}} = (u_0, u_1)$ is defined by:
$$u_0(i) = \frac{u(i)}{\text{domain}(i) - a}, \quad u_1(i) = \frac{1}{\text{domain}(i) - a}$$
For any combining coefficient $\gamma \in F$, the linear combination is:
$$u_0 + \gamma u_1 = \frac{u + \gamma}{\text{domain} - a}$$
which corresponds to the deep-hole line at $\gamma$.

By relating the closeness of $u$ to the list $\{p_j\}$ with the closeness of the deep-hole line
to the code $\mathrm{RS}[k]$, we prove that the uniform probability of the deep-hole line being
close
to the code is bounded below by:
$$\text{Pr}_{\gamma \leftarrow F} [\delta_{\mathrm{r}}(u_0 + \gamma u_1, \mathrm{RS}[k]) \le \delta]
\ge \frac{\text{numDistinct}(p, a)}{|F|}$$
where $\text{numDistinct}(p, a)$ is the number of distinct evaluations of the polynomials at the
hole $a$.

Under the hypothesis that the deep-hole stack is not jointly close to the code (packaged as the
`DeepHoleJointFar` predicate), this probability is bounded above by the correlated agreement error
$\varepsilon_{\mathrm{ca}}$. We thereby derive the final list-size bound.

## References
* [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*, eprint 2025/2046.
* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25.DeepHole

open scoped NNReal ProbabilityTheory BigOperators ENNReal
open ProximityGap ListDecodable Polynomial Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The deep-hole stack and its line identity -/

/-- The first component of the deep-hole stack, defined by $u_0(i) = \frac{u(i)}{\text{domain}(i) -
a}$. -/
noncomputable def dhWord0 (domain : ι ↪ F) (u : ι → F) (a : F) : ι → F :=
  fun i => u i / (domain i - a)

/-- The second component of the deep-hole stack, defined by $u_1(i) = \frac{1}{\text{domain}(i) -
a}$. -/
noncomputable def dhWord1 (domain : ι ↪ F) (a : F) : ι → F :=
  fun i => 1 / (domain i - a)

/-- The deep-hole word stack $u_{\mathrm{dh}} = (u_0, u_1)$ of dimension 2. -/
noncomputable def dhStack (domain : ι ↪ F) (u : ι → F) (a : F) : WordStack F (Fin 2) ι :=
  ![dhWord0 domain u a, dhWord1 domain a]

@[simp] lemma dhStack_zero (domain : ι ↪ F) (u : ι → F) (a : F) :
    dhStack domain u a 0 = dhWord0 domain u a := rfl

@[simp] lemma dhStack_one (domain : ι ↪ F) (u : ι → F) (a : F) :
    dhStack domain u a 1 = dhWord1 domain a := rfl

/-- The line identity showing that the linear combination of the deep-hole stack components
equals the deep-hole line point. -/
theorem dhStack_line_eq (domain : ι ↪ F) (u : ι → F) (a γ : F) :
    dhStack domain u a 0 + γ • dhStack domain u a 1 = deepHoleLine domain u a γ := by
  funext i
  simp only [dhStack_zero, dhStack_one, dhWord0, dhWord1, deepHoleLine,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_one_div, add_div]

/-! ### Closeness transfer: each `z_j = −(p j).eval a` makes the line `δ`-close to `RS[k]` -/

/-- Closeness transfer lemma.
If the evaluation of $p$ is $\delta$-close to $u$ in relative Hamming distance, and the hole $a$
lies outside the domain, then the deep-hole line evaluated at $\gamma = -p(a)$ is $\delta$-close to
the Reed-Solomon code $RS[k]$. -/
theorem deepHoleLine_relClose_of_mem_ball
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X]) {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hp : p ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hmem : ReedSolomon.evalOnPoints domain p ∈ relHammingBall u δ) :
    δᵣ(deepHoleLine domain u a (-(p.eval a)),
        (ReedSolomon.code domain k : Set (ι → F))) ≤ δ.toNNReal := by
  -- The `RS[k]` codeword witness: `lineQuotient p a`.
  have hcw : ReedSolomon.evalOnPoints domain (lineQuotient p a)
      ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    lineQuotient_mem_RScode domain hp
  have hdist_eq :
      Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a))
        = Code.relHammingDist u (ReedSolomon.evalOnPoints domain p) :=
    relHammingDist_deepHoleLine_eq domain u a p hdom
  have hball : (Code.relHammingDist u (ReedSolomon.evalOnPoints domain p) : ℝ) ≤ δ := by
    have hmem' := hmem
    rw [relHammingBall, Set.mem_setOf_eq] at hmem'
    convert hmem' using 3
  have hle_real :
      (Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a)) : ℝ) ≤ δ := by
    rw [hdist_eq]; exact hball
  have hle_nn :
      Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a)) ≤ δ.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal δ hδ0]
    exact hle_real
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  exact ⟨_, hcw, hle_nn⟩

/-! ### The CA line-close event and the distinct-combiner count -/

/-- The event that the deep-hole line at combining coefficient $\gamma$ is $\delta$-close to the
code. -/
def caCloseEvent (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ) (γ : F) : Prop :=
  δᵣ(deepHoleLine domain u a γ, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ.toNNReal

open Classical in
/-- Show that the distinct values among the evaluation points at the hole $a$ map injectively
into the set of combining coefficients that satisfy the closeness event. -/
theorem numDistinct_le_card_caGood
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) :
    numDistinct p a ≤
      (Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ)).card := by
  classical
  have hcard_eq :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card = numDistinct p a := by
    rw [numDistinct]
    rw [show (fun j : Fin L => -(p j).eval a)
          = (fun x : F => -x) ∘ (fun j : Fin L => (p j).eval a) from rfl,
      ← Finset.image_image]
    exact Finset.card_image_of_injective _ neg_injective
  have hsub :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)) ⊆
        Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ) := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨j, -, rfl⟩ := hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact deepHoleLine_relClose_of_mem_ball domain u a (p j) hδ0 (hdeg j) hdom (hclose j)
  calc numDistinct p a = (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card := hcard_eq.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- Probability lower bound for the closeness event under the uniform distribution.
The probability that a uniformly chosen combining coefficient $\gamma \in F$ satisfies the closeness
event is at least $\text{numDistinct}(p, a) / |F|$. -/
theorem numDistinct_div_card_le_pr
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) :
    ((numDistinct p a : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) ≤
      (Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ]).toNNReal := by
  classical
  have hpr :
      Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ] =
        ((((Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ)).card : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [prob_uniform_eq_card_filter_div_card (F := F)
      (P := fun γ : F => caCloseEvent domain u a k δ γ)]
    rw [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero)]
  rw [hpr]
  rw [ENNReal.toNNReal_coe]
  gcongr
  exact_mod_cast numDistinct_le_card_caGood domain u a p hδ0 hdeg hdom hclose

/-! ### The joint-far condition and the `epsCA` bound -/

/-- The geometric condition certifying that the stack is not jointly $\delta$-close. -/
def DeepHoleJointFar (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ) : Prop :=
  ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F)))
      (u := dhStack domain u a) δ.toNNReal

/-- Upper bound on the closeness event probability by the correlated agreement error.
Under the joint-far condition, the probability that the deep-hole line is close to the code
is bounded above by the correlated agreement error $\varepsilon_{\mathrm{ca}}$. -/
theorem pr_caCloseEvent_le_epsCA
    (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ)
    (hjf : DeepHoleJointFar domain u a k δ) :
    Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ] ≤
      epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal := by
  classical
  refine le_trans (Pr_le_Pr_of_implies _ _ _ ?_)
    (line_close_probability_le_epsCA_of_not_jointProximity
      ((ReedSolomon.code domain k : Set (ι → F))) δ.toNNReal δ.toNNReal
      (dhStack domain u a) hjf)
  intro γ hγ
  rw [dhStack_line_eq]
  exact hγ

/-- The distinct combiner count is bounded by the correlated agreement error times the field size,
assuming the joint-far condition holds. -/
theorem numDistinct_le_eps_of_jointFar
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ)
    (hjf : DeepHoleJointFar domain u a k δ) :
    (numDistinct p a : ℝ) ≤
      (epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal).toReal * (Fintype.card F : ℝ) := by
  classical
  set eCA := epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
      δ.toNNReal δ.toNNReal with heCAdef
  have hεne : eCA ≠ ⊤ := by
    rw [heCAdef]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (Bridge.epsCA_le_one _ _ _)
  have h1 := numDistinct_div_card_le_pr domain u a p hδ0 hdeg hdom hclose
  have h2 : (Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ]).toNNReal ≤ eCA.toNNReal := by
    rw [heCAdef]
    exact ENNReal.toNNReal_mono hεne (pr_caCloseEvent_le_epsCA domain u a k δ hjf)
  have hchain : ((numDistinct p a : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ eCA.toNNReal :=
    le_trans h1 h2
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hchainR : (numDistinct p a : ℝ) / (Fintype.card F : ℝ) ≤ (eCA.toNNReal : ℝ) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast] at this
  rw [div_le_iff₀ hqpos] at hchainR
  rw [ENNReal.coe_toNNReal_eq_toReal] at hchainR
  exact hchainR

/-! ### Assembling `DeepHoleProbResidual` from the joint-far side condition -/

/-- Proof that the probabilistic residual `DeepHoleProbResidual` is discharged under the
joint-far hypothesis at every point in the sampling set. -/
theorem deepHoleProbResidual_of_jointFar
    (domain : ι ↪ F) (u : ι → F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hjf : ∀ a ∈ sampleSet domain, DeepHoleJointFar domain u a k δ) :
    DeepHoleProbResidual domain k L δ
      (epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal).toReal u p := by
  intro hdeg hclose a ha
  exact numDistinct_le_eps_of_jointFar domain u a p hδ0 hdeg
    (mem_sampleSet_imp_off_domain ha) hclose (hjf a ha)

/-- Final list-size bound for Reed-Solomon codes in the CS25 regime.
This theorem discharges the probabilistic residual to establish the list size upper bound,
under the assumption that the deep-hole stack satisfies the joint-far condition at every point
in the sampling set. -/
theorem rs_epsCA_implies_lambda_extended_cs25_jointFar
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hkn : k + 1 ≤ Fintype.card ι)
    (hs_pos : (0 : ℝ) < Fintype.card F - Fintype.card ι)
    (hδ0 : 0 ≤ δ)
    (hε_ca :
        (epsCA (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F)))
    (hjf :
      let ε := (epsCA (F := F) (A := F)
                  ((ReedSolomon.code domain k : Set (ι → F)))
                  δ.toNNReal δ.toNNReal).toReal
      let L0 : ℕ := Nat.ceil ((Fintype.card F : ℝ) / (1 - η) * ε)
      ∀ (u : ι → F) (a : F), a ∈ sampleSet domain → DeepHoleJointFar domain u a k δ) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCA (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  apply rs_epsCA_implies_lambda_extended_cs25_final
    domain k δ η hk_pos hη_lo hη_lt hkn hs_pos hε_ca
  intro ε L0 u p
  exact deepHoleProbResidual_of_jointFar domain u p hδ0 (fun a ha => hjf u a ha)

end CodingTheory.CS25.DeepHole

/- Axiom audit for the CS25 joint-far discharge of `DeepHoleProbResidual` (#22). -/
#print axioms CodingTheory.CS25.DeepHole.DeepHoleJointFar
#print axioms CodingTheory.CS25.DeepHole.pr_caCloseEvent_le_epsCA
#print axioms CodingTheory.CS25.DeepHole.numDistinct_le_eps_of_jointFar
#print axioms CodingTheory.CS25.DeepHole.deepHoleProbResidual_of_jointFar
#print axioms CodingTheory.CS25.DeepHole.rs_epsCA_implies_lambda_extended_cs25_jointFar
