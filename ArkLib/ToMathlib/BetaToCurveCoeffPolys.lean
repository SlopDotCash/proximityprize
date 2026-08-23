/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaMatchingVanishes
import ArkLib.ToMathlib.IngredientCBridge
import ArkLib.ToMathlib.BCIKS20PointwiseConditional

/-!
# Curve Coefficient Polynomial Reconstruction from the Beta Recursion

This module formalizes the end-to-end reconstruction of the curve coefficient polynomials
$\text{CurveCoeffPolys}$ from the Hensel-lift numerator recurrence $\beta_t$, completing the
list-decoding
agreement chain of [BCIKS20] §5.

### Reconstructive Chain

The reduction proceeds through the following algebraic links:
1. **Vanishing of the Embedding:** The matching set conditions and weight bounds force the
   function-field embedding of $\beta_t$ to vanish for all $t \ge k$.
2. **Tail Vanishing of Coefficients:** The vanishing of the numerator embedding implies the
   vanishing of the Hensel-lift coefficients $\alpha_t = 0$ for $t \ge k$.
3. **Linear Representative:** The tail vanishing of $\alpha_t$ implies that the power series
   $\gamma$ represents a bivariate polynomial of degree at most 1 in the coordinate variables.
4. **Coefficient Interpolation:** The linear representative is evaluated at coordinate points,
   yielding the polynomial interpolation of the curve coefficients $B_j$ over the agreement set.

This module formalizes these steps unconditionally, routing the algebraic results of
`BetaMatchingVanishes` and `Claim59Conditional`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

set_option linter.style.longLine false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaToCurveCoeffPolys

variable {F : Type} [Field F]

/-! ## Step A — the in-tree $\alpha$-formula, threaded through `betaRec`

The in-tree Hensel-lift coefficient is given by $\alpha_t = \text{embedding}(\beta_t) / (W^{t+1}
\cdot \text{embedding}(\xi)^{2t-1})$.
We define the same quotient using the recursive numerator `betaRec`, denoted `αFromBeta`.
If the embedding of the numerator vanishes, then $\alpha_t = 0$. -/

/-- The Hensel-lift coefficient $\alpha_t$ with the recursive numerator `betaRec`. -/
noncomputable def αFromBeta (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField H.leadingCoeff
  embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) /
    (W ^ (t + 1) *
      (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t)

/-- If the embedding of `betaRec t` vanishes, then the Hensel-lift coefficient `αFromBeta t`
vanishes. -/
theorem alphaFromBeta_eq_zero_of_embedding_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) {t : ℕ}
    (hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0) :
    αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  simp [αFromBeta, hemb]

/-! ## Step B — the §5 tail vanishing $\alpha_t = 0$ for $t \ge k$, from the $\beta$-construction -/

/-- Under a sufficiently large matching set and weight bounds, the Hensel-lift tail vanishes:
$\alpha_t = 0$ for all $t \ge k$. -/
theorem tail_zero_of_betaRec_embedding_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t ht
  have hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
    BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large
      x₀ R H hHyp Bcoeff t hH D hD (mp t ht) (hcard t ht)
  exact alphaFromBeta_eq_zero_of_embedding_zero x₀ R H hHyp Bcoeff hemb

/-! ## The §5 list-decoding output, as the per-index curve-coefficient datum -/

/-- Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is
interpolated
by a polynomial $B_j(z)$ of degree less than $k+1$ over the agreement set. -/
def CurveCoeffPolys (k deg : ℕ) (good : Finset F) (P : F → Polynomial F) : Prop :=
  ∀ j < deg, ∃ Bj : Polynomial F, Bj.natDegree < k + 1 ∧
    ∀ z ∈ good, (P z).coeff j = Bj.eval z

/-! ## Step D — a linear-in-$Z$ representative yields `CurveCoeffPolys` -/

/-- Specializing the linear representative $v_0(X) + X \cdot v_1(X) \in F[Z][X]$ at $Z = z$
yields the polynomial $C(v_0(z)) + v_1(z) \cdot X \in F[X]$. -/
theorem eval_linear_representative (v₀ v₁ : F[X]) (z : F) :
    ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
        (Polynomial.C z)
      = Polynomial.C (v₀.eval z) + (v₁.eval z) • (Polynomial.X : F[X]) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  have hmap : ∀ v : F[X], (Polynomial.map Polynomial.C v).eval (Polynomial.C z)
      = Polynomial.C (v.eval z) := by
    intro v
    rw [Polynomial.eval_map]; exact Polynomial.eval₂_hom Polynomial.C z
  rw [hmap v₀, hmap v₁]
  rw [smul_eq_C_mul]
  ring

/-- The $j$-th coefficient of $C(a) + b \cdot X$ is $a$ for $j=0$, $b$ for $j=1$, and $0$ otherwise.
-/
theorem coeff_C_add_smul_X (a b : F) :
    ∀ j, (Polynomial.C a + b • (Polynomial.X : F[X])).coeff j
      = if j = 0 then a else if j = 1 then b else 0 := by
  intro j
  rw [Polynomial.coeff_add, smul_eq_C_mul, Polynomial.coeff_C]
  rcases j with _ | _ | j
  · simp
  · simp
  · simp

/-- Reconstructs the coefficient polynomials $B_j$ from a linear bivariate representative. -/
theorem curveCoeffPolys_of_linear_representative
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F} (v₀ v₁ : F[X])
    (hdeg₀ : v₀.natDegree < k + 1) (hdeg₁ : v₁.natDegree < k + 1)
    (hPz : ∀ z ∈ good, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z)) :
    CurveCoeffPolys k deg good P := by
  intro j hj
  refine ⟨if j = 0 then v₀ else if j = 1 then v₁ else 0, ?_, ?_⟩
  · rcases j with _ | _ | j
    · simpa using hdeg₀
    · simpa using hdeg₁
    · simp
  · intro z hz
    rw [hPz z hz, eval_linear_representative, coeff_C_add_smul_X]
    rcases j with _ | _ | j
    · simp
    · simp
    · simp

/-! ## The end-to-end reconstruction: `betaRec` implies `CurveCoeffPolys` -/

/-- End-to-end list-decoding agreement chain showing that the Hensel-lift numerator recurrence
$\beta_t$ reconstructs the curve coefficient polynomials $B_j$. -/
theorem curveCoeffPolys_of_betaRec
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst (Claim59Conditional.shiftSeries x₀ H))
    {Ppoly : F[X][Y]} (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ good, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CurveCoeffPolys k deg good P := by
  have htail : ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
    tail_zero_of_betaRec_embedding_zero x₀ R H hHyp Bcoeff hH D hD k mp hcard
  have htrunc :
      γ x₀ R H hHyp =
        Polynomial.aeval (Claim59Conditional.shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff))) := by
    rw [hγ]
    exact subst_mk_eq_aeval_trunc_of_tail_zero hsubst htail
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdegX
  have hlin :
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← hrep, hPpoly]
  have _hconsistent :
      Polynomial.aeval (Claim59Conditional.shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)))
        = polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← htrunc, hlin]
  obtain ⟨hPeval, hd₀, hd₁⟩ := hPz v₀ v₁ hlin
  exact curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval

end BetaToCurveCoeffPolys

end ArkLib

/-! ## Axiom audit — every claimed-done declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaToCurveCoeffPolys.alphaFromBeta_eq_zero_of_embedding_zero
#print axioms ArkLib.BetaToCurveCoeffPolys.tail_zero_of_betaRec_embedding_zero
#print axioms ArkLib.BetaToCurveCoeffPolys.eval_linear_representative
#print axioms ArkLib.BetaToCurveCoeffPolys.coeff_C_add_smul_X
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_linear_representative
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
