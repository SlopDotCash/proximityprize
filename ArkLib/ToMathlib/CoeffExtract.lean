/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaMatchingVanishes

/-!
# Coefficient Extraction for Power Series Solutions

This module formalizes the coefficient extraction step (corresponding to the `coeffExtract` field
of `BetaMatchingVanishes.MatchingPoint` / brick L12). Specifically, it relates the equality of two
power series (e.g., arising from Hensel uniqueness) to the vanishing of specific algebraic terms
in the recurrence.

## Mathematical Context

Let $F$ be a field, and let $H \in F[X][Y]$ be an irreducible polynomial defining an algebraic
curve.
In the Hensel lifting context, uniqueness properties establish the equality of two power series
$$a_\beta = a_P$$
under a specialization map $\pi_z$.

By extracting the $t$-th coefficient of these power series, we thread the relation:
$$\alpha_t = \frac{\text{betaRec}(t)}{W^{t+1} \cdot \xi^{e_t}}$$
where $W$ and $\xi$ are non-zero elements. Extracting the coefficient at $(X - x_0)^t$ translates
the power-series level identity into a scalar-level vanishing condition:
$$\pi_z(\text{betaRec}(t)) = 0$$

## Key Formalizations
* `coeff_extract_scalar`: Distills the coefficient extraction process to bare field arithmetic.
* `coeff_extract_betaRec`: Connects the algebraic relation of $\alpha_t$ with the specialized power
series,
  yielding the vanishing of the recurrence term.
* `MatchingPoint.mk_coeffExtract`: A constructor wrapper for matching point verification in the
  proximity gap argument.
-/

set_option linter.style.longLine false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 PowerSeries

namespace ArkLib

namespace CoeffExtract

/-! ### Field-Level Coefficient Extraction Core -/

/-- Core coefficient extraction lemma. If two power series are equal, and their $t$-th coefficients
are given by $s/D$ (with $D \neq 0$) and $0$ respectively, then the numerator $s$ must vanish. -/
theorem coeff_extract_scalar {k : Type*} [Field k]
    {aβ aP : PowerSeries k} (t : ℕ) {s D : k}
    (hαβ : PowerSeries.coeff t aβ = s / D) (hD : D ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    s = 0 := by
  have hcoeff : PowerSeries.coeff t aβ = PowerSeries.coeff t aP := by rw [heq]
  rw [hαβ, haP] at hcoeff
  exact (div_eq_zero_iff.mp hcoeff).resolve_right hD

/-- Repackaging of `coeff_extract_scalar` where the denominator $D$ is given as a product of powers
of two non-zero elements. -/
theorem coeff_extract_scalar_prod {k : Type*} [Field k]
    {aβ aP : PowerSeries k} (t : ℕ) {s w x : k} (a e : ℕ)
    (hαβ : PowerSeries.coeff t aβ = s / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    s = 0 :=
  coeff_extract_scalar t hαβ (mul_ne_zero (pow_ne_zero a hw) (pow_ne_zero e hx)) haP heq

end CoeffExtract

namespace BetaMatchingVanishes

variable {F : Type} [Field F]

/-! ### Specialized Matching Point Coefficient Extraction -/

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {t : ℕ}
    {z : F} {root : rationalRoot (H_tilde' H) z}

/-- Evaluates the $t$-th coefficient of the recurrence relation under the specialization $\pi_z$.
Using the specialized coefficient identity and the vanishing of the proximate series term,
the uniqueness relation $a_\beta = a_P$ implies the vanishing of the specialized recurrence term. -/
theorem coeff_extract_betaRec
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0) :
    aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  fun heq => CoeffExtract.coeff_extract_scalar_prod t a e hαβ hw hx haP heq

/-- Constructor helper to populate the `coeffExtract` field of a `MatchingPoint`. -/
theorem MatchingPoint.mk_coeffExtract
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0) :
    aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  coeff_extract_betaRec hαβ hw hx haP

/-- Combines Hensel uniqueness and coefficient extraction to deduce the vanishing of the specialized
recurrence term. -/
theorem pi_z_betaRec_eq_zero_of_bridge
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP : PowerSeries.coeff t aP = 0)
    (heq : aβ = aP) :
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  coeff_extract_betaRec hαβ hw hx haP heq

end BetaMatchingVanishes

end ArkLib

