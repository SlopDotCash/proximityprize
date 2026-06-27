/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HighMultiplicityBadCount
import ArkLib.Data.CodingTheory.ProximityGap.RatioValueMultiplicity

/-!
# Bridge: polynomial error lines are degree-collapsed (#389, face (iv) closure of the local step)

`HighMultiplicityBadCount.highMult_empty_of_lt` vanishes the per-error-line bad set once the
demanded agreement exceeds the maximum multiplicity `D` of the line's ratio.
`RatioValueMultiplicity.value_mult_le_max` bounds that multiplicity by `max(deg P, deg Q)` when the
ratio is a genuine rational function.  This file connects them: when the two error coordinates are
**low-degree polynomial evaluations** `e₀ i = P(dom i)`, `e₁ i = Q(dom i)` on an injective domain
`dom` (the Reed–Solomon / GRS case), the incidence multiplicity `mult` is itself degree-bounded,

> `mult e₀ e₁ γ ≤ max(deg P, deg Q)`   whenever `P + γ·Q ≢ 0`   (`mult_poly_le_max`),

so the degree-collapse fires unconditionally: `highMult_empty_of_lt` then gives **no bad scalar**
once `max(deg P, deg Q) < μ₀` (`badScalars_empty_of_degree`).

This is the local certificate H-EXT consumes (`DISPROOF_LOG.md` O159): for a structured error line
(both coordinates bounded-degree polynomials on the domain) the per-pair supply collapses purely by
degree.  It does NOT bypass the open core — the open core is the case where the *stack* coordinate
`u₀` is an arbitrary word (no polynomial structure), so the ratio degree is unbounded and the
collapse does not apply; the structured case is precisely the one this certifies.  Axiom-clean.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.RatioMultiplicity

open ArkLib.ProximityGap.HighMultiplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] [Fintype F] in
/-- **A polynomial error line has degree-bounded multiplicity.**  If the error coordinates are
evaluations `e₀ i = P(dom i)`, `e₁ i = Q(dom i)` of polynomials on an injective domain `dom`, then
for every scalar `γ` with `P + γ·Q ≢ 0`, the incidence multiplicity is at most `max(deg P, deg Q)`.
The level set `{i : P(dom i) + γ·Q(dom i) = 0}` injects into the roots of the nonzero polynomial
`P + γ·Q`. -/
theorem mult_poly_le_max (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {γ : F} (h : P + C γ * Q ≠ 0) :
    mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ
      ≤ max P.natDegree Q.natDegree := by
  classical
  -- drop the `e₁ ≠ 0` conjunct: mult ≤ #{i : P(dom i) + γ·Q(dom i) = 0}
  have hstep1 :
      mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ
        ≤ (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) = 0)).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  -- transport the level set along the injective domain into `image dom`
  have hstep2 :
      (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) = 0)).card
        = ((univ.image dom).filter (fun x => P.eval x = (-γ) * Q.eval x)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hdom]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> intro hi <;> linear_combination hi
  -- the level set is a value-fibre of the ratio `P/Q`; bound it by the degree
  have hc : P - C (-γ) * Q ≠ 0 := by
    rwa [map_neg, neg_mul, sub_neg_eq_add]
  exact (hstep1.trans_eq hstep2).trans
    (value_mult_le_max P Q (-γ) hc (univ.image dom))

omit [DecidableEq ι] in
/-- **Degree-collapse for polynomial error lines.**  If the error coordinates are evaluations of
`P, Q` on an injective domain, and the demanded agreement `μ₀` exceeds `max(deg P, deg Q)`, then —
provided `P + γ·Q ≢ 0` for every scalar `γ` (no value of the ratio is identically attained) — there
is **no** bad scalar: the per-error-line bad set is empty.  The structured (bounded-degree) supply
collapses purely by degree. -/
theorem badScalars_empty_of_degree (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {μ₀ : ℕ} (hμ : max P.natDegree Q.natDegree < μ₀)
    (hnz : ∀ γ : F, P + C γ * Q ≠ 0) :
    univ.filter (fun γ : F =>
        μ₀ ≤ mult (fun i => P.eval (dom i)) (fun i => Q.eval (dom i)) γ) = ∅ :=
  highMult_empty_of_lt _ _ (fun γ => mult_poly_le_max dom hdom P Q (hnz γ)) hμ

omit [DecidableEq ι] in
/-- **Exact degree-collapse for weight-thresholded polynomial error lines.**  If the error
coordinates are polynomial evaluations and every ratio fibre has multiplicity at most
`max(deg P, deg Q)`, then the actual low-weight bad-scalar set is empty as soon as that degree is
below the exact required multiplicity

`#{Q ≠ 0 on dom} + #{Q = 0 ∧ P ≠ 0 on dom} - w`.

This composes `mult_poly_le_max` with
`HighMultiplicity.badWeight_empty_of_mult_cap_exact`, retaining the fixed zero-`Q` correction that
the older `badScalars_empty_of_degree` high-multiplicity form did not expose. -/
theorem badWeight_empty_of_degree_exact (dom : ι → F) (hdom : Function.Injective dom)
    (P Q : F[X]) {w : ℕ}
    (hdeg : max P.natDegree Q.natDegree <
      (univ.filter (fun i => Q.eval (dom i) ≠ 0)).card
        + (univ.filter (fun i => Q.eval (dom i) = 0 ∧ P.eval (dom i) ≠ 0)).card - w)
    (hnz : ∀ γ : F, P + C γ * Q ≠ 0) :
    univ.filter (fun γ : F =>
        (univ.filter (fun i => P.eval (dom i) + γ * Q.eval (dom i) ≠ 0)).card ≤ w) = ∅ :=
  badWeight_empty_of_mult_cap_exact
    (fun i => P.eval (dom i)) (fun i => Q.eval (dom i))
    (fun γ => mult_poly_le_max dom hdom P Q (hnz γ)) hdeg

end ArkLib.ProximityGap.RatioMultiplicity

#print axioms ArkLib.ProximityGap.RatioMultiplicity.badWeight_empty_of_degree_exact
