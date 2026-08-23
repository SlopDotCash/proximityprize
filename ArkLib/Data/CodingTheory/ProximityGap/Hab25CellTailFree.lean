/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellSelectionFree

/-!
# The tail is FREE for section-linked cells (#348, the graded-disc machinery collapsed)

At the section branch, the genuine Hensel root has an EXPLICIT closed form: it is the
recentred surface itself (`coeffHom x₀ H w` — the series whose order-`t` coefficient is
the lift of the `t`-th Taylor coefficient of `w`).  Uniqueness of the Hensel lift then
identifies `gammaGenuine` with it outright, and the Claim-5.8′ coefficient tail follows
from nothing but the surface's degree bound:

* `alpha0_sectionBranch` — `α₀ = lift (w.eval (C x₀))` at the section branch (monic, so
  `α₀ = T`, and the defining relation evaluates the linear branch);
* `Q_eval_coeffHom` — the recentred surface is a root of the genuine `Q` (the map
  computation through `R = (Y − C w) · unit`);
* **`gammaGenuine_eq_coeffHom`** — the genuine root IS the recentred surface
  (`gammaGenuine_unique`);
* `alphaGenuine_eq_lift_taylor` — every genuine coefficient is the lifted Taylor
  coefficient;
* **`htail_of_surface`** — the Claim-5.8′ tail `∀ t ≥ n, αGenuine t = 0` from
  `w.natDegree < n` ALONE: no graded budgets, no discriminant cover, no matching sets,
  no `Ppoly` representative.

With GK1 (`hypotheses_of_surface`) and this file, the per-cell package of
`cell_improvement_of_pinning_package'` loses its `hHyp` and `htail` legs to pure
construction; what remains is the heavy/agreement data (matching sets, fold readings,
weight, cardinality) — the genuinely quantitative §5 content.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.CellSelectionFree

namespace BCIKS20.CellTailFree

variable {F₀ : Type} [Field F₀]

/-- **`α₀` at the section branch is the lifted base value.**  The defining vanishing
`eval₂ lift α₀ H = 0` evaluates the linear branch to `α₀ − lift (w.eval (C x₀))`. -/
theorem alpha0_sectionBranch (w : F₀[X][Y]) (x₀ : F₀)
    [Fact (Irreducible (sectionBranch w x₀))]
    [Fact (0 < (sectionBranch w x₀).natDegree)] :
    α₀ (sectionBranch w x₀)
      = liftToFunctionField (H := sectionBranch w x₀) (w.eval (Polynomial.C x₀)) := by
  have h : Polynomial.eval₂ (liftToFunctionField (H := sectionBranch w x₀))
      (α₀ (sectionBranch w x₀))
      (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) = 0 :=
    eval₂_H_α₀ (H := sectionBranch w x₀)
  rw [Polynomial.eval₂_sub (liftToFunctionField (H := sectionBranch w x₀))
      (p := Polynomial.X) (q := Polynomial.C (w.eval (Polynomial.C x₀))),
    Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at h
  exact h

/-- **The recentred surface is a root of the genuine `Q`** (the map computation through
`R = (Y − C w) · unit`). -/
theorem Q_eval_coeffHom {R : (F₀[X])[X][Y]} {w : F₀[X][Y]} {c : (F₀[X])[X][Y]}
    (hc : R = (Polynomial.X - Polynomial.C w) * c) (x₀ : F₀)
    {H : F₀[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    Polynomial.eval (coeffHom x₀ H w) (Q x₀ R H) = 0 := by
  rw [Q, hc, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, zero_mul]

/-- **The genuine Hensel root at the section branch IS the recentred surface**
(uniqueness of the Hensel lift at the shared base datum). -/
theorem gammaGenuine_eq_coeffHom {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R) (x₀ : F₀)
    [Fact (Irreducible (sectionBranch w x₀))]
    [Fact (0 < (sectionBranch w x₀).natDegree)] :
    gammaGenuine x₀ R (sectionBranch w x₀) (hypotheses_of_surface hRirr hwdvd x₀)
      = coeffHom x₀ (sectionBranch w x₀) w := by
  have hwdvd' := hwdvd
  obtain ⟨c, hc⟩ := hwdvd'
  refine (gammaGenuine_unique (hypotheses_of_surface hRirr hwdvd x₀) ?_ ?_).symm
  · rw [constantCoeff_coeffHom, alpha0_sectionBranch]
  · exact Q_eval_coeffHom hc x₀

/-- **Every genuine coefficient is the lifted Taylor coefficient of the surface.** -/
theorem alphaGenuine_eq_lift_taylor {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R) (x₀ : F₀)
    [Fact (Irreducible (sectionBranch w x₀))]
    [Fact (0 < (sectionBranch w x₀).natDegree)] (t : ℕ) :
    BCIKS20.HenselNumerator.αGenuine (sectionBranch w x₀) x₀ R
        (hypotheses_of_surface hRirr hwdvd x₀) t
      = liftToFunctionField (H := sectionBranch w x₀)
          ((Polynomial.taylor (Polynomial.C x₀) w).coeff t) := by
  rw [BCIKS20.HenselNumerator.αGenuine, gammaGenuine_eq_coeffHom hRirr hwdvd x₀,
    coeff_coeffHom]

/-- **THE TAIL IS FREE**: the Claim-5.8′ coefficient tail at the section branch from the
surface degree bound alone — no graded budgets, no discriminant cover, no matching sets. -/
theorem htail_of_surface {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]} {n : ℕ} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R) (x₀ : F₀)
    [Fact (Irreducible (sectionBranch w x₀))]
    [Fact (0 < (sectionBranch w x₀).natDegree)] :
    ∀ t, n ≤ t →
      BCIKS20.HenselNumerator.αGenuine (sectionBranch w x₀) x₀ R
        (hypotheses_of_surface hRirr hwdvd x₀) t = 0 := by
  intro t ht
  rw [alphaGenuine_eq_lift_taylor hRirr hwdvd x₀ t]
  have hcoeff : (Polynomial.taylor (Polynomial.C x₀) w).coeff t = 0 := by
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    rw [Polynomial.natDegree_taylor]
    omega
  rw [hcoeff, map_zero]

end BCIKS20.CellTailFree

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CellTailFree.alpha0_sectionBranch
#print axioms BCIKS20.CellTailFree.gammaGenuine_eq_coeffHom
#print axioms BCIKS20.CellTailFree.alphaGenuine_eq_lift_taylor
#print axioms BCIKS20.CellTailFree.htail_of_surface
