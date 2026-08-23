/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25K4FiberReduction

/-!
# The per-coordinate fold capture — the first half of BCIKS20 Claim 5.10

The named open residual of #302 is `CoordinateUpgrade` (Claim 5.10). Its proof in the
paper has two halves: (i) at each rich coordinate `x`, the **fold section divides the
fiber**, `(Y − w(x,Z)) ∣ R(x,Y,Z)` — an *elementary* degree count once the interpolant
carries the **sloped** `(Y,Z)`-budget of `GSInterpolantSloped.lean`; (ii) the analytic
assembly of the per-coordinate identities into the global branch (Lemma A.1 + Claim A.2,
the Λ-weight kernel). This file proves half (i):

* `eval_fold_specializes` — evaluating `Y` at the section then specializing `Z` equals
  specializing first (the one-level-down `eval_specializes`);
* `fiberAt_coeff_natDegree_le_sloped` — the slope descends to fibers (evaluation of the
  mid variable at a constant cannot raise `Z`-degrees);
* **`fold_divides_fiber_of_many_agreements`** — THE capture: a `Z`-linear section
  agreeing with a root of the specialized fiber at more than `D_YZ` scalars is a root of
  the fiber **identically in `Z`**. The slope is load-bearing: the defect
  `δ(Z) = G(w(Z), Z)` has each term `coeff_b·w^b` of degree
  `≤ (D_YZ − b) + b·1 = D_YZ` — *uniform in `b`* exactly because the budget slopes.
  Without the slope (flat budget `B`), the defect degree is `B + d` and grows with the
  `Y`-degree; with it the count closes at the interpolant's own budget;
* `fold_section_dvd_fiber` — the factor-theorem corollary `(Y − C w) ∣ G`.

What remains of Claim 5.10 is half (ii) alone: the per-coordinate identities assemble to
the global branch through the Hensel series (the fold rows are words, not polynomials,
so the branch is a priori only analytic — bounding its series coefficients is the
Λ-weight content).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- Evaluating `Y` at a section then specializing `Z` equals specializing first and
evaluating at the specialized section value. -/
lemma eval_fold_specializes (G : F₀[X][Y]) (w : F₀[X]) (γ : F₀) :
    (Polynomial.eval w G).eval γ =
      Polynomial.eval (w.eval γ) (G.map (Polynomial.evalRingHom γ)) := by
  have h := Polynomial.hom_eval₂ G (RingHom.id F₀[X]) (Polynomial.evalRingHom γ) w
  rw [RingHom.comp_id] at h
  rw [show Polynomial.eval w G = Polynomial.eval₂ (RingHom.id F₀[X]) w G from rfl,
    Polynomial.eval_map]
  exact h

/-- The slope descends to fibers: if `deg_Z((R.coeff b).coeff a) ≤ D_YZ − b` for every
`a`, then `deg_Z((fiberAt x₀ R).coeff b) ≤ D_YZ − b` — evaluating the mid variable at
the constant `x₀` cannot raise `Z`-degrees. -/
lemma fiberAt_coeff_natDegree_le_sloped {R : (F₀[X])[X][Y]} {DYZ : ℕ}
    (hB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ DYZ - b) (x₀ : F₀) (b : ℕ) :
    ((fiberAt x₀ R).coeff b).natDegree ≤ DYZ - b := by
  have hcoeff : (fiberAt x₀ R).coeff b = (R.coeff b).eval (Polynomial.C x₀) := by
    rw [fiberAt, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coe_evalRingHom]
  rw [hcoeff, Polynomial.eval_eq_sum_range]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  have h1 : ((Polynomial.C x₀ : F₀[X]) ^ a).natDegree = 0 := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C, mul_zero]
  rw [h1, add_zero]
  exact hB b a

/-- **The per-coordinate fold capture (BCIKS20 Claim 5.10, first half).** A `Z`-linear
section `w` agreeing with a root of the specialized fiber at more than `D_YZ` scalars is
a root of the fiber identically: the defect `G(w(Z), Z)` has degree `≤ D_YZ` —
**uniformly in the `Y`-exponent, by the slope** — and vanishes at too many points. -/
theorem fold_divides_fiber_of_many_agreements
    {G : F₀[X][Y]} {DYZ : ℕ} (hdY : G.natDegree ≤ DYZ)
    (hslope : ∀ b : ℕ, (G.coeff b).natDegree ≤ DYZ - b)
    {w : F₀[X]} (hw : w.natDegree ≤ 1)
    (S : Finset F₀) (hcard : DYZ < S.card)
    (hvan : ∀ γ ∈ S, (G.map (Polynomial.evalRingHom γ)).eval (w.eval γ) = 0) :
    Polynomial.eval w G = 0 := by
  classical
  set δ : F₀[X] := Polynomial.eval w G with hδ
  -- the sloped defect degree: every term is uniformly `≤ D_YZ`
  have hδdeg : δ.natDegree ≤ DYZ := by
    rw [hδ, Polynomial.eval_eq_sum_range]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := hslope b
    have h2 : (w ^ b).natDegree ≤ b := by
      refine le_trans (Polynomial.natDegree_pow_le) ?_
      calc b * w.natDegree ≤ b * 1 := Nat.mul_le_mul_left b hw
        _ = b := Nat.mul_one b
    have hble : b ≤ DYZ :=
      le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hdY
    omega
  -- the defect vanishes at every scalar of `S`
  have hδvan : ∀ γ ∈ S, δ.eval γ = 0 := by
    intro γ hγ
    rw [hδ, eval_fold_specializes]
    exact hvan γ hγ
  -- too many roots
  by_contra hδ0
  have hsub : S ⊆ δ.roots.toFinset := by
    intro γ hγ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hδ0]
    exact hδvan γ hγ
  have hle : S.card ≤ DYZ :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' _) hδdeg))
  omega

/-- The factor-theorem corollary: the fold section **divides the fiber**. -/
theorem fold_section_dvd_fiber
    {G : F₀[X][Y]} {DYZ : ℕ} (hdY : G.natDegree ≤ DYZ)
    (hslope : ∀ b : ℕ, (G.coeff b).natDegree ≤ DYZ - b)
    {w : F₀[X]} (hw : w.natDegree ≤ 1)
    (S : Finset F₀) (hcard : DYZ < S.card)
    (hvan : ∀ γ ∈ S, (G.map (Polynomial.evalRingHom γ)).eval (w.eval γ) = 0) :
    (Polynomial.X - Polynomial.C w) ∣ G :=
  Polynomial.dvd_iff_isRoot.mpr
    (fold_divides_fiber_of_many_agreements hdY hslope hw S hcard hvan)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms eval_fold_specializes
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fiberAt_coeff_natDegree_le_sloped
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fold_divides_fiber_of_many_agreements
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fold_section_dvd_fiber
