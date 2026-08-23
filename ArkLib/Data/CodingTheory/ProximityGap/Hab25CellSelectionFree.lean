/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellPencilJohnson

/-!
# The selection is FREE for section-linked cells (#348, GK1 collapsed)

For the factor cells of the cell production, the §5 centre/branch selection — the
GK1 hypothesis of the portfolio, expected to need the Claim-5.6 discriminant-counting
move — is **free**: cell irreducibility together with the surface divisibility
`(Y′ − C w) ∣ R` (the `section_link` premises, already required) make `R` an associate
of the surface factor, so at EVERY centre `x₀`:

* the slice `evalX (C x₀) R` is a nonzero constant times the monic linear
  `Y − C (w.eval (C x₀))`;
* taking `H := Y − C (w.eval (C x₀))` gives a monic, irreducible, degree-one branch
  with `ClaimA2.Hypotheses x₀ R H` **by construction** — both fields
  (`dvd_evalX` and `separable_evalX`) computed outright.

No discriminant certificate, no good-centre counting, no per-cell case analysis: the
irreducibility that defines the cells already collapsed the slice to a single separable
linear branch.  This eliminates the GK1 selection leg of
`cell_improvement_of_pinning_package'` entirely; the remaining legs are the tail, the
heavy sets, and the numerics (GK3–GK5).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA.ClaimA2

namespace BCIKS20.CellSelectionFree

variable {F₀ : Type} [Field F₀]

/-- The canonical branch of a section-linked cell at the centre `x₀`: the monic linear
fiber factor of the surface. -/
noncomputable def sectionBranch (w : F₀[X][Y]) (x₀ : F₀) : F₀[X][Y] :=
  Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))

/-- The section branch is monic. -/
theorem sectionBranch_monic (w : F₀[X][Y]) (x₀ : F₀) :
    (sectionBranch w x₀).Monic :=
  Polynomial.monic_X_sub_C _

/-- The section branch has degree one. -/
theorem sectionBranch_natDegree (w : F₀[X][Y]) (x₀ : F₀) :
    (sectionBranch w x₀).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C _

/-- The section branch is irreducible (monic linear over a domain). -/
theorem sectionBranch_irreducible (w : F₀[X][Y]) (x₀ : F₀) :
    Irreducible (sectionBranch w x₀) := by
  refine Polynomial.Monic.irreducible_of_degree_eq_one ?_ (sectionBranch_monic w x₀)
  rw [sectionBranch, Polynomial.degree_X_sub_C]

/-- **The slice computation**: for irreducible `R` with the surface divisibility, the
slice at every centre is a nonzero `F₀`-constant times the section branch. -/
theorem evalX_eq_unit_mul_sectionBranch {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R) (x₀ : F₀) :
    ∃ a : F₀, a ≠ 0 ∧
      Bivariate.evalX (Polynomial.C x₀) R
        = Polynomial.C (Polynomial.C a) * sectionBranch w x₀ := by
  classical
  -- `R` is an associate of the surface factor
  have hXw_nu : ¬ IsUnit (Polynomial.X - Polynomial.C w) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc⟩ := hwdvd
  have hcu : IsUnit c := (hRirr.isUnit_or_isUnit hc).resolve_left hXw_nu
  -- the unit is a nonzero `F₀`-constant (units of the iterated polynomial ring)
  obtain ⟨q, hq⟩ := Polynomial.isUnit_iff.mp hcu
  obtain ⟨a, ha⟩ := Polynomial.isUnit_iff.mp hq.1
  obtain ⟨b, hb⟩ := Polynomial.isUnit_iff.mp ha.1
  have hb0 : b ≠ 0 := IsUnit.ne_zero hb.1
  refine ⟨b, hb0, ?_⟩
  -- compute the slice of `R = (Y − C w) * c`
  have hcval : c = Polynomial.C (Polynomial.C (Polynomial.C b)) := by
    rw [← hq.2, ← ha.2, ← hb.2]
  rw [hc, hcval, Bivariate.evalX_eq_map, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, sectionBranch]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C]
  ring

/-- **GK1 COLLAPSED: `ClaimA2.Hypotheses` holds by construction at every centre** for the
section branch of any section-linked cell — both fields computed from the slice. -/
theorem hypotheses_of_surface {R : (F₀[X])[X][Y]}
    (hRirr : Irreducible R) {w : F₀[X][Y]}
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R) (x₀ : F₀) :
    Hypotheses x₀ R (sectionBranch w x₀) := by
  obtain ⟨a, ha0, hslice⟩ := evalX_eq_unit_mul_sectionBranch hRirr hwdvd x₀
  constructor
  · -- dvd_evalX
    rw [hslice]
    exact Dvd.intro_left _ rfl
  · -- separable_evalX: a nonzero constant times a monic linear is separable
    rw [hslice]
    have hsep : (sectionBranch w x₀).Separable := by
      rw [sectionBranch]
      exact Polynomial.separable_X_sub_C
    have hunit : IsUnit (Polynomial.C (Polynomial.C a) : F₀[X][Y]) := by
      refine Polynomial.isUnit_C.mpr ?_
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha0)
    exact Polynomial.Separable.unit_mul hunit hsep

/-- The bundled `Fact` instances for consuming the package theorems at the section
branch. -/
theorem sectionBranch_facts (w : F₀[X][Y]) (x₀ : F₀) :
    Fact (Irreducible (sectionBranch w x₀)) ∧ Fact (0 < (sectionBranch w x₀).natDegree) :=
  ⟨⟨sectionBranch_irreducible w x₀⟩, ⟨by rw [sectionBranch_natDegree]; omega⟩⟩

end BCIKS20.CellSelectionFree

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CellSelectionFree.sectionBranch_irreducible
#print axioms BCIKS20.CellSelectionFree.evalX_eq_unit_mul_sectionBranch
#print axioms BCIKS20.CellSelectionFree.hypotheses_of_surface
