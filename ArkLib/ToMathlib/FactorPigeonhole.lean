/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.IncidenceBound

/-!
# Issue #304 — the factor pigeonhole: the §6 branch assignment with a cardinality LOWER bound

The F7/F8 self-audits established what the matching geometry **cannot** be (rational branch
separation; low-degree surfaces).  This file builds what it **is**: the honest [BCIKS20] §6
branch assignment.  At each good place `z`, the decoded surface's value roots the full GS
interpolant (`Q(z, v(z)) = 0` — the GS list-membership cargo); the interpolant factors as
`Q = ∏ᵢ Hᵢ`; over a field some factor vanishes at `(z, v(z))`; **pigeonhole over the factors**
hands one factor `Hᵢ` at least `|goodSet| / m` incidence places:

* `exists_vanishing_factor` — per-place factor selection (field: a vanishing product has a
  vanishing factor).
* `exists_factor_incidence_large` — **the pigeonhole**: some factor's incidence set inside the
  good set has cardinality `≥ n` whenever `m · n ≤ |goodSet|`.
* `incidenceRoot` / `incidenceRoot_val_monic` — on the selected factor's incidence set, the
  branch roots **with the base-point values** are constructed
  (`RationalRootSupply.rationalRoot_of_evalEval`); for monic factors the value is exactly the
  surface value, so the `hbase` field of `DecodedProximateRoot.mpFin_of_decoded` holds by
  construction — now in the membership-dependent form (total-root sections do not generally
  exist; cf. the rootOn repair).

This is the production of the matching set with the cardinality **lower** bound the counting
needs — the missing half that F8's upper bound gates: the §5 probability hypothesis makes the
good set `ε·q`-large, the pigeonhole transfers `(ε/m)·q`-largeness to one branch, and the
F8 gate is then *passed* because the genuine surface interpolates over that many places.

## References
* [BCIKS20] §5–§6 (the GS list at each good parameter; the factor/branch assignment by
  pigeonhole); Appendix A.5.2.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace FactorPigeonhole

variable {F : Type} [Field F]

/-! ## Per-place factor selection -/

/-- **A vanishing product has a vanishing factor** (field): if the full interpolant vanishes
at `(z, v(z))`, some factor does. -/
theorem exists_vanishing_factor {ι : Type*} {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) {v : F[X]} {z : F}
    (hvan : Polynomial.evalEval z (v.eval z) Q = 0) :
    ∃ i ∈ s, Polynomial.evalEval z (v.eval z) (Hf i) = 0 := by
  have h2 : (Polynomial.evalEvalRingHom z (v.eval z)) Q = 0 := hvan
  rw [hQ, map_prod] at h2
  exact Finset.prod_eq_zero_iff.mp h2

/-! ## The pigeonhole -/

/-- **The factor pigeonhole (the §6 branch assignment).**  If the interpolant `Q = ∏ᵢ Hᵢ`
vanishes at the surface value over every good place, then some factor's incidence set carries
at least `n` places, whenever `m · n ≤ |goodSet|`. -/
theorem exists_factor_incidence_large {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet, Polynomial.evalEval z (v.eval z) Q = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card) :
    ∃ i ∈ s, n ≤
      (goodSet.filter (fun z => Polynomial.evalEval z (v.eval z) (Hf i) = 0)).card := by
  classical
  -- per-place factor choice
  have hex : ∀ z ∈ goodSet, ∃ i ∈ s, Polynomial.evalEval z (v.eval z) (Hf i) = 0 :=
    fun z hz => exists_vanishing_factor hQ (hvan z hz)
  set f : F → ι := fun z =>
    if h : ∃ i ∈ s, Polynomial.evalEval z (v.eval z) (Hf i) = 0
    then h.choose else hsne.choose with hf
  have hmaps : ∀ z ∈ goodSet, f z ∈ s := by
    intro z hz
    rw [hf]
    simp only [dif_pos (hex z hz)]
    exact (hex z hz).choose_spec.1
  obtain ⟨i, hi, hcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hsne hcount
  refine ⟨i, hi, le_trans hcard (Finset.card_le_card ?_)⟩
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have h1 := hz.2
  rw [hf] at h1
  simp only [dif_pos (hex z hz.1)] at h1
  exact h1 ▸ (hex z hz.1).choose_spec.2

/-! ## The branch roots with base-point values on the incidence set -/

section Roots

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The incidence-set branch root**, membership-dependent: at a place in the selected
factor's incidence set, the branch root of `H̃′` with value `lc_H(z) · v(z)`. -/
noncomputable def incidenceRoot {v : F[X]} {z : F}
    (hinc : Polynomial.evalEval z (v.eval z) H = 0) :
    rationalRoot (H_tilde' H) z :=
  RationalRootSupply.rationalRoot_of_evalEval (Fact.out) hinc

omit [Fact (Irreducible H)] in
/-- **The base-point fact on the incidence set (monic)**: the constructed root's value is the
surface value — the `hbase` field of `DecodedProximateRoot.mpFin_of_decoded`, by
construction, in membership-dependent form. -/
theorem incidenceRoot_val_monic (hlc : H.leadingCoeff = 1) {v : F[X]} {z : F}
    (hinc : Polynomial.evalEval z (v.eval z) H = 0) :
    (v.eval z : F) = (incidenceRoot (H := H) hinc).1 := by
  rw [incidenceRoot, RationalRootSupply.rationalRoot_of_evalEval_val]
  have h1 : H.coeff H.natDegree = 1 := hlc
  rw [h1, Polynomial.eval_one, one_mul]

end Roots

/-! ## The composed §6 supply -/

/-- **The §6 matching-geometry supply (membership-dependent form).**  From: the interpolant
factorization, the per-good-place GS list membership (`Q(z, v(z)) = 0`), and the count
`m · n ≤ |goodSet|` — a factor `Hᵢ`, its incidence set of size `≥ n`, and on it the branch
roots with base-point values (when `Hᵢ` is monic).  Exactly the `matchingSet`/`root`/`hbase`
inputs of the sound `mpFin` surface, with the cardinality LOWER bound the counting consumes
(the F8 gate is passed by interpolation-scale surfaces). -/
theorem matching_supply_of_factorization {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet, Polynomial.evalEval z (v.eval z) Q = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card) :
    ∃ i ∈ s, ∃ matchingSet : Finset F,
      matchingSet ⊆ goodSet ∧ n ≤ matchingSet.card ∧
      ∀ z ∈ matchingSet, Polynomial.evalEval z (v.eval z) (Hf i) = 0 := by
  obtain ⟨i, hi, hcard⟩ := exists_factor_incidence_large hQ hsne hvan hcount
  exact ⟨i, hi,
    goodSet.filter (fun z => Polynomial.evalEval z (v.eval z) (Hf i) = 0),
    Finset.filter_subset _ _, hcard,
    fun z hz => (Finset.mem_filter.mp hz).2⟩

end FactorPigeonhole

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FactorPigeonhole.exists_vanishing_factor
#print axioms ArkLib.FactorPigeonhole.exists_factor_incidence_large
#print axioms ArkLib.FactorPigeonhole.incidenceRoot
#print axioms ArkLib.FactorPigeonhole.incidenceRoot_val_monic
#print axioms ArkLib.FactorPigeonhole.matching_supply_of_factorization
