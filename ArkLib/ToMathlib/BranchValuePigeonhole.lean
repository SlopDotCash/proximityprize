/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FactorPigeonhole

/-!
# Issue #304 — the branch-value pigeonhole: the §6 assignment that EVADES F7/F8

`FactorPigeonhole` ran the §6 assignment on the rational surface's values `v(z)` — and the
F7/F8 findings show that route pins the incidence places onto a low-degree curve (or, with the
fleet's irreducibility finding, dies entirely on the graph interpolant).  The repair is
structural: the genuine [BCIKS20] §5.2.6 matching runs on the **per-place decoded branch
values** `y : F → F` — an *arbitrary function* (each `y z` produced by the per-`z` GS decoder
independently), not the evaluation of any global polynomial.  With a function-valued `y`:

* **F7 does not apply** — there is no global linear factor `(Y′ − C v)` to be prime;
* **F8 does not apply** — there is no incidence *polynomial*, so no degree cap on the
  matching set: `|matchingSet|` can genuinely reach `|goodSet| / m`.

Contents:

* `exists_vanishing_factor_fn` / `exists_factor_incidence_large_fn` — the per-place factor
  selection and the pigeonhole, now over an arbitrary value function `y : F → F` with the
  centre-specialization vanishing `(evalX (C x₀) R)(z, y z) = 0` (which the per-`z` GS list
  membership supplies);
* `incidenceRootFn` / `incidenceRootFn_val_monic` — on the selected factor's incidence set,
  the branch roots with values `y z` (monic: exactly `y z` — the `hbase` content against the
  per-place decoded value);
* `matching_supply_of_centre_vanishing` — **the capstone supply**: from the GS split
  `evalX (C x₀) R = ∏ᵢ Hᵢ` (the factorization of the centre specialization), the per-place
  centre vanishing, and the count `m · n ≤ |goodSet|` — a factor with an incidence set of
  size `≥ n` carrying branch roots and base-point values.  Exactly the
  `matchingSet`/`root`/`hbase` inputs of `DecodedProximateRoot.mpFin_of_decoded`, in
  membership-dependent form, with **no rational-surface hypothesis anywhere**.

The honest remaining input is the per-place centre vanishing
`(evalX (C x₀) R)(z, y z) = 0` for the decoded branch values — the per-`z` GS list membership
read at the centre, the genuine §5 decoder output shape.

## References
* [BCIKS20] §5.2.6/§6 (the per-parameter list and the branch assignment); the F-series ledger
  on issue #304 (F7/F8: why the rational-surface form of this supply is impossible).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace BranchValuePigeonhole

variable {F : Type} [Field F]

/-! ## Per-place factor selection over a value function -/

/-- **Per-place factor selection (function-valued).**  If the centre specialization vanishes
at the decoded branch value, some factor of it does. -/
theorem exists_vanishing_factor_fn {ι : Type*} {s : Finset ι} {Hf : ι → F[X][Y]}
    {Q : F[X][Y]} (hQ : Q = ∏ i ∈ s, Hf i) {y z : F}
    (hvan : Polynomial.evalEval z y Q = 0) :
    ∃ i ∈ s, Polynomial.evalEval z y (Hf i) = 0 := by
  have h2 : (Polynomial.evalEvalRingHom z y) Q = 0 := hvan
  rw [hQ, map_prod] at h2
  exact Finset.prod_eq_zero_iff.mp h2

/-- **The branch-value pigeonhole.**  Over an arbitrary per-place value function `y : F → F`:
if the factored polynomial vanishes at `(z, y z)` for every good place, some factor's
incidence set carries at least `n` places whenever `m · n ≤ |goodSet|`.  No incidence-degree
cap applies — `y` is not a polynomial evaluation. -/
theorem exists_factor_incidence_large_fn {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {y : F → F} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet, Polynomial.evalEval z (y z) Q = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card) :
    ∃ i ∈ s, n ≤
      (goodSet.filter (fun z => Polynomial.evalEval z (y z) (Hf i) = 0)).card := by
  classical
  have hex : ∀ z ∈ goodSet, ∃ i ∈ s, Polynomial.evalEval z (y z) (Hf i) = 0 :=
    fun z hz => exists_vanishing_factor_fn hQ (hvan z hz)
  set f : F → ι := fun z =>
    if h : ∃ i ∈ s, Polynomial.evalEval z (y z) (Hf i) = 0
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

/-! ## Branch roots at the decoded values -/

section Roots

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The branch root at a decoded value** (membership-dependent). -/
noncomputable def incidenceRootFn {y z : F}
    (hinc : Polynomial.evalEval z y H = 0) :
    rationalRoot (H_tilde' H) z :=
  RationalRootSupply.rationalRoot_of_evalEval (Fact.out) hinc

omit [Fact (Irreducible H)] in
/-- **The base-point fact at the decoded value (monic)**: the constructed root's value is the
decoded branch value itself. -/
theorem incidenceRootFn_val_monic (hlc : H.leadingCoeff = 1) {y z : F}
    (hinc : Polynomial.evalEval z y H = 0) :
    (y : F) = (incidenceRootFn (H := H) hinc).1 := by
  rw [incidenceRootFn, RationalRootSupply.rationalRoot_of_evalEval_val]
  have h1 : H.coeff H.natDegree = 1 := hlc
  rw [h1, Polynomial.eval_one, one_mul]

end Roots

/-! ## The composed §6 supply at the centre specialization -/

/-- **The §6 matching supply from the centre specialization (F7/F8-evading form).**
From: the factorization of the centre specialization `evalX (C x₀) R = ∏ᵢ Hᵢ`, the per-place
centre vanishing at the decoded branch values (`(evalX (C x₀) R)(z, y z) = 0` — the per-`z`
GS list membership read at the centre), and the count `m · n ≤ |goodSet|` — a factor with an
incidence set of size `≥ n` whose places all carry the per-place vanishing.  Combined with
`incidenceRootFn[_val_monic]`, exactly the `matchingSet`/`root`/`hbase` inputs of the sound
`mpFin` surface — with no rational-surface hypothesis, no incidence-degree cap. -/
theorem matching_supply_of_centre_vanishing {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {x₀ : F} {R : F[X][X][Y]}
    {s : Finset ι} {Hf : ι → F[X][Y]}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {y : F → F} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet,
      Polynomial.evalEval z (y z) (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card) :
    ∃ i ∈ s, ∃ matchingSet : Finset F,
      matchingSet ⊆ goodSet ∧ n ≤ matchingSet.card ∧
      ∀ z ∈ matchingSet, Polynomial.evalEval z (y z) (Hf i) = 0 := by
  obtain ⟨i, hi, hcard⟩ := exists_factor_incidence_large_fn hQ hsne hvan hcount
  exact ⟨i, hi,
    goodSet.filter (fun z => Polynomial.evalEval z (y z) (Hf i) = 0),
    Finset.filter_subset _ _, hcard,
    fun z hz => (Finset.mem_filter.mp hz).2⟩

end BranchValuePigeonhole

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BranchValuePigeonhole.exists_vanishing_factor_fn
#print axioms ArkLib.BranchValuePigeonhole.exists_factor_incidence_large_fn
#print axioms ArkLib.BranchValuePigeonhole.incidenceRootFn
#print axioms ArkLib.BranchValuePigeonhole.incidenceRootFn_val_monic
#print axioms ArkLib.BranchValuePigeonhole.matching_supply_of_centre_vanishing
