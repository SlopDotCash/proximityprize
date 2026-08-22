/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.Trivariate
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami
import ArkLib.Data.CodingTheory.ProximityGap.GSFactorExtract
import ArkLib.ToMathlib.BivariateDegreeToolkit

/-!
# GAP-NZ: the `Z`-specialization of the GS interpolant is nonzero for all but few parameters

The BCIKS20 §5 trivariate Guruswami–Sudan list-decoding keystone
(`GSMultiplicityCore.Q_vanishes_on_close_codeword_graph_of_radius` and friends) takes the
non-degeneracy `hQz_ne : Trivariate.eval_on_Z Q z ≠ 0` as an *explicit hypothesis*: a nonzero
trivariate `Q : F[Z][X][Y]` need not stay nonzero after substituting `Z = z`, and the whole
multiplicity/root-counting argument only runs at parameters `z` where it does.

This file discharges that obligation. A `Z`-specialization `eval_on_Z Q z` vanishes iff *every*
inner-`Z` coefficient `((Q.coeff j).coeff i) ∈ F[Z]` vanishes at `z`.  Picking one nonzero such
coefficient `c` (which exists since `Q ≠ 0`), the bad-parameter set is contained in the roots of
`c`, whose number is at most `c.natDegree ≤ d` whenever `ZdegLE Q d` (every inner coefficient has
`Z`-degree `≤ d`).  Since the constructed GS interpolant satisfies `ZdegLE Q (gsZCap n m k)`
(`ZdegLE_triCoeffsToPoly`), this bounds the bad set by a `poly(n)`-sized quantity, so for any
parameter set larger than that, a good `z` exists.

## Main results

* `card_badZ_le` — `#{z : eval_on_Z Q z = 0} ≤ d`, given `Q ≠ 0` and `ZdegLE Q d`.
* `exists_eval_on_Z_ne_zero` — if `d < |F|`, some `z` has `eval_on_Z Q z ≠ 0`.
* `exists_goodZ_in` — on any `S` with `d < |S|`, some `z ∈ S` has `eval_on_Z Q z ≠ 0`.

These are the generic discharge of `hQz_ne`; the BCIKS20 §5 keystone consumes them directly.
-/

set_option linter.style.longLine false


open Polynomial Trivariate Finset
open scoped Polynomial

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The double-coefficient of a `Z`-specialization is the inner-`Z` coefficient evaluated at `z`. -/
theorem eval_on_Z_coeff_coeff (Q : F[Z][X][Y]) (z : F) (j i : ℕ) :
    ((eval_on_Z Q z).coeff j).coeff i = ((Q.coeff j).coeff i).eval z := by
  rw [eval_on_Z_eq, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom]

/-- **GAP-NZ: the bad-parameter set is small.** For a nonzero trivariate `Q` whose inner-`Z`
coefficients all have degree `≤ d` (`ZdegLE Q d`), the set of parameters `z` at which the
`Z`-specialization `eval_on_Z Q z` vanishes has cardinality `≤ d`.

A `Z`-specialization vanishes iff *every* inner coefficient `((Q.coeff j).coeff i) ∈ F[Z]` vanishes
at `z`; picking one nonzero such coefficient `c` (exists since `Q ≠ 0`), the bad set is contained in
the roots of `c`, which number `≤ c.natDegree ≤ d`. -/
theorem card_badZ_le {Q : F[Z][X][Y]} {d : ℕ} (hQ : Q ≠ 0) (hZ : ZdegLE Q d) :
    (univ.filter (fun z : F => eval_on_Z Q z = 0)).card ≤ d := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, Q.coeff j ≠ 0 := by
    by_contra h; push Not at h
    exact hQ (Polynomial.ext h)
  obtain ⟨i, hi⟩ : ∃ i, (Q.coeff j).coeff i ≠ 0 := by
    by_contra h; push Not at h
    exact hj (Polynomial.ext h)
  set c : F[X] := (Q.coeff j).coeff i with hc
  have hcdeg : c.natDegree ≤ d := hZ i j
  have hsub : (univ.filter (fun z : F => eval_on_Z Q z = 0))
      ⊆ univ.filter (fun z : F => c.eval z = 0) := by
    intro z hz
    rw [mem_filter] at hz ⊢
    refine ⟨mem_univ _, ?_⟩
    have := eval_on_Z_coeff_coeff Q z j i
    rw [hz.2] at this
    simp only [Polynomial.coeff_zero] at this
    rw [hc]; exact this.symm
  calc (univ.filter (fun z : F => eval_on_Z Q z = 0)).card
      ≤ (univ.filter (fun z : F => c.eval z = 0)).card := card_le_card hsub
    _ ≤ c.roots.toFinset.card := by
        refine card_le_card (fun z hz => ?_)
        rw [mem_filter] at hz
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hi, Polynomial.IsRoot.def]
        exact hz.2
    _ ≤ Multiset.card c.roots := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := c.card_roots'
    _ ≤ d := hcdeg

/-- For all but `≤ d` parameters, the `Z`-specialization is nonzero; so if `d < |F|`, a good `z`
exists.  This is the existence form of the `hQz_ne` discharge. -/
theorem exists_eval_on_Z_ne_zero {Q : F[Z][X][Y]} {d : ℕ} (hQ : Q ≠ 0) (hZ : ZdegLE Q d)
    (hd : d < Fintype.card F) : ∃ z : F, eval_on_Z Q z ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hall : (univ.filter (fun z : F => eval_on_Z Q z = 0)) = univ := by
    rw [Finset.filter_true_of_mem (fun z _ => h z)]
  have := card_badZ_le hQ hZ
  rw [hall, Finset.card_univ] at this
  omega

/-- **Avoiding form (matches the c56 bad-set template).** On any parameter set `S` with `d < |S|`,
some `z ∈ S` has `eval_on_Z Q z ≠ 0`. -/
theorem exists_goodZ_in {Q : F[Z][X][Y]} {d : ℕ} (hQ : Q ≠ 0) (hZ : ZdegLE Q d)
    (S : Finset F) (hS : d < S.card) : ∃ z ∈ S, eval_on_Z Q z ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hsub : S ⊆ univ.filter (fun z : F => eval_on_Z Q z = 0) := by
    intro z hz; rw [mem_filter]; exact ⟨mem_univ _, h z hz⟩
  have := le_trans (Finset.card_le_card hsub) (card_badZ_le hQ hZ)
  omega

/-- **Per-parameter list-size bound (PATH 2 #2).** At a *good* parameter `z` (`eval_on_Z Q z ≠ 0`,
ensured for all but `≤ d` parameters by `card_badZ_le`), any family `Ps` of candidate message
polynomials whose linear factors `(Y - C p)` divide the `Z`-specialization `eval_on_Z Q z` numbers at
most `D_Y Q` (the trivariate `Y`-degree).  This is the Guruswami–Sudan list-size bound
(`GSFactorExtract.gs_list_size_le`) transported through `natDegreeY_eval_on_Z_le`: at a good `z` the
close codewords are distinct `Y`-roots of `eval_on_Z Q z`, hence number `≤ natDegreeY (eval_on_Z Q z)
≤ D_Y Q ≤ gsDpg/k = poly(n)`.

Each close codeword's linear factor is supplied by the BCIKS20 §5 keystone
`GSMultiplicityCore.Q_graph_factor_dvd_of_radius` (`(Y - C Pz) ∣ eval_on_Z Q z`), whose `hQz_ne`
hypothesis is discharged here by `exists_eval_on_Z_ne_zero`. -/
theorem perZ_listSize_le {Q : F[Z][X][Y]} {z : F} (hQz : eval_on_Z Q z ≠ 0)
    (Ps : Finset (Polynomial F))
    (hdvd : ∀ p ∈ Ps, (Polynomial.X - Polynomial.C p) ∣ eval_on_Z Q z) :
    Ps.card ≤ Trivariate.D_Y Q := by
  refine le_trans (GSFactorExtract.gs_list_size_le (eval_on_Z Q z) hQz Ps hdvd) ?_
  exact ArkLib.BivariateDegreeToolkit.natDegreeY_eval_on_Z_le Q z

end ProximityGap
