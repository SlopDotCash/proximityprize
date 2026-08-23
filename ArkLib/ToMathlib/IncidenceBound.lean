/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BranchSeparationUnsat
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

/-!
# Issue #304 — the incidence bound on base-point matching sets (the F8 satisfiability gate)

Continuation of the F7 self-audit, one level up.  After F7 the sound `mpFin` surface is the
root/`hbase`-input form (`DecodedProximateRoot.mpFin_of_decoded`): per matching place `z`, a
branch root `root z` of `H̃′(z, ·)` whose value equals the decoded surface's centre value,
`hbase : (w.eval (C x₀)).eval z = (root z).1`.  This file quantifies how many such places can
exist at all:

* `incidencePoly` — the incidence polynomial `inc := H̃′.eval v ∈ F[X]`
  (`v := w.eval (C x₀)`): its value at `z` is `H̃′(z, v(z))` (`incidencePoly_eval`).
* `incidencePoly_eval_eq_zero_of_hbase` — every place carrying a base-point root is a root of
  `inc`: the matching set of the root/`hbase`-input form lies inside `inc`'s root set.
* `incidencePoly_ne_zero_of_monic` — for monic `H` with `d_H ≥ 2`, `inc ≠ 0` (else
  `(T − C v) ∣ H̃′ = H`, forcing `d_H = 1` by the F7 degree argument).
* `card_le_of_hbase` — **the incidence bound**: any matching set with base-point roots has
  cardinality `≤ inc.natDegree` (monic, `d_H ≥ 2`).

**The F8 satisfiability gate (the honest consequence).**  The truncation capstones demand
`|matchingSet| > gradedCardBudget` (through the discriminant counting `hbig`), while the
incidence bound caps `|matchingSet| ≤ natDegree (H̃′.eval v)`.  `card_le_natDegree_eval`
bounds the latter by `degreeX H̃′ + d_{H̃′} · natDegree v`.  So the root/`hbase`-input
hypothesis set is jointly satisfiable **only when the decoded surface's place-line degree
`natDegree v` is large enough that the incidence curve carries the whole counting set**:

  `gradedCardBudget < degreeX H̃′ + d_H · natDegree v`.

This is a kernel-checked necessary condition (`natDegree_v_lower_bound_of_counting`), exposed
so instantiation work targets surfaces of the right degree — or, if the genuine §5 surface has
small place-line degree, so the `hbase`-shaped congruence gets the same fidelity treatment as
F1–F7 (the base-point pinning may need to live against a non-rational branch object rather
than the rational surface value).

## References
* [BCIKS20] §5, Appendix A.5.2/A.1 (Lemma A.1's counting against `S_β` and the matching
  congruence); the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace IncidenceBound

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The incidence polynomial -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The incidence polynomial's value at `z` is the branch equation at the surface value:
`(H̃′.eval v).eval z = H̃′(z, v(z))`. -/
theorem incidencePoly_eval (v : F[X]) (z : F) :
    (((H_tilde' H).eval v).eval z : F)
      = Polynomial.evalEval z (v.eval z) (H_tilde' H) :=
  (RationalRootSupply.evalEval_eval_eval z (H_tilde' H) v).symm

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Every base-point matching place is an incidence root**: if the branch root at `z` carries
the surface's centre value, then `z` roots the incidence polynomial. -/
theorem incidencePoly_eval_eq_zero_of_hbase {v : F[X]} {z : F}
    (root : rationalRoot (H_tilde' H) z) (hbase : v.eval z = root.1) :
    ((H_tilde' H).eval v).eval z = 0 := by
  rw [incidencePoly_eval, hbase]
  exact root.2

/-- **The incidence polynomial is nonzero (monic, `d_H ≥ 2`)**: its vanishing would make the
rational surface a branch of the irreducible `H`, forcing `d_H = 1`. -/
theorem incidencePoly_ne_zero_of_monic (hlc : H.leadingCoeff = 1)
    (hd2 : 2 ≤ H.natDegree) (v : F[X]) :
    (H_tilde' H).eval v ≠ 0 := by
  intro h0
  have hdvd : (Polynomial.X - Polynomial.C v) ∣ H_tilde' H :=
    Polynomial.dvd_iff_isRoot.mpr h0
  rw [BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic H hlc] at hdvd
  exact absurd (BranchSeparationUnsat.natDegree_eq_one_of_X_sub_C_dvd_irreducible hdvd)
    (by omega)

section Card

/-- **The incidence bound**: any matching set whose places carry base-point roots has
cardinality at most the incidence polynomial's degree (monic, `d_H ≥ 2`). -/
theorem card_le_of_hbase (hlc : H.leadingCoeff = 1) (hd2 : 2 ≤ H.natDegree)
    {v : F[X]} {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hbase : ∀ z ∈ matchingSet, v.eval z = (root z).1) :
    matchingSet.card ≤ ((H_tilde' H).eval v).natDegree := by
  refine Polynomial.card_le_degree_of_subset_roots (p := (H_tilde' H).eval v) ?_
  intro z hz
  rw [Polynomial.mem_roots (incidencePoly_ne_zero_of_monic hlc hd2 v)]
  exact incidencePoly_eval_eq_zero_of_hbase (root z)
    (hbase z (by simpa using hz))

end Card

/-! ## The degree accounting and the F8 gate -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Degree accounting for the incidence polynomial:
`natDegree (B.eval v) ≤ degreeX B + natDegree_Y B · natDegree v`. -/
theorem natDegree_eval_le (B : F[X][Y]) (v : F[X]) :
    (B.eval v).natDegree ≤ Polynomial.Bivariate.degreeX B + B.natDegree * v.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro i hi
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (B.coeff i).natDegree ≤ Polynomial.Bivariate.degreeX B :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX B i
  have h2 : (v ^ i).natDegree ≤ i * v.natDegree := by
    refine le_trans (Polynomial.natDegree_pow_le) (le_refl _)
  have hiB : i ≤ B.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have : i * v.natDegree ≤ B.natDegree * v.natDegree := Nat.mul_le_mul_right _ hiB
  omega

section Gate

variable [Fintype F] [DecidableEq F]

/-- **The F8 satisfiability gate (kernel-checked necessary condition).**  If a base-point
matching set additionally satisfies the discriminant-counting largeness
(`|F| − deg disc ≤ |matchingSet|` via a covering discriminant), then the decoded surface's
place-line degree is forced up: `|F| ≤ deg disc + degreeX H̃′ + d_{H̃′} · natDegree v`.
Contrapositive: in any regime where the right side is smaller than `|F|`, the root/`hbase`
hypothesis set of the truncation capstones is **jointly unsatisfiable**. -/
theorem natDegree_v_lower_bound_of_counting (hlc : H.leadingCoeff = 1)
    (hd2 : 2 ≤ H.natDegree)
    {v : F[X]} {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hbase : ∀ z ∈ matchingSet, v.eval z = (root z).1)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet) :
    Fintype.card F ≤ disc.natDegree
      + (Polynomial.Bivariate.degreeX (H_tilde' H)
          + (H_tilde' H).natDegree * v.natDegree) := by
  classical
  -- counting: the matching set covers the complement of disc's roots
  have hlarge : Fintype.card F - disc.natDegree ≤ matchingSet.card := by
    have hsub : Finset.univ \ disc.roots.toFinset ⊆ matchingSet := by
      intro z hz
      rw [Finset.mem_sdiff] at hz
      refine hcover z (fun h0 => hz.2 ?_)
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hdisc]
      exact h0
    have hcard := Finset.card_le_card hsub
    have hroots : disc.roots.toFinset.card ≤ disc.natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' disc)
    have hsdiff : (Finset.univ \ disc.roots.toFinset).card
        = Fintype.card F - disc.roots.toFinset.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  -- the incidence cap
  have hcap : matchingSet.card ≤ ((H_tilde' H).eval v).natDegree :=
    card_le_of_hbase hlc hd2 root hbase
  have hdeg := natDegree_eval_le (H_tilde' H) v
  omega

end Gate

end IncidenceBound

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.IncidenceBound.incidencePoly_eval
#print axioms ArkLib.IncidenceBound.incidencePoly_eval_eq_zero_of_hbase
#print axioms ArkLib.IncidenceBound.incidencePoly_ne_zero_of_monic
#print axioms ArkLib.IncidenceBound.card_le_of_hbase
#print axioms ArkLib.IncidenceBound.natDegree_eval_le
#print axioms ArkLib.IncidenceBound.natDegree_v_lower_bound_of_counting
