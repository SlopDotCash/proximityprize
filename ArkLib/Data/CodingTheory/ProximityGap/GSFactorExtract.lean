/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic.Ring
import ArkLib.Data.CodingTheory.ProximityGap.BivariateVanishing

/-! # Guruswami–Sudan factor extraction (Track A3)

This file proves the two algebraic cores of the Guruswami–Sudan factor-extraction
step of list decoding, both fully `Mathlib`-backed.

## Setting

Work in the bivariate ring `F[X][Y] = (F[X])[X]` (`Polynomial (Polynomial F)`).  A
candidate message is a `p : F[X]` of degree `< k`; the corresponding *factor* is the
monic-linear-in-`Y` polynomial `Y - C p`, where `C : F[X] → F[X][Y]` is the constant
embedding.  Evaluating `Q : F[X][Y]` at `Y := p` (via `Polynomial.eval`, whose value
ring is the base `F[X]`) gives the "restriction along the curve" `Q(X, p(X)) : F[X]`.

## Part 1 — Multiplicity-sum factor extraction

`A1` supplies, at each agreement point `a ∈ S`, an `m`-fold root of the restriction
`g := Q(X, p(X))` (`(X - C a) ^ m ∣ g`).  The pigeonhole core says: if these
multiplicities sum to more than `g.natDegree`, then `g = 0`.  Combined with
`Polynomial.dvd_iff_isRoot` for the monic linear `Y - C p`, this yields the
divisibility `(Y - C p) ∣ Q` in `F[X][Y]`.

Stated abstractly first over an arbitrary domain (`multiplicity_sum_le_natDegree`,
`eq_zero_of_natDegree_lt_multiplicity_sum`), then specialized to the curve
restriction (`curve_factor_extraction`).

## Part 2 — List-size bound

Distinct degree-`< k` messages `p` whose factor `Y - C p` divides `Q` are bounded in
number by the `Y`-degree `Q.natDegree`: each such `p` is a root of `Q` in the
outer variable `Y` (`Polynomial.dvd_iff_isRoot`), and the distinct roots of a
nonzero polynomial number at most its `natDegree`
(`Polynomial.card_le_degree_of_subset_roots`).

No `sorry`, `admit`, or `native_decide`; every theorem is checked to depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

namespace GSFactorExtract

noncomputable section

open Polynomial Finset

/-! ## Part 1: multiplicity-sum bound and factor extraction -/

section MultiplicitySum

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Multiplicity-sum bound.** If `g ≠ 0` and at each point `a` of a finite set
`S` the polynomial `g` has an `m a`-fold root (witnessed by `(X - C a) ^ (m a) ∣ g`),
then the total multiplicity `∑_{a ∈ S} m a` is at most `g.natDegree`.

This is the counting heart of Guruswami–Sudan: the `m`-fold agreement contributions
collected by the substitution lemma `A1` cannot exceed the degree budget. -/
theorem multiplicity_sum_le_natDegree
    {g : R[X]} (hg : g ≠ 0) {S : Finset R} {m : R → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ g) :
    ∑ a ∈ S, m a ≤ g.natDegree := by
  classical
  -- assemble the multiset of roots-with-multiplicity drawn from `S`
  set s : Multiset R := S.val.bind (fun a => Multiset.replicate (m a) a) with hs
  -- its total cardinality is exactly the multiplicity sum
  have hcard : Multiset.card s = ∑ a ∈ S, m a := by
    rw [hs, Multiset.card_bind]
    simp only [Function.comp, Multiset.card_replicate]
    rfl
  -- `s ≤ g.roots`: each point's count `m a` is ≤ its root multiplicity in `g`
  have hle : s ≤ g.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases haS : a ∈ S
    · have hcount : Multiset.count a s = m a := by
        rw [hs, Multiset.count_bind]
        have hmap : (S.val.map fun b => Multiset.count a (Multiset.replicate (m b) b))
            = S.val.map fun b => if b = a then m b else 0 := by
          apply Multiset.map_congr rfl
          intro b _
          rw [Multiset.count_replicate]
        rw [hmap]
        change ∑ b ∈ S, (if b = a then m b else 0) = m a
        rw [Finset.sum_ite_eq' S a (fun b => m b)]
        simp [haS]
      rw [hcount, Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hg).mpr (hroot a haS)
    · have hcount : Multiset.count a s = 0 := by
        rw [hs, Multiset.count_bind]
        have hmap : (S.val.map fun b => Multiset.count a (Multiset.replicate (m b) b))
            = S.val.map fun b => if b = a then m b else 0 := by
          apply Multiset.map_congr rfl
          intro b _
          rw [Multiset.count_replicate]
        rw [hmap]
        change ∑ b ∈ S, (if b = a then m b else 0) = 0
        rw [Finset.sum_ite_eq' S a (fun b => m b)]
        simp [haS]
      rw [hcount]
      exact Nat.zero_le _
  calc ∑ a ∈ S, m a = Multiset.card s := hcard.symm
    _ ≤ Multiset.card g.roots := Multiset.card_le_card hle
    _ ≤ g.natDegree := Polynomial.card_roots' g

/-- **Factor extraction (vanishing form).** If the collected agreement multiplicities
`∑_{a ∈ S} m a` strictly exceed the degree budget `g.natDegree`, then `g = 0`. -/
theorem eq_zero_of_natDegree_lt_multiplicity_sum
    {g : R[X]} {S : Finset R} {m : R → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ g)
    (hbudget : g.natDegree < ∑ a ∈ S, m a) :
    g = 0 := by
  by_contra hg
  exact absurd (multiplicity_sum_le_natDegree hg hroot) (not_le.mpr hbudget)

end MultiplicitySum

/-! ## The curve restriction `Q(X, p(X))` and `(Y - C p) ∣ Q`

In `F[X][Y] = (F[X])[X]`, the base ring is `F[X]` and the outer variable is `Y`.
Evaluating `Q : (F[X])[X]` via `Polynomial.eval` takes a value in the base `F[X]`;
evaluating at `p : F[X]` is exactly the restriction `Q(X, p(X))`.  The constant
embedding `C : F[X] → (F[X])[X]` builds the linear factor `Y - C p`. -/

section CurveRestriction

variable {F : Type*} [CommRing F]

/-- The restriction of `Q : F[X][Y]` to the curve `Y = p(X)`, i.e. `Q(X, p(X))`,
obtained by evaluating the outer variable `Y` at `p : F[X]`. -/
def curveRestrict (Q : (F[X])[X]) (p : F[X]) : F[X] := Q.eval p

theorem curveRestrict_def (Q : (F[X])[X]) (p : F[X]) :
    curveRestrict Q p = Q.eval p := rfl

/-- `Y - C p` is monic (leading coefficient `1`), since it is `X - C c` in the outer
ring `F[X][Y]` with `c := p`. -/
theorem monic_Y_sub_Cp (p : F[X]) : (X - C p : (F[X])[X]).Monic := monic_X_sub_C p

/-- **`(Y - C p) ∣ Q` iff the curve restriction vanishes.** In `F[X][Y]`, the monic
linear factor `Y - C p` divides `Q` exactly when `Q(X, p(X)) = 0`. This is
`Polynomial.dvd_iff_isRoot` applied in the ring `F[X][Y]` (whose base ring is
`F[X]`), with `IsRoot` unfolding to evaluation at `p`. -/
theorem Y_sub_Cp_dvd_iff_curveRestrict_eq_zero (Q : (F[X])[X]) (p : F[X]) :
    (X - C p) ∣ Q ↔ curveRestrict Q p = 0 := by
  rw [curveRestrict_def, Polynomial.dvd_iff_isRoot]
  rfl

end CurveRestriction

/-! ### Assembled curve-factor extraction over a field

Specialize to a field `F`: then `F[X]` is a domain, so the multiplicity-sum bound
applies to the curve restriction. We assume `A1` has supplied, at each agreement
point, an `m`-fold root of `g = Q(X, p(X))` *as a polynomial in `F[X]`*, witnessed by
divisibility by a power of `X - C a` (`a ∈ F`). When the multiplicities overrun the
degree budget, `Q(X, p(X)) = 0`, hence `(Y - C p) ∣ Q`. -/
section FieldAssembly

variable {F : Type*} [Field F]

/-- **Guruswami–Sudan curve factor extraction.** Let `Q : F[X][Y]` and `p : F[X]`,
with restriction `g := Q(X, p(X))`. Suppose `A1` yields, for each agreement point
`a ∈ S ⊆ F`, an `m a`-fold root `(X - C a) ^ (m a) ∣ g`, and the collected
multiplicities exceed the `X`-degree budget `B := g.natDegree`. Then the factor
`Y - C p` divides `Q` in `F[X][Y]`. -/
theorem curve_factor_extraction
    (Q : (F[X])[X]) (p : F[X]) {S : Finset F} {m : F → ℕ}
    (hroot : ∀ a ∈ S, (X - C a) ^ (m a) ∣ curveRestrict Q p)
    (hbudget : (curveRestrict Q p).natDegree < ∑ a ∈ S, m a) :
    (X - C p) ∣ Q := by
  rw [Y_sub_Cp_dvd_iff_curveRestrict_eq_zero]
  exact eq_zero_of_natDegree_lt_multiplicity_sum hroot hbudget

/-- **Factor extraction from root multiplicities.**  This is the usual GS-facing
form: each agreement point contributes multiplicity `m a` to the univariate
restriction `Q(X, p(X))`. -/
theorem curve_factor_extraction_of_rootMultiplicity
    (Q : (F[X])[X]) (p : F[X]) {S : Finset F} {m : F → ℕ}
    (hroot : ∀ a ∈ S, m a ≤ (curveRestrict Q p).rootMultiplicity a)
    (hbudget : (curveRestrict Q p).natDegree < ∑ a ∈ S, m a) :
    (X - C p) ∣ Q := by
  refine curve_factor_extraction Q p ?_ hbudget
  intro a ha
  by_cases hzero : curveRestrict Q p = 0
  · rw [hzero]
    exact dvd_zero _
  · exact (Polynomial.le_rootMultiplicity_iff hzero).mp (hroot a ha)

/-- **Factor extraction from bivariate order-vanishing.**  If `Q` vanishes to order
`m a` at every curve point `(a, p(a))`, then the substitution lemma supplies the
univariate divisibility witnesses consumed by `curve_factor_extraction`. -/
theorem curve_factor_extraction_of_vanishesToOrder
    (Q : (F[X])[X]) (p : F[X]) {S : Finset F} {m : F → ℕ}
    (hvan : ∀ a ∈ S, ArkLib.GS.vanishesToOrder (m a) Q a (p.eval a))
    (hbudget : (curveRestrict Q p).natDegree < ∑ a ∈ S, m a) :
    (X - C p) ∣ Q := by
  refine curve_factor_extraction Q p ?_ hbudget
  intro a ha
  simpa [curveRestrict] using
    (ArkLib.GS.vanishesToOrder.dvd_eval (hvan a ha) p rfl)

end FieldAssembly

/-! ## Part 2: list-size bound

The number of *distinct* messages `p` (here, members of a finite candidate set
`Ps : Finset F[X]`, e.g. the degree-`< k` polynomials) whose factor `Y - C p`
divides `Q ≠ 0` is at most `Q.natDegree`, the `Y`-degree of `Q`.

Geometric idea: distinct `p` are pairwise-distinct roots (in the outer variable `Y`)
of `Q`, since `Y - C p ∣ Q ↔ Q.eval p = 0`; the distinct roots of a nonzero
polynomial over a domain number at most its `natDegree`. We realize this in the outer
polynomial ring `(F[X])[X]`, which is a domain. -/

section ListSize

variable {F : Type*} [Field F]

/-- The candidate messages `p ∈ Ps` whose factor divides `Q` are distinct roots of
`Q : F[X][Y]` (in the variable `Y`), hence number at most `Q.natDegree`. -/
theorem card_distinct_linear_factors_le_natDegree
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (hdvd : ∀ p ∈ Ps, (X - C p) ∣ Q) :
    Ps.card ≤ Q.natDegree := by
  classical
  -- every `p ∈ Ps` is a root of `Q` (in the outer variable)
  have hsub : Ps.val ⊆ Q.roots := by
    intro p hp
    rw [← Finset.mem_def] at hp
    rw [Polynomial.mem_roots hQ]
    simpa [Polynomial.IsRoot.def] using (Polynomial.dvd_iff_isRoot).mp (hdvd p hp)
  -- distinct roots of a nonzero polynomial number ≤ its `natDegree`
  exact Polynomial.card_le_degree_of_subset_roots hsub

/-- **Guruswami–Sudan list-size bound.** With `Q : F[X][Y]` nonzero, the set of
candidate messages `p` (members of a finite candidate family `Ps`, e.g. all degree
`< k` polynomials) whose factor `Y - C p` divides `Q` has cardinality at most the
`Y`-degree `Q.natDegree`. This bounds the Guruswami–Sudan output list. -/
theorem gs_list_size_le
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (hdvd : ∀ p ∈ Ps, (X - C p) ∣ Q) :
    Ps.card ≤ Q.natDegree :=
  card_distinct_linear_factors_le_natDegree Q hQ Ps hdvd

end ListSize

/-! ## End-to-end statement

Combining Parts 1 and 2: from `A1`'s per-point multiplicity witnesses, every
candidate message whose curve restriction is killed by an overrun budget yields a
linear factor of `Q`, and the number of such distinct messages is bounded by the
`Y`-degree. This is the full Guruswami–Sudan factor-extraction + list-size pipeline. -/

section EndToEnd

variable {F : Type*} [Field F]

/-- **GS factor extraction ⟹ list-size bound, assembled.** Given nonzero `Q` and a
finite candidate family `Ps` of messages such that *each* candidate `p ∈ Ps` carries,
from `A1`, agreement multiplicities (over a per-`p` agreement set `S p` with
multiplicity `m p`) exceeding the degree budget of its curve restriction, the family
size is bounded by the `Y`-degree `Q.natDegree`. -/
theorem gs_factor_extraction_list_size
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (S : F[X] → Finset F) (m : F[X] → F → ℕ)
    (hroot : ∀ p ∈ Ps, ∀ a ∈ S p, (X - C a) ^ (m p a) ∣ curveRestrict Q p)
    (hbudget : ∀ p ∈ Ps, (curveRestrict Q p).natDegree < ∑ a ∈ S p, m p a) :
    Ps.card ≤ Q.natDegree := by
  apply gs_list_size_le Q hQ Ps
  intro p hp
  exact curve_factor_extraction Q p (hroot p hp) (hbudget p hp)

/-- End-to-end list-size bound in the root-multiplicity form normally produced
by multiplicity transfer from interpolation constraints. -/
theorem gs_factor_extraction_list_size_of_rootMultiplicity
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (S : F[X] → Finset F) (m : F[X] → F → ℕ)
    (hroot : ∀ p ∈ Ps, ∀ a ∈ S p, m p a ≤ (curveRestrict Q p).rootMultiplicity a)
    (hbudget : ∀ p ∈ Ps, (curveRestrict Q p).natDegree < ∑ a ∈ S p, m p a) :
    Ps.card ≤ Q.natDegree := by
  apply gs_list_size_le Q hQ Ps
  intro p hp
  exact curve_factor_extraction_of_rootMultiplicity Q p (hroot p hp) (hbudget p hp)

/-- End-to-end list-size bound directly from bivariate order-vanishing along each
candidate curve `Y = p(X)`. -/
theorem gs_factor_extraction_list_size_of_vanishesToOrder
    (Q : (F[X])[X]) (hQ : Q ≠ 0) (Ps : Finset F[X])
    (S : F[X] → Finset F) (m : F[X] → F → ℕ)
    (hvan : ∀ p ∈ Ps, ∀ a ∈ S p,
      ArkLib.GS.vanishesToOrder (m p a) Q a (p.eval a))
    (hbudget : ∀ p ∈ Ps, (curveRestrict Q p).natDegree < ∑ a ∈ S p, m p a) :
    Ps.card ≤ Q.natDegree := by
  apply gs_list_size_le Q hQ Ps
  intro p hp
  exact curve_factor_extraction_of_vanishesToOrder Q p (hvan p hp) (hbudget p hp)

end EndToEnd

end

end GSFactorExtract
