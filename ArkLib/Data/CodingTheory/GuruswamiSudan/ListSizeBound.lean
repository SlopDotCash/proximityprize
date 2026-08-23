/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/
import ArkLib.Data.CodingTheory.ProximityGap.GSFactorExtract
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import Mathlib.Tactic.Positivity

/-! # The Guruswami–Sudan list-size theorem (the composition)

This file composes the three in-tree algebraic pillars of Guruswami–Sudan list
decoding into the headline **list-size bound** `#candidates ≤ D / (k-1)`, and then
instantiates the explicit Johnson-regime *parameter window* `D := m·a − 1`.

## The three pillars

* **A2 — interpolation/existence.**
  `GSMultInterp.exists_ne_zero_vanishesToOrder`: whenever the *dimension condition*
  `n · (m·(m+1)/2) < #monomials(D, k)` holds, there is a nonzero bivariate
  interpolant of `(1, k)`-weighted degree `< D` vanishing to order `m` at all `n`
  interpolation points.  We consume this only at the level of its arithmetic
  feasibility predicate (`GSMultInterp.monoIdx`), since the existence theorem lives
  in coefficient-vector form while the factor-extraction pillar lives on the
  `F[X][Y]` surface; the bivariate interpolant `Q` is therefore taken as an explicit
  hypothesis carrying the same data (nonzero, order-`m` vanishing, weighted-degree
  bound).

* **A1 — substitution / multiplicity transfer + the agreement condition `m·a > D`.**
  `ArkLib.GS.vanishesToOrder.dvd_eval` (re-exported through
  `GSFactorExtract.curve_factor_extraction_of_vanishesToOrder`): if `Q` vanishes to
  order `m` at every curve point `(xᵢ, p(xᵢ))` for `i` in an *agreement* set `S` and
  the collected multiplicities `m·|S|` exceed the `X`-degree budget of the curve
  restriction `Q(X, p(X))`, then the linear factor `Y − C p` divides `Q`.  The
  degree budget is supplied by `GuruswamiSudan.degree_eval_le_weightedDegree`
  (`deg Q(X,p) ≤ natWeightedDegree Q 1 (k-1) ≤ D`); combined with the agreement
  condition `m·a > D` (and `a ≤ |S|`) this discharges the multiplicity overrun.

* **A3 — the `Y`-degree bound.**
  `GSFactorExtract.gs_list_size_le`: distinct candidate messages `p` whose factors
  `Y − C p` divide `Q ≠ 0` number at most `Q.natDegree`; and
  `GuruswamiSudan.natDegree_le_of_natWeightedDegree` turns the weighted-degree
  bound into the `Y`-degree bound `Q.natDegree ≤ D / (k-1)`.

## Main results

* `gs_dvd_of_agreement` — the agreement-condition factor extraction (A1 + A2-degree).
* `gs_list_size_bound` — the composed list-size theorem: `#candidates ≤ Q.natDegree`.
* `gs_list_size_bound_div` — the `D / (k-1)` form (A3 degree budget folded in).
* `gs_list_size_window` — the explicit parameter window `D := m·a − 1`, with
  `m·a > D` automatic and the dimension condition reduced to the purely arithmetic
  inequality `n · (m·(m+1)/2) < #monomials(m·a − 1, k)`.

Every theorem is kernel-checked to depend only on
`[propext, Classical.choice, Quot.sound]` (verified in-file via `#print axioms`).
-/

namespace GSListSizeBound

open Polynomial Finset

noncomputable section

variable {F : Type} [Field F]

/-! ## Pillar A1 + A2 (degree budget): the agreement-condition factor extraction

If a degree-`< k` candidate `p` agrees with the interpolation data on an agreement
set `S` (so `Q` vanishes to order `m` at each curve point `(xᵢ, p(xᵢ))`, `i ∈ S`),
and the **agreement condition** `m · |S| > D` holds for the `(1, k-1)`-weighted
degree bound `D` of `Q`, then the linear factor `Y − C p` divides `Q`.

The degree budget `deg Q(X, p(X)) ≤ D` comes from
`GuruswamiSudan.degree_eval_le_weightedDegree` (valid since `deg p ≤ k − 1`), and the
multiplicity overrun `m · |S| > deg Q(X, p(X))` then follows from the agreement
condition.  Factor extraction is `curve_factor_extraction_of_vanishesToOrder`. -/
theorem gs_dvd_of_agreement
    {ι : Type*} (Q : (F[X])[X]) (p : F[X]) {k D m : ℕ}
    (xs : ι → F) (S : Finset ι)
    (hpdeg : p.natDegree ≤ k - 1)
    (hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ D)
    (hvan : ∀ i ∈ S, ArkLib.GS.vanishesToOrder m Q (xs i) (p.eval (xs i)))
    (hxinj : ∀ i ∈ S, ∀ j ∈ S, xs i = xs j → i = j)
    (hagree : D < m * S.card) :
    (X - C p) ∣ Q := by
  classical
  -- Reindex the agreement set by its evaluation points (injective on `S`).
  set T : Finset F := S.image xs with hT
  have hTcard : T.card = S.card := by
    rw [hT, Finset.card_image_of_injOn]
    intro i hi j hj hij
    exact hxinj i hi j hj hij
  -- Per-point multiplicity function on the reindexed set.
  -- Each `a ∈ T` is `xs i` for some `i ∈ S`; assign multiplicity `m`.
  -- Vanishing of order `m` at `(a, p(a))` gives the `m`-fold root of the curve restriction.
  have hroot : ∀ a ∈ T, ArkLib.GS.vanishesToOrder m Q a (p.eval a) := by
    intro a ha
    rw [hT, Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hvan i hi
  -- Curve-restriction degree budget: `deg Q(X, p(X)) ≤ D`.
  have hbudgetD : (GSFactorExtract.curveRestrict Q p).natDegree ≤ D := by
    rw [GSFactorExtract.curveRestrict_def]
    exact le_trans (GuruswamiSudan.degree_eval_le_weightedDegree Q p k hpdeg) hwd
  -- Multiplicity overrun: `∑_{a ∈ T} m = m·|T| = m·|S| > D ≥ deg Q(X,p)`.
  have hsum : ∑ _a ∈ T, m = m * S.card := by
    rw [Finset.sum_const, hTcard, smul_eq_mul, Nat.mul_comm]
  have hbudget : (GSFactorExtract.curveRestrict Q p).natDegree < ∑ _a ∈ T, m := by
    rw [hsum]; omega
  -- Factor extraction from order-vanishing.
  exact GSFactorExtract.curve_factor_extraction_of_vanishesToOrder Q p
    (S := T) (m := fun _ => m) hroot hbudget

/-! ## The composed list-size theorem (A1 + A2-degree + A3 cardinality)

Now quantify over a finite family `Ps` of distinct candidate messages, each of which
satisfies the agreement-condition hypotheses of `gs_dvd_of_agreement` for its own
agreement set.  Pillar A3 (`gs_list_size_le`: distinct linear factors of `Q ≠ 0`
number `≤ Q.natDegree`) then caps the family. -/

/-- **Guruswami–Sudan list-size bound.** Let `Q : F[X][Y]` be a nonzero interpolant
of `(1, k-1)`-weighted degree `≤ D`.  For every candidate `p` in a finite family
`Ps`, suppose `p` has degree `< k` (`deg p ≤ k − 1`), `Q` vanishes to order `m` at
the curve points over an agreement set `S p`, and the agreement condition
`m · |S p| > D` holds.  Then the number of candidates is at most the `Y`-degree of
`Q`:

  `Ps.card ≤ Q.natDegree`. -/
theorem gs_list_size_bound
    {ι : Type*} (Q : (F[X])[X]) (hQ : Q ≠ 0) {k D m : ℕ}
    (xs : ι → F) (Ps : Finset F[X]) (S : F[X] → Finset ι)
    (hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ D)
    (hpdeg : ∀ p ∈ Ps, p.natDegree ≤ k - 1)
    (hvan : ∀ p ∈ Ps, ∀ i ∈ S p,
      ArkLib.GS.vanishesToOrder m Q (xs i) (p.eval (xs i)))
    (hxinj : ∀ p ∈ Ps, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hagree : ∀ p ∈ Ps, D < m * (S p).card) :
    Ps.card ≤ Q.natDegree := by
  apply GSFactorExtract.gs_list_size_le Q hQ Ps
  intro p hp
  exact gs_dvd_of_agreement Q p xs (S p) (hpdeg p hp) hwd
    (hvan p hp) (hxinj p hp) (hagree p hp)

/-- **List-size bound, `D / (k-1)` form (A3 degree budget folded in).** Under the
hypotheses of `gs_list_size_bound`, together with positivity of the weight `k − 1`,
the candidate count is bounded by `D / (k − 1)`. This is the classical
`L ≤ D/(k-1)` Guruswami–Sudan output-list bound. -/
theorem gs_list_size_bound_div
    {ι : Type*} (Q : (F[X])[X]) (hQ : Q ≠ 0) {k D m : ℕ}
    (xs : ι → F) (Ps : Finset F[X]) (S : F[X] → Finset ι)
    (hk : 0 < k - 1)
    (hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ D)
    (hpdeg : ∀ p ∈ Ps, p.natDegree ≤ k - 1)
    (hvan : ∀ p ∈ Ps, ∀ i ∈ S p,
      ArkLib.GS.vanishesToOrder m Q (xs i) (p.eval (xs i)))
    (hxinj : ∀ p ∈ Ps, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hagree : ∀ p ∈ Ps, D < m * (S p).card) :
    Ps.card ≤ D / (k - 1) := by
  refine le_trans
    (gs_list_size_bound Q hQ xs Ps S hwd hpdeg hvan hxinj hagree) ?_
  exact GuruswamiSudan.natDegree_le_of_natWeightedDegree hk hwd

/-! ## The parameter window `D := m·a − 1`

Instantiating the degree bound at `D := m·a − 1` makes the agreement condition
`m · a > D` *automatic* (`m·a > m·a − 1`), so a single agreement threshold `a`
suffices: any candidate agreeing on `≥ a` points is captured.  Simultaneously, the
dimension/feasibility condition for the interpolation pillar becomes the purely
arithmetic inequality

  `n · (m·(m+1)/2)  <  #monomials(m·a − 1, k)`,

with `#monomials(D, k) = (GSMultInterp.monoIdx k D).card`.  This is the
Johnson-regime instantiation reduced to arithmetic. -/

/-- The agreement condition is automatic in the window `D := m·a − 1`, for any
agreement set of size `≥ a` (with multiplicity `m ≥ 1` and threshold `a ≥ 1`). -/
theorem agreement_window
    {m a c : ℕ} (hm : 0 < m) (ha : 0 < a) (hc : a ≤ c) :
    m * a - 1 < m * c := by
  have h1 : m * a ≤ m * c := Nat.mul_le_mul_left m hc
  have hpos : 0 < m * a := Nat.mul_pos hm ha
  omega

/-- **Guruswami–Sudan list-size bound — explicit parameter window `D := m·a − 1`.**

Fix an agreement threshold `a ≥ 1`.  Let `Q : F[X][Y]` be a nonzero interpolant of
`(1, k-1)`-weighted degree `≤ m·a − 1`.  For every candidate `p` in the finite
family `Ps`, suppose `p` has degree `< k`, `Q` vanishes to order `m` at the curve
points over an agreement set `S p`, and `p` *agrees on at least `a` points*
(`a ≤ |S p|`).  Then

  `Ps.card ≤ Q.natDegree`,

with the agreement condition `m·a > D` discharged automatically by the window
choice.  This is the Johnson-regime statement in which the only remaining feasibility
requirement is the *arithmetic* dimension inequality
`n · (m·(m+1)/2) < #monomials(m·a − 1, k)`. -/
theorem gs_list_size_window
    {ι : Type*} (Q : (F[X])[X]) (hQ : Q ≠ 0) {k m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (xs : ι → F) (Ps : Finset F[X]) (S : F[X] → Finset ι)
    (hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ m * a - 1)
    (hpdeg : ∀ p ∈ Ps, p.natDegree ≤ k - 1)
    (hvan : ∀ p ∈ Ps, ∀ i ∈ S p,
      ArkLib.GS.vanishesToOrder m Q (xs i) (p.eval (xs i)))
    (hxinj : ∀ p ∈ Ps, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hcard : ∀ p ∈ Ps, a ≤ (S p).card) :
    Ps.card ≤ Q.natDegree := by
  refine gs_list_size_bound Q hQ xs Ps S hwd hpdeg hvan hxinj ?_
  intro p hp
  exact agreement_window (m := m) (a := a) (c := (S p).card)
    (hm := hm) (ha := ha) (hc := hcard p hp)

/-- **Parameter-window list-size bound, `D / (k-1)` form.** Same hypotheses as
`gs_list_size_window`, with `0 < k − 1`, giving the explicit
`Ps.card ≤ (m·a − 1) / (k − 1)`. -/
theorem gs_list_size_window_div
    {ι : Type*} (Q : (F[X])[X]) (hQ : Q ≠ 0) {k m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (xs : ι → F) (Ps : Finset F[X]) (S : F[X] → Finset ι)
    (hk : 0 < k - 1)
    (hwd : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ m * a - 1)
    (hpdeg : ∀ p ∈ Ps, p.natDegree ≤ k - 1)
    (hvan : ∀ p ∈ Ps, ∀ i ∈ S p,
      ArkLib.GS.vanishesToOrder m Q (xs i) (p.eval (xs i)))
    (hxinj : ∀ p ∈ Ps, ∀ i ∈ S p, ∀ j ∈ S p, xs i = xs j → i = j)
    (hcard : ∀ p ∈ Ps, a ≤ (S p).card) :
    Ps.card ≤ (m * a - 1) / (k - 1) := by
  refine gs_list_size_bound_div Q hQ xs Ps S hk hwd hpdeg hvan hxinj ?_
  intro p hp
  exact agreement_window (m := m) (a := a) (c := (S p).card)
    (hm := hm) (ha := ha) (hc := hcard p hp)

/-! ## The dimension/feasibility window: purely arithmetic interpolation existence

In the window `D := m·a − 1`, the interpolation pillar
`GSMultInterp.exists_ne_zero_vanishesToOrder` becomes feasible exactly when the
arithmetic inequality

  `n · (m·(m+1)/2) < (GSMultInterp.monoIdx k (m·a − 1)).card`

holds.  We record this as the existence of a nonzero coefficient vector vanishing to
order `m` at all interpolation points, with the dimension condition phrased directly
at the window value.  (This is the coefficient-vector pillar; bridging it to the
`F[X][Y]` interpolant `Q` of `gs_list_size_window` is the separate
coefficient-vector ↔ bivariate-polynomial dictionary, not folded in here.) -/

/-- **Interpolation feasibility in the window `D := m·a − 1`** (the dimension
condition becomes purely arithmetic).  If
`n · (m·(m+1)/2) < #monomials(m·a − 1, k)`, then there is a nonzero interpolant
coefficient vector vanishing to order `m` at all `n` interpolation points.  Direct
specialization of `GSMultInterp.exists_ne_zero_vanishesToOrder` to `D := m·a − 1`. -/
theorem interpolation_feasible_window (k m a n : ℕ) (xs ys : Fin n → F)
    (hdim : n * (m * (m + 1) / 2) < (GSMultInterp.monoIdx k (m * a - 1)).card) :
    ∃ c : GSMultInterp.CoeffSpace (F := F) k (m * a - 1), c ≠ 0 ∧
      ∀ i : Fin n, GSMultInterp.vanishesToOrder k (m * a - 1) m c (xs i) (ys i) :=
  GSMultInterp.exists_ne_zero_vanishesToOrder k (m * a - 1) m n xs ys hdim

end

end GSListSizeBound

-- Axiom audit: every theorem reduces to the three standard axioms.
#print axioms GSListSizeBound.gs_dvd_of_agreement
#print axioms GSListSizeBound.gs_list_size_bound
#print axioms GSListSizeBound.gs_list_size_bound_div
#print axioms GSListSizeBound.agreement_window
#print axioms GSListSizeBound.gs_list_size_window
#print axioms GSListSizeBound.gs_list_size_window_div
#print axioms GSListSizeBound.interpolation_feasible_window
