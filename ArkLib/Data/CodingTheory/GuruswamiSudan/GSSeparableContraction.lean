/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorDegreeOverRatFunc
import ArkLib.ToMathlib.DiscriminantSeparableConverse
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!
# Hab25 §3, characteristic `p`: separable cores of the GS interpolant factors

The only remaining piece of Step S5 in characteristic `p` is the inseparable-factor descent:
the paper writes each irreducible factor of the GS interpolant as
`R(X, Y) = R_sep(X, Y^{p^f})` with `R_sep` separable, and runs the discriminant /
Hensel argument on the separable core `R_sep`. This file formalizes the **existence of the
separable core with the exact payload S5 needs**:

* `irreducible_factor_separable_contraction` — for `F` of exponential characteristic `q` and
  any irreducible `R ∈ K[X][Y]` (`K = F(Z)`) of positive `Y`-degree, over the function field
  `L = K(X) = FractionRing K[X]` there are `g ∈ L[Y]` and `m : ℕ` with

  - `g.Separable`, `Irreducible g`, `0 < deg g`,
  - **`discr g ≠ 0`** (by the converse bridge `discr_ne_zero_of_separable`),
  - `g(Y^{q^m}) = R` in `L[Y]` (`expand L (q^m) g = R.map (algebraMap K[X] L)`),
  - `deg g · q^m = deg_Y R` (the inseparable degree bookkeeping).

  The chain: Gauss transports irreducibility of `R` to `L[Y]`
  (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`); Mathlib's
  `Irreducible.hasSeparableContraction` (Stacks 09H0) produces the contraction; `expand`
  reflects irreducibility (`of_irreducible_expand`) and multiplies degrees
  (`natDegree_expand`); and the converse discriminant bridge upgrades separability to
  `discr ≠ 0`.

In exponential characteristic one (char zero) this recovers `m = 0`, `g = R` — the
`GSSeparabilityCharZero.lean` situation. What remains for full char-`p` S5 is *quantitative*:
clearing denominators to descend `g` to `K[X][Y]` with controlled `X`-degrees, so the
avoidance engine can run on the cores. The Hensel lift (S6) consumes exactly the separable
core produced here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

/-- **The separable core of an irreducible GS factor, with nonzero discriminant.**

For `F` of exponential characteristic `q` and `R ∈ (RatFunc F)[X][Y]` irreducible of positive
`Y`-degree, the function field `L = K(X)` carries a separable irreducible core `g` of `R`:
`expand L (q^m) g` is the image of `R`, `deg g · q^m = deg_Y R`, and — the S5 payload —
`discr g ≠ 0`. This is the paper's `R(X,Y) = R_sep(X, Y^{p^f})` decomposition. -/
theorem irreducible_factor_separable_contraction (q : ℕ) [ExpChar F q]
    {R : (RatFunc F)[X][Y]} (hirr : Irreducible R) (hdeg : 0 < R.natDegree) :
    ∃ (g : Polynomial (FractionRing ((RatFunc F)[X]))) (m : ℕ),
      g.Separable ∧ Irreducible g ∧ 0 < g.natDegree ∧ g.discr ≠ 0 ∧
      Polynomial.expand _ (q ^ m) g =
        R.map (algebraMap ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))) ∧
      g.natDegree * q ^ m = R.natDegree := by
  classical
  -- transport the exponential characteristic up the algebra tower
  haveI : ExpChar (RatFunc F) q :=
    expChar_of_injective_ringHom (algebraMap F (RatFunc F)).injective q
  haveI : ExpChar ((RatFunc F)[X]) q :=
    expChar_of_injective_ringHom (C_injective (R := RatFunc F)) q
  haveI : ExpChar (FractionRing ((RatFunc F)[X])) q :=
    expChar_of_injective_ringHom
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))) q
  have hq0 : q ≠ 0 := (expChar_pos F q).ne'
  -- Gauss: irreducibility transports to the function field L = K(X)
  have hprim : R.IsPrimitive := hirr.isPrimitive hdeg.ne'
  have hirr' : Irreducible
      (R.map (algebraMap ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  -- the separable contraction (Stacks 09H0)
  obtain ⟨g, hgsep, m, hexp⟩ := hirr'.hasSeparableContraction q
  -- degree bookkeeping: deg g · q^m = deg_Y R
  have hmapdeg :
      (R.map (algebraMap ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))).natDegree =
        R.natDegree :=
    natDegree_map_eq_of_injective
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))) R
  have hdeg_eq : g.natDegree * q ^ m = R.natDegree := by
    rw [← hmapdeg, ← hexp, natDegree_expand]
  -- the core has positive degree
  have hgdeg : 0 < g.natDegree := by
    rcases Nat.eq_zero_or_pos g.natDegree with h0 | h
    · rw [h0, zero_mul] at hdeg_eq
      omega
    · exact h
  -- the core is irreducible, hence (being separable of positive degree) has discr ≠ 0
  have hgirr : Irreducible g :=
    of_irreducible_expand (pow_ne_zero m hq0) (by rw [hexp]; exact hirr')
  exact ⟨g, m, hgsep, hgirr, hgdeg,
    discr_ne_zero_of_separable hgdeg hgsep, hexp, hdeg_eq⟩

/-- **Char-`p` S5 dichotomy for GS factors.** Every positive-`Y`-degree irreducible factor of
the GS interpolant either already has nonzero `Y`-discriminant over `K[X]` (the separable
case — directly consumable by `gs_interpolant_good_specialization_of_dvd`), or it is a
genuine `q`-power expansion (`m ≥ 1`) of a smaller separable irreducible core with nonzero
discriminant over `K(X)`. The two branches are exactly the paper's separable/inseparable
factor split. -/
theorem factor_discr_ne_zero_or_contraction (q : ℕ) [ExpChar F q]
    {R : (RatFunc F)[X][Y]} (hirr : Irreducible R) (hdeg : 0 < R.natDegree) :
    R.discr ≠ 0 ∨
    ∃ (g : Polynomial (FractionRing ((RatFunc F)[X]))) (m : ℕ), 1 ≤ m ∧
      g.Separable ∧ Irreducible g ∧ 0 < g.natDegree ∧ g.discr ≠ 0 ∧
      Polynomial.expand _ (q ^ m) g =
        R.map (algebraMap ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))) ∧
      g.natDegree * q ^ m = R.natDegree := by
  obtain ⟨g, m, hgsep, hgirr, hgdeg, hgdiscr, hexp, hdeg_eq⟩ :=
    irreducible_factor_separable_contraction q hirr hdeg
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- m = 0: the factor itself is separable over L, so its discriminant over K[X] is nonzero
    left
    subst hm0
    rw [pow_zero, expand_one] at hexp
    refine Polynomial.discr_ne_zero_of_separable_map
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))
      hdeg ?_
    rw [← hexp]
    exact hgsep
  · exact Or.inr ⟨g, m, hm, hgsep, hgirr, hgdeg, hgdiscr, hexp, hdeg_eq⟩

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.irreducible_factor_separable_contraction
#print axioms GuruswamiSudan.OverRatFunc.factor_discr_ne_zero_or_contraction
