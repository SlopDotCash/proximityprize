/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceMappedSeparability
import ArkLib.ToMathlib.DiscriminantSeparableConverse

/-!
# Issue #304 — trivariate separability characterized (`SurfaceSeparabilitySupply` kernel)

Mathlib's `Polynomial.Separable p := IsCoprime p p.derivative` demands a Bézout identity
`A·p + B·p′ = 1` **in the coefficient ring itself**.  Over a non-field base (here `F[Z]` or
`F[Z][X]`) this is far stronger than squarefreeness, and this file machine-checks exactly
how strong, against the open #304 residual
`ArkLib.GSSurfaceSupply.SurfaceSeparabilitySupply (Q₀ : F[X][X][Y]) := Q₀.Separable`.

## Brick 1 — the refutation witness

* `Polynomial.Separable.isCoprime_eval` — a Bézout identity survives **every** evaluation:
  separability of `p` forces `IsCoprime (p.eval c) (p.derivative.eval c)` in the base ring,
  for every point `c`.
* `Polynomial.not_separable_X_pow_two_sub_C` — hence `Y² − C r` is **never** separable when
  `r` is not a unit of the base (evaluate the Bézout identity at `Y := 0`:
  `A(0)·(−r) = 1`).  No characteristic hypothesis: in char 2 the derivative term dies even
  faster.  Instantiated in the exact `SurfaceSeparabilitySupply` ring shape as
  `surfaceSeparabilitySupply_counterexample_Z` (`Y² − Z`, irreducible-style quadratic) and
  `surfaceSeparabilitySupply_counterexample_X` (`Y² − X`): **`SurfaceSeparabilitySupply` is
  not satisfiable in general**, even for squarefree, content-primitive trivariates.

## Brick 2 — the characterization (unit-resultant / unit-discriminant forcing)

* `Polynomial.Separable.isUnit_resultant_derivative` — for monic `p : R[Y]`, separability
  forces `Res_Y(p, p′)` to be a **unit of `R`** (via Mathlib's
  `isUnit_resultant_iff_isCoprime`).
* `Polynomial.Separable.isUnit_discr` — likewise the discriminant `p.discr` is a unit of
  `R` (the sign/leading-coefficient normalization of `resultant_deriv` is monic-trivial).
* `discr_eq_nonzero_const_of_separable_polyBase` — the concrete currency over `R = F[Z]`:
  the discriminant must be a **nonzero constant**, i.e. it may vanish at *no* specialization
  whatsoever.  Contrast: the in-tree GS chain (`GSSurfaceRadicalSupply`,
  `DiscriminantBadSet`) only ever certifies `disc ≠ 0` *generically*, away from a finite
  bad set of centres — for the GS integer representative the `Y`-discriminant is a honest
  nonconstant polynomial (it vanishes at the bad centres), so the supply is **false** for
  any such `Q₀`.  The contrapositive specialization tests:
* `Polynomial.not_separable_of_map_not_separable` (any inseparable specialization refutes,
  from Mathlib's `Separable.map`) and `Polynomial.not_separable_of_discr_map_eq_zero` (a
  single field specialization with vanishing discriminant refutes, via the in-tree
  `discr_ne_zero_of_separable`).

## Brick 3 — the weld (what the consumers actually need)

The audit in `GSSurfaceMappedSeparability.lean` shows the entire decoded-capstone chain
consumes `hR : R.Separable` through the **single** lemma
`specialized_separable_of_R_separable`, i.e. only through *mapped images* of `R` — exactly
the `Separable.map` channel of Brick 2.  The weakened consumer chain at the per-place
hypothesis `MappedSliceSeparability` is already in-tree
(`gammaGenuine_eq_trunc_of_surface_mapped` etc.); this file re-exports the supply-level
bridge `mappedSliceSeparability_of_supply` (`SurfaceSeparabilitySupply Q₀ →
MappedSliceSeparability hHyp`), so downstream code can quote the weld against the named
#304 `Prop` rather than the raw `Separable`.  The honest producible currency is
`MappedSliceSeparability.of_residue` (per-place **field-level** residue separability — the
kind of datum `DiscriminantSeparable`/`GSSurfaceRadicalSupply` supply), NOT the trivariate
Bézout identity.

## Brick 4 — the verdict for GS-shaped data

F8 (`not_surface_dvd_of_irreducible` + `hd2`) forces the surface-bearing trivariate to be
**reducible**: `Q₀ = (Y − C w) · G` with `degY G ≥ 1`.  Does reducibility alone kill the
supply?  **No**: reducible-and-separable coexist over a non-field base —
`separable_X_sub_C_mul_X_sub_C` / `surfaceSeparabilitySupply_of_split_surfaces` exhibit
`(Y − C w)(Y − C (w+1))`, separable because the root difference is a unit.  The genuine
obstruction is quantitative: `isUnit_cofactor_eval_of_supply` shows the supply forces the
cofactor evaluated **along the decoded surface** to be a unit of `F[Z][X]`, i.e.
(`cofactor_eval_eq_const_of_supply`) a nonzero **constant** `c ∈ F`.  So for GS-shaped
`Q₀`:

* satisfiable iff the `Y`-discriminant data is globally unit-like — `Q₀` splits into
  surfaces whose pairwise differences are units and whose cofactor values are constants;
* **refuted** the moment any specialization `(z, x) ↦` field has a repeated `Y`-root
  (Brick 1/2 contrapositives) — which is exactly the situation the §5 bad-centre counting
  manages.  `SurfaceSeparabilitySupply` as stated is therefore *not derivable* from the
  in-tree GS chain and is genuinely false outside the unit-discriminant regime; the
  consumers should be (and, by `GSSurfaceMappedSeparability`, already are) re-based on the
  per-place residue currency.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see the `#print axioms` footer).
-/

set_option linter.style.longLine false

namespace Polynomial

open scoped Polynomial

/-! ## Brick 2a — separability survives every evaluation / every base change -/

/-- **A Bézout identity survives evaluation**: if `p : R[X]` is separable then for *every*
point `c : R` the pair `(p(c), p′(c))` is coprime **in the base ring `R`** — in particular
the two values can never both lie in a proper ideal (both vanish at a specialization). -/
theorem Separable.isCoprime_eval {R : Type*} [CommRing R] {p : R[X]} (hs : p.Separable)
    (c : R) : IsCoprime (p.eval c) (p.derivative.eval c) := by
  have h := IsCoprime.map hs (evalRingHom c)
  simpa only [coe_evalRingHom] using h

/-- At a root `w` of a separable `p`, the derivative value `p′(w)` is forced to be a **unit**
of the base ring (not merely nonzero). -/
theorem Separable.isUnit_derivative_eval_of_isRoot {R : Type*} [CommRing R] {p : R[X]}
    (hs : p.Separable) {w : R} (hw : p.IsRoot w) : IsUnit (p.derivative.eval w) := by
  have h := hs.isCoprime_eval w
  rw [hw.eq_zero] at h
  exact isCoprime_zero_left.mp h

/-- Contrapositive of Mathlib's `Polynomial.Separable.map`: a single inseparable
specialization (any ring hom out of the base) refutes separability over the base. -/
theorem not_separable_of_map_not_separable {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {p : R[X]} (h : ¬ (p.map f).Separable) : ¬ p.Separable :=
  fun hs => h hs.map

/-- A single **field** specialization with vanishing discriminant (and surviving positive
degree) refutes separability over the base — via the in-tree converse
`discr_ne_zero_of_separable`. -/
theorem not_separable_of_discr_map_eq_zero {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) {p : R[X]} (hdeg : 0 < (p.map φ).natDegree)
    (h0 : (p.map φ).discr = 0) : ¬ p.Separable :=
  fun hs => discr_ne_zero_of_separable hdeg hs.map h0

/-! ## Brick 1 — the quadratic counterexample, in any base ring -/

/-- **The refutation witness, base-ring general**: `X² − C r` is never separable when `r` is
not a unit.  Evaluate the Bézout identity at `X := 0`: the derivative value dies
(`p′(0) = 0` — in *every* characteristic), leaving `IsCoprime (−r) 0`, i.e. `IsUnit r`.
Note `X² − C r` is squarefree/irreducible in the natural cases (e.g. `r = Z` over `F[Z]`,
char `F ≠ 2`), so this separates `Separable` from squarefreeness over non-field bases. -/
theorem not_separable_X_pow_two_sub_C {R : Type*} [CommRing R] {r : R} (hr : ¬ IsUnit r) :
    ¬ (Polynomial.X ^ 2 - Polynomial.C r : R[X]).Separable := by
  intro hs
  have h := hs.isCoprime_eval 0
  have hp : (Polynomial.X ^ 2 - Polynomial.C r : R[X]).eval 0 = -r := by simp
  have hd : ((Polynomial.X ^ 2 - Polynomial.C r : R[X]).derivative).eval 0 = 0 := by
    simp [derivative_sub]
  rw [hp, hd] at h
  exact hr ((IsUnit.neg_iff r).mp (isCoprime_zero_right.mp h))

/-! ## Brick 2b — unit-resultant / unit-discriminant forcing -/

/-- **Separability forces a unit resultant**: for monic `p : R[Y]`, a Bézout identity in
`R[Y]` makes `Res_Y(p, p′) ∈ R` a **unit** of the base ring (Mathlib's
`isUnit_resultant_iff_isCoprime`).  Since the resultant maps along every `R →+* K`, the
discriminant-like invariant may vanish at *no* specialization whatsoever. -/
theorem Separable.isUnit_resultant_derivative {R : Type*} [CommRing R] {p : R[X]}
    (hm : p.Monic) (hs : p.Separable) : IsUnit (p.resultant p.derivative) :=
  (isUnit_resultant_iff_isCoprime hm).mpr hs

/-- **Separability forces a unit discriminant** (monic, positive degree).  The padding to
size `natDegree − 1` is leading-coefficient-free for monic `p`, and the sign in
`resultant_deriv` splits off as a unit. -/
theorem Separable.isUnit_discr {R : Type*} [CommRing R] {p : R[X]}
    (hm : p.Monic) (hdeg : 0 < p.natDegree) (hs : p.Separable) : IsUnit p.discr := by
  have hres : IsUnit (p.resultant p.derivative) := hs.isUnit_resultant_derivative hm
  -- pad the derivative-side size up to `natDegree p − 1` (free of charge: `p` is monic)
  have hpad := resultant_add_right_deg p p.derivative p.natDegree p.derivative.natDegree
    ((p.natDegree - 1) - p.derivative.natDegree) le_rfl
  rw [show p.derivative.natDegree + ((p.natDegree - 1) - p.derivative.natDegree)
      = p.natDegree - 1 by have := natDegree_derivative_le p; omega,
    coeff_natDegree, hm.leadingCoeff, one_pow, one_mul] at hpad
  -- match against the discriminant–resultant identity
  have hrd := resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg)
  rw [hpad, hm.leadingCoeff, mul_one] at hrd
  exact (IsUnit.mul_iff.mp (hrd ▸ hres)).2

/-! ## Brick 4a — the reducible case: cofactor-value forcing and the positive witness -/

/-- **The cofactor forcing**: if `(X − C w) · G` is separable, then the cofactor evaluated
at the root, `G(w)`, is a **unit** of the base ring.  (Derivative of the product at `X := w`
collapses to `G(w)`; apply `isUnit_derivative_eval_of_isRoot`.)  For GS-shaped data this is
the precise rigidity that `SurfaceSeparabilitySupply` imposes along the decoded surface. -/
theorem isUnit_eval_of_separable_mul {R : Type*} [CommRing R] {w : R} {G : R[X]}
    (hs : ((Polynomial.X - Polynomial.C w) * G).Separable) : IsUnit (G.eval w) := by
  have hroot : ((Polynomial.X - Polynomial.C w) * G).IsRoot w := by
    simp [Polynomial.IsRoot.def]
  have hu := hs.isUnit_derivative_eval_of_isRoot hroot
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hu
  simpa using hu

/-- **Reducible and separable DO coexist over a non-field base**: two surfaces whose
difference is a unit have separable product.  (So the F8-forced reducibility does *not* by
itself refute `SurfaceSeparabilitySupply`; the genuine obstruction is the unit-discriminant
forcing above.) -/
theorem separable_X_sub_C_mul_X_sub_C {R : Type*} [CommRing R] {a b : R}
    (h : IsUnit (a - b)) :
    ((Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)).Separable :=
  (separable_X_sub_C (x := a)).mul (separable_X_sub_C (x := b))
    (isCoprime_X_sub_C_of_isUnit_sub h)

end Polynomial

/-! ## The GS-shaped instantiations (`SurfaceSeparabilitySupply`) -/

namespace ArkLib

namespace TrivariateSeparability

open Polynomial Polynomial.Bivariate
open ArkLib.GSSurfaceSupply (SurfaceSeparabilitySupply)

variable {F : Type} [Field F]

/-- **Brick 1, in the exact #304 ring shape**: the supply `Prop` is **not satisfiable in
general** — the trivariate `Y² − Z` (innermost variable `Z`, the surface "Y² = Z") is
inseparable over the base `F[Z][X]`, in every characteristic, because `Z` is not a unit. -/
theorem surfaceSeparabilitySupply_counterexample_Z :
    ¬ SurfaceSeparabilitySupply
      (Polynomial.X ^ 2 - Polynomial.C (Polynomial.C Polynomial.X) : F[X][X][Y]) :=
  Polynomial.not_separable_X_pow_two_sub_C
    (fun h => Polynomial.not_isUnit_X (Polynomial.isUnit_C.mp h))

/-- Same with the **middle** variable (the GS `X`): `Y² − X` is inseparable as a trivariate. -/
theorem surfaceSeparabilitySupply_counterexample_X :
    ¬ SurfaceSeparabilitySupply
      (Polynomial.X ^ 2 - Polynomial.C Polynomial.X : F[X][X][Y]) :=
  Polynomial.not_separable_X_pow_two_sub_C Polynomial.not_isUnit_X

/-- **Brick 4 (negative half), in supply currency**: a decoded surface factorization
`Q₀ = (Y − C w) · G` plus the supply forces the cofactor value along the surface,
`G.eval (C w) ∈ F[Z][X]`-style — here `G.eval w` over the base `F[X][Y]` — to be a unit. -/
theorem isUnit_cofactor_eval_of_supply {Q₀ : F[X][X][Y]} {w : F[X][Y]} {G : F[X][X][Y]}
    (hG : Q₀ = (Polynomial.X - Polynomial.C w) * G)
    (hR : SurfaceSeparabilitySupply Q₀) : IsUnit (G.eval w) :=
  Polynomial.isUnit_eval_of_separable_mul (hG ▸ hR)

/-- The unit of the previous theorem, unpacked over the domain base `F[Z][X]`: the cofactor
evaluated along the decoded surface must be a **nonzero constant** `c ∈ F` — the concrete
rigidity that makes the supply underivable for honest GS interpolants (whose cofactor data
genuinely depends on `(Z, X)`). -/
theorem cofactor_eval_eq_const_of_supply {Q₀ : F[X][X][Y]} {w : F[X][Y]} {G : F[X][X][Y]}
    (hG : Q₀ = (Polynomial.X - Polynomial.C w) * G)
    (hR : SurfaceSeparabilitySupply Q₀) :
    ∃ c : F, c ≠ 0 ∧ G.eval w = Polynomial.C (Polynomial.C c) := by
  have hu := isUnit_cofactor_eval_of_supply hG hR
  obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨c, hc, hCc⟩ := Polynomial.isUnit_iff.mp hr
  exact ⟨c, hc.ne_zero, by rw [← hCr, ← hCc]⟩

/-- **Brick 4 (positive half), in supply currency**: the supply IS satisfiable at a
*reducible* trivariate with `degY = 2` — the split pair of surfaces `w` and `w + 1`
(difference `−1`, a unit).  So F8's forced reducibility alone does not refute the supply;
only the unit-discriminant forcing does. -/
theorem surfaceSeparabilitySupply_of_split_surfaces (w : F[X][Y]) :
    SurfaceSeparabilitySupply
      ((Polynomial.X - Polynomial.C w) * (Polynomial.X - Polynomial.C (w + 1)) : F[X][X][Y]) :=
  Polynomial.separable_X_sub_C_mul_X_sub_C
    (show IsUnit (w - (w + 1)) by
      rw [show w - (w + 1) = -1 by ring]
      exact (IsUnit.neg_iff (1 : F[X][Y])).mpr isUnit_one)

/-- **Brick 2, in the concrete `F[Z]`-currency**: for a monic positive-degree polynomial
over a univariate base, separability forces the discriminant to be a **nonzero constant** —
it may vanish at no specialization at all.  The in-tree GS chain only certifies generic
(`away from finitely many bad centres`) nonvanishing, which is strictly weaker; this is the
exact daylight between the open `SurfaceSeparabilitySupply` and the discharged
`DiscriminantSeparable`/`GSSurfaceRadicalSupply` front. -/
theorem discr_eq_nonzero_const_of_separable_polyBase {p : (Polynomial F)[X]}
    (hm : p.Monic) (hdeg : 0 < p.natDegree) (hs : p.Separable) :
    ∃ c : F, c ≠ 0 ∧ p.discr = Polynomial.C c := by
  obtain ⟨c, hc, hCc⟩ := Polynomial.isUnit_iff.mp (hs.isUnit_discr hm hdeg)
  exact ⟨c, hc.ne_zero, hCc.symm⟩

end TrivariateSeparability

namespace MappedSeparability

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Brick 3 (the weld), at the named #304 `Prop`**: the open supply implies the
consolidated per-place hypothesis that the decoded-capstone chain actually consumes
(`MappedSliceSeparability`, through whose `Separable.map`-shaped channel `hR` enters
*everything*).  Combined with `surfaceSeparabilitySupply_counterexample_Z` this confirms
the relocation in `GSSurfaceMappedSeparability.lean` is a **strict** weakening: the weak
side is producible from per-place field residues (`MappedSliceSeparability.of_residue`)
while the strong side is false outside the unit-discriminant regime. -/
theorem mappedSliceSeparability_of_supply {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hR : ArkLib.GSSurfaceSupply.SurfaceSeparabilitySupply R) :
    MappedSliceSeparability hHyp :=
  MappedSliceSeparability.of_separable hHyp hR

end MappedSeparability

end ArkLib

#print axioms Polynomial.Separable.isCoprime_eval
#print axioms Polynomial.Separable.isUnit_derivative_eval_of_isRoot
#print axioms Polynomial.not_separable_of_map_not_separable
#print axioms Polynomial.not_separable_of_discr_map_eq_zero
#print axioms Polynomial.not_separable_X_pow_two_sub_C
#print axioms Polynomial.Separable.isUnit_resultant_derivative
#print axioms Polynomial.Separable.isUnit_discr
#print axioms Polynomial.isUnit_eval_of_separable_mul
#print axioms Polynomial.separable_X_sub_C_mul_X_sub_C
#print axioms ArkLib.TrivariateSeparability.surfaceSeparabilitySupply_counterexample_Z
#print axioms ArkLib.TrivariateSeparability.surfaceSeparabilitySupply_counterexample_X
#print axioms ArkLib.TrivariateSeparability.isUnit_cofactor_eval_of_supply
#print axioms ArkLib.TrivariateSeparability.cofactor_eval_eq_const_of_supply
#print axioms ArkLib.TrivariateSeparability.surfaceSeparabilitySupply_of_split_surfaces
#print axioms ArkLib.TrivariateSeparability.discr_eq_nonzero_const_of_separable_polyBase
#print axioms ArkLib.MappedSeparability.mappedSliceSeparability_of_supply
