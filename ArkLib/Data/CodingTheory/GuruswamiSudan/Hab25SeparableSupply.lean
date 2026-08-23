/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.Hab25FactorWeld
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSquarefreePart

/-!
# Hab25 §3 — the good-`z` supply: separable specializations at all but finitely many `z`

`Hab25FactorWeld.lean` proved the S6→S8 weld (per-good-`z` uniqueness of the claiming
factor + affine pinning) conditional on one analytic input: the **separable-specialization
condition** `hnosq` — the specialized integer interpolant `W₀|_{Z:=z}` has no repeated
linear factor. This file **discharges that input at all but finitely many `z`** for the
squarefree part `radical Q` in characteristic zero, closing residual (i) of the weld:

* `separable_C_mul_of_ne_zero` — separability is preserved by nonzero constant scaling
  (the Bézout pair rescales).

* `integer_rep_discr_ne_zero` — if the `K = F(Z)`-level polynomial `W` has separable image
  in `Frac(K[X])`, then the **integer representative** `W₀ ∈ F[Z][X][Y]` already has
  nonzero discriminant over `F[Z][X]`: route `W₀` through the composite injective
  coefficient hom `F[Z][X] → K[X] → Frac(K[X])`, where its image is the nonzero-constant
  multiple `C (ι (C (φ e))) · W̄` of the separable `W̄` — then
  `Polynomial.discr_ne_zero_of_separable_map` pulls `discr ≠ 0` back to the integer level.

* `exists_good_specialization_no_sq_linear` — **the cofinite good set**: if
  `0 < natDegree_Y W₀` and `discr_Y W₀ ≠ 0`, there is a nonzero `g ∈ F[Z]` such that for
  every `z` with `g(z) ≠ 0` the specialization `W₀|_{Z:=z}` has **no repeated linear
  factor**. The polynomial `g` is the product of one surviving coefficient of the leading
  `Y`-coefficient (degree preservation at `z`) and one surviving coefficient of the
  discriminant (discriminant nonvanishing at `z`); the chain is
  `discr(W₀|_z) = (discr W₀)|_z ≠ 0` (`discr_map_of_natDegree_preserved`), push into
  `RatFunc F`, `separable_of_discr_ne_zero`, then root simplicity
  (`not_sq_linear_dvd_of_separable_map`).

* `radical_rep_good_specialization_charZero` — **the char-0 capstone**: for the squarefree
  part `W = radical Q` of a GS interpolant with at least one decoded linear factor, *any*
  integer representative `(e, W₀)` admits a nonzero `g ∈ F[Z]` whose non-roots `z` all
  satisfy the separable-specialization condition. Combined with
  `exists_specialized_factor_assignment_sep` (applied to `radical Q`, whose decoded linear
  factors agree with those of `Q` by `radical_linearFactor_dvd_iff`), the claiming factor
  of every per-`z` decoded root is **unique** at all but finitely many `z` in
  characteristic zero — no hypothesis remains on this side of the weld.

What remains of the full Hab25 §3 capture kernel after this file is only residual (ii) of
`Hab25FactorWeld.lean`: the Hensel linearity of the claiming factor (no per-`z` decoded
root hides in a `Y`-degree `≥ 2` factor — BCIKS20 §5 Steps 5–7 / Appendix C), plus the
finite-bad-`z` bookkeeping (`|{z : bad(z)·g(z) = 0}| ≤ deg bad + deg g`).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate UniqueFactorizationMonoid

namespace GuruswamiSudan.OverRatFunc

attribute [local instance] Classical.propDecidable

/-- **Separability survives nonzero constant scaling** (over a field): the Bézout pair of
`f` rescales to a Bézout pair of `C c * f`. -/
theorem separable_C_mul_of_ne_zero {L : Type*} [Field L] {c : L} (hc : c ≠ 0)
    {f : L[X]} (hf : f.Separable) : (Polynomial.C c * f).Separable := by
  rw [Polynomial.separable_def] at hf ⊢
  obtain ⟨u, v, huv⟩ := hf
  refine ⟨Polynomial.C c⁻¹ * u, Polynomial.C c⁻¹ * v, ?_⟩
  rw [Polynomial.derivative_C_mul]
  calc Polynomial.C c⁻¹ * u * (Polynomial.C c * f) +
        Polynomial.C c⁻¹ * v * (Polynomial.C c * Polynomial.derivative f)
      = (Polynomial.C c⁻¹ * Polynomial.C c) *
          (u * f + v * Polynomial.derivative f) := by ring
    _ = 1 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul, huv]

variable {F : Type} [Field F]

/-- **The integer representative inherits a nonzero discriminant.** If the `K = F(Z)`-level
polynomial `W` has separable image in `Frac(K[X])`, then any integer representative
`W₀ ∈ F[Z][X][Y]` (with `Ψ W₀ = C (C (φ e)) · W`, `e ≠ 0`) of positive `Y`-degree has
`discr_Y W₀ ≠ 0` over `F[Z][X]`. -/
theorem integer_rep_discr_ne_zero
    {W : (RatFunc F)[X][Y]} {e : F[X]} {W₀ : (F[X])[X][Y]} (he : e ≠ 0)
    (hrep : W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) * W)
    (hdeg : 0 < W₀.natDegree)
    (hsep : (W.map (algebraMap (RatFunc F)[X]
      (FractionRing ((RatFunc F)[X])))).Separable) :
    W₀.discr ≠ 0 := by
  classical
  set ι := algebraMap (RatFunc F)[X] (FractionRing ((RatFunc F)[X])) with hι
  have hιinj : Function.Injective ι :=
    IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X]))
  have hφinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have h2 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ hφinj
  set χ : (F[X])[X] →+* FractionRing ((RatFunc F)[X]) :=
    ι.comp (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) with hχ
  have hχinj : Function.Injective ⇑χ := by
    rw [hχ, RingHom.coe_comp]
    exact hιinj.comp h2
  -- the image of the integer representative under the composite hom
  have hmap : W₀.map χ =
      Polynomial.C (ι (Polynomial.C (algebraMap F[X] (RatFunc F) e))) * W.map ι := by
    rw [hχ, ← Polynomial.map_map, hrep, Polynomial.map_mul, Polynomial.map_C]
  -- the surviving constant is nonzero, so the image is separable
  have hc0 : ι (Polynomial.C (algebraMap F[X] (RatFunc F) e)) ≠ 0 := by
    intro h0
    have h1 : (Polynomial.C (algebraMap F[X] (RatFunc F) e) : (RatFunc F)[X]) = 0 :=
      hιinj (by rw [h0, map_zero])
    rw [Polynomial.C_eq_zero] at h1
    exact he ((map_eq_zero_iff _ hφinj).mp h1)
  have hsepχ : (W₀.map χ).Separable := by
    rw [hmap]
    exact separable_C_mul_of_ne_zero hc0 hsep
  exact Polynomial.discr_ne_zero_of_separable_map hχinj hdeg hsepχ

/-- **The cofinite good set for the separable-specialization condition.** If the integer
interpolant `W₀ ∈ F[Z][X][Y]` has positive `Y`-degree and nonzero `Y`-discriminant, there
is a nonzero `g ∈ F[Z]` such that at every `z` with `g(z) ≠ 0` the specialization
`W₀|_{Z:=z}` has **no repeated linear factor** — exactly the `hnosq` input of the
uniqueness clause of `exists_specialized_factor_assignment_sep`. -/
theorem exists_good_specialization_no_sq_linear
    {W₀ : (F[X])[X][Y]} (hdeg : 0 < W₀.natDegree) (hdiscr : W₀.discr ≠ 0) :
    ∃ g : F[X], g ≠ 0 ∧ ∀ z : F, g.eval z ≠ 0 →
      ∀ r : F[X], ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣
        W₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) := by
  classical
  have hW₀ : W₀ ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (lt_irrefl 0)
  have hlc : W₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hW₀
  -- choose surviving coefficients of the leading coefficient and the discriminant
  obtain ⟨j₀, hj₀⟩ : ∃ j, (W₀.leadingCoeff).coeff j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hlc (Polynomial.ext fun j => by rw [hall j, Polynomial.coeff_zero])
  obtain ⟨i₀, hi₀⟩ : ∃ i, (W₀.discr).coeff i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hdiscr (Polynomial.ext fun i => by rw [hall i, Polynomial.coeff_zero])
  refine ⟨(W₀.leadingCoeff).coeff j₀ * (W₀.discr).coeff i₀,
    mul_ne_zero hj₀ hi₀, ?_⟩
  intro z hz r
  have hz1 : ((W₀.leadingCoeff).coeff j₀).eval z ≠ 0 := fun h0 =>
    hz (by rw [Polynomial.eval_mul, h0, zero_mul])
  have hz2 : ((W₀.discr).coeff i₀).eval z ≠ 0 := fun h0 =>
    hz (by rw [Polynomial.eval_mul, h0, mul_zero])
  set σ : (F[X])[X] →+* F[X] := Polynomial.mapRingHom (Polynomial.evalRingHom z) with hσ
  have hσapp : ∀ p : (F[X])[X], σ p = p.map (Polynomial.evalRingHom z) := fun _ => rfl
  -- the leading coefficient survives the specialization, so the degree is preserved
  have hlcz : σ W₀.leadingCoeff ≠ 0 := by
    intro h0
    apply hz1
    have h1 := congrArg (fun p : F[X] => p.coeff j₀) h0
    simpa only [hσapp, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.coeff_zero] using h1
  have hmapdeg : (W₀.map σ).natDegree = W₀.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero σ hlcz
  -- the discriminant commutes with the specialization and survives at `z`
  have hdz : (W₀.map σ).discr = σ W₀.discr :=
    Polynomial.discr_map_of_natDegree_preserved hdeg hmapdeg
  have hdz0 : σ W₀.discr ≠ 0 := by
    intro h0
    apply hz2
    have h1 := congrArg (fun p : F[X] => p.coeff i₀) h0
    simpa only [hσapp, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
      Polynomial.coeff_zero] using h1
  -- push into the fraction field `RatFunc F` and conclude separability
  have hψinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have hdeg2 : 0 < (W₀.map σ).natDegree := by rw [hmapdeg]; exact hdeg
  have hmapdeg2 : ((W₀.map σ).map (algebraMap F[X] (RatFunc F))).natDegree =
      (W₀.map σ).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hψinj _
  have hdisc2 : ((W₀.map σ).map (algebraMap F[X] (RatFunc F))).discr ≠ 0 := by
    rw [Polynomial.discr_map_of_natDegree_preserved hdeg2 hmapdeg2, hdz]
    intro h0
    exact hdz0 ((map_eq_zero_iff _ hψinj).mp h0)
  have hsep2 : ((W₀.map σ).map (algebraMap F[X] (RatFunc F))).Separable :=
    Polynomial.separable_of_discr_ne_zero (by rw [hmapdeg2]; exact hdeg2) hdisc2
  exact not_sq_linear_dvd_of_separable_map (algebraMap F[X] (RatFunc F)) hsep2 r

/-- **The char-0 good-`z` supply for the squarefree part (residual (i) of the weld,
discharged).** Let `Q` be any nonzero `K = F(Z)`-level interpolant with at least one
decoded linear factor, `F` of characteristic zero, and `(e, W₀)` any integer representative
of the squarefree part `radical Q`. Then there is a nonzero `g ∈ F[Z]` such that at every
`z` with `g(z) ≠ 0` the specialization `W₀|_{Z:=z}` has no repeated linear factor — the
`hnosq` input of the weld's uniqueness clause holds at all but finitely many `z`. -/
theorem radical_rep_good_specialization_charZero [CharZero F]
    {Q : (RatFunc F)[X][Y]} (hQ0 : Q ≠ 0)
    {e : F[X]} {W₀ : (F[X])[X][Y]} (he : e ≠ 0)
    (hrep : W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) * radical Q)
    {p : (RatFunc F)[X]}
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ Q) :
    ∃ g : F[X], g ≠ 0 ∧ ∀ z : F, g.eval z ≠ 0 →
      ∀ r : F[X], ¬ ((Polynomial.X - Polynomial.C r) ^ 2 ∣
        W₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) := by
  classical
  -- positive degree of the squarefree part, transferred to the integer representative
  have hWdeg : 0 < (radical Q : (RatFunc F)[X][Y]).natDegree :=
    natDegree_radical_pos_of_linearFactor_dvd hQ0 hdvd
  have hrad0 : (radical Q : (RatFunc F)[X][Y]) ≠ 0 := radical_ne_zero
  have hφinj : Function.Injective (algebraMap F[X] (RatFunc F)) :=
    RatFunc.algebraMap_injective F
  have hφe : algebraMap F[X] (RatFunc F) e ≠ 0 := fun h0 =>
    he ((map_eq_zero_iff _ hφinj).mp h0)
  have hcc : (Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) e)) :
      (RatFunc F)[X][Y]) ≠ 0 := by
    simpa using hφe
  have h2 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_injective _ hφinj
  have h1 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      W₀.natDegree :=
    Polynomial.natDegree_map_eq_of_injective h2 W₀
  have h3 : (W₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))).natDegree =
      (radical Q : (RatFunc F)[X][Y]).natDegree := by
    rw [hrep, Polynomial.natDegree_mul hcc hrad0, Polynomial.natDegree_C, zero_add]
  have hdeg : 0 < W₀.natDegree := by
    rw [← h1, h3]
    exact hWdeg
  -- separability of the squarefree part over the perfect fraction field (char 0)
  haveI : CharZero (RatFunc F) :=
    charZero_of_injective_algebraMap (algebraMap F (RatFunc F)).injective
  haveI : CharZero ((RatFunc F)[X]) :=
    charZero_of_injective_algebraMap
      (C_injective : Function.Injective (C (R := RatFunc F)))
  haveI : CharZero (FractionRing ((RatFunc F)[X])) :=
    charZero_of_injective_algebraMap
      (IsFractionRing.injective ((RatFunc F)[X]) (FractionRing ((RatFunc F)[X])))
  have hsep : ((radical Q : (RatFunc F)[X][Y]).map
      (algebraMap (RatFunc F)[X] (FractionRing ((RatFunc F)[X])))).Separable :=
    separable_map_radical Q
  -- the integer representative has nonzero discriminant; conclude the cofinite good set
  exact exists_good_specialization_no_sq_linear hdeg
    (integer_rep_discr_ne_zero he hrep hdeg hsep)

end GuruswamiSudan.OverRatFunc

/-! ## Axiom audit — all kernel-clean. -/
#print axioms GuruswamiSudan.OverRatFunc.separable_C_mul_of_ne_zero
#print axioms GuruswamiSudan.OverRatFunc.integer_rep_discr_ne_zero
#print axioms GuruswamiSudan.OverRatFunc.exists_good_specialization_no_sq_linear
#print axioms GuruswamiSudan.OverRatFunc.radical_rep_good_specialization_charZero
