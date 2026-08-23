/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HenselMatchingPolySupply
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions
import ArkLib.ToMathlib.DiscriminantSeparable

/-!
# Issue #304 — `InterpolantInput` from the S10-converse GS surface

`HenselMatchingPolySupply.InterpolantInput` is the `F[X][Y]`-level input bundle of the Hensel
lane: per good `z`, a specialized interpolant `Q z`, the two matching divisibilities (for the
decoded `P z` and for the lift specialisation), order-0 agreement, and separability.  This file
wires the **S10-converse Guruswami–Sudan chain**
(`GuruswamiSudan.OverRatFunc.scalar_fold_decoded_divides_specialization`) into that bundle —
the last composite step on the Hensel lane: the per-`z` interpolant family is the
specialization family `z ↦ Q₀|_{Z:=z}` of ONE integer representative `Q₀` of the `K = F(Z)`-
level GS interpolant for the generic fold.

* `liftSpec` (+ `liftSpec_eq`, `liftSpec_natDegree_le`, `liftSpec_degree_lt`) — the
  competitor of the eval-shaped `hPz` lane, `Qz' z = (lift v₀ v₁).eval (C z)`, identified in
  closed form as the affine polynomial `C (v₀.eval z) + X · C (v₁.eval z)`; in particular it
  is a Reed–Solomon codeword polynomial whenever `2 ≤ deg`.
* `curveWord_line_eq` / `mem_lineGoodCoeffs_iff` — the `k = 1` curve word of
  `RS_goodCoeffsCurve` *is* the scalar fold `u 0 + z • u 1` of the S10 surface, so good-set
  membership is exactly `δ`-proximity of the fold to the code.
* `dvd_specialization_of_close` — **the core brick**: any polynomial `W` with
  `deg W < deg` whose evaluations lie within the GS Johnson radius of the scalar fold `f_z`
  satisfies `(Y − C W) ∣ Q₀|_{Z:=z}` (at every `z` where the specialization survives).  This
  upgrades `scalar_fold_decoded_divides_specialization` from `codewordToPoly p` to an
  arbitrary low-degree close polynomial via the Lagrange round-trip
  (`GuruswamiSudan.interpolate_eq_of_degree_lt`).
* `dvd_specialization_family` — the good-set family form, for an arbitrary decoding family
  `W : F → F[X]`.  Instantiated **twice** in the assembly: at the decoded family `P` (the
  `hPdvd` field) and at the lift-specialisation family `liftSpec v₀ v₁` (the `hQdvd` field).
  This answers the symmetric-competitor question affirmatively: the competitor IS a `δ`-close
  affine decoding of the same fold (for `2 ≤ deg`), so the SAME GS argument applies to it,
  consuming its own proximity hypothesis — no separate `hQdvd` source is needed.
* `hsep_of_discr_isUnit` — the discriminant-route separability supply at the `F[X][Y]` level:
  per-`z` unit leading coefficient + unit discriminant of `Q₀|_{Z:=z}` give the `hsep` field
  (`Polynomial.separable_of_leadingCoeff_isUnit_of_discr_isUnit`).  NB
  `PerPlaceSeparabilitySupply` produces separability **one level down** (the residue
  `F[Y]`-level specialization of a bivariate source, feeding `HenselDatum.hderiv` directly);
  `InterpolantInput.hsep` demands `Separable` over the non-field `F[X]`, whose honest
  discriminant route is the *unit*-discriminant one exposed here.
* `GSLineInput` / `GSLineInput.toInterpolantInput` / `GSLineInput.toHenselDatum` — the bundled
  S10-converse surface and the assembled producers into `InterpolantInput` and
  `HPzBridge.HenselDatum`.
* `hPz_of_gs_line` — **the capstone**: the `hPz` field (per-`z` identity
  `P z = (lift v₀ v₁).eval (C z)` on the good set, for every representative consistent with
  `γ`) from per-representative `GSLineInput` data, through
  `henselDatum_of_interpolantInput` and `HPzBridge.hPz_of_henselDatum`.

## Honest residuals

Nothing here fabricates §5/S10 content.  The residual hypotheses of `GSLineInput` are exactly
the recognized BCIKS20/Hab25 ingredients, each with its own in-tree production lane:

* the `K = F(Z)`-level GS `Conditions` for the generic fold — the S2 interpolation step
  (`GuruswamiSudan` solver surface over `RatFunc F`);
* the integer representative `(d, Q₀)` — fully discharged in-tree by
  `GuruswamiSudan.OverRatFunc.exists_integer_representative`;
* per-`z` non-collapse `Q₀|_{Z:=z} ≠ 0` — the cofinite bad-set fact (`d(z) ≠ 0` route);
* the two per-`z` proximity bounds (decoded `P z`, and the lift specialisation) within the GS
  Johnson radius of the fold — the per-`z` agreement counts of §5;
* per-`z` order-0 agreement and `F[X][Y]`-level separability — the common-approximation fact
  and the unit-discriminant geometry (`hsep_of_discr_isUnit` route).

None of these is `≡` the goal: the per-`z` identity `P z = (lift).eval (C z)` is *derived* by
Hensel uniqueness downstream.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5; Hab25 §3 Steps S2/S10.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace ArkLib

namespace InterpolantInputSupply

section Bricks

variable {F : Type} [Field F]

/-! ## The competitor in closed form -/

/-- **The lift-specialisation competitor** of the eval-shaped `hPz` lane:
`Qz' z = ((map C v₀) + (C X) · (map C v₁)).eval (C z)`.  This is *definitionally* the
competitor appearing in `HenselMatchingPolySupply.InterpolantInput.hQdvd`/`h0`. -/
noncomputable def liftSpec (v₀ v₁ : F[X]) (z : F) : F[X] :=
  ((Polynomial.map Polynomial.C v₀)
      + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
    (Polynomial.C z)

/-- **Closed form**: the competitor is the affine polynomial `C (v₀(z)) + X · C (v₁(z))`. -/
theorem liftSpec_eq (v₀ v₁ : F[X]) (z : F) :
    liftSpec v₀ v₁ z
      = Polynomial.C (v₀.eval z) + Polynomial.X * Polynomial.C (v₁.eval z) := by
  rw [liftSpec, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Polynomial.eval₂_at_apply]

/-- The competitor is (at most) affine in the Reed–Solomon variable. -/
theorem liftSpec_natDegree_le (v₀ v₁ : F[X]) (z : F) :
    (liftSpec v₀ v₁ z).natDegree ≤ 1 := by
  rw [liftSpec_eq]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp

/-- Degree-`< deg` helper (`WithBot` form, zero-polynomial-safe). -/
theorem degree_lt_of_natDegree_lt {W : F[X]} {deg : ℕ} (h : W.natDegree < deg) :
    W.degree < (deg : WithBot ℕ) := by
  rcases eq_or_ne W 0 with rfl | hW
  · rw [Polynomial.degree_zero]
    exact_mod_cast WithBot.bot_lt_coe deg
  · exact (Polynomial.natDegree_lt_iff_degree_lt hW).mp h

/-- For `2 ≤ deg` the competitor is a degree-`< deg` (Reed–Solomon codeword) polynomial. -/
theorem liftSpec_degree_lt {deg : ℕ} (hdeg2 : 2 ≤ deg) (v₀ v₁ : F[X]) (z : F) :
    (liftSpec v₀ v₁ z).degree < (deg : WithBot ℕ) :=
  degree_lt_of_natDegree_lt
    (lt_of_le_of_lt (liftSpec_natDegree_le v₀ v₁ z) (by omega))

end Bricks

/-! ## The `k = 1` curve word is the S10 scalar fold -/

section Line

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The degree-1 curve word of `RS_goodCoeffsCurve` is the scalar fold `u 0 + z • u 1` —
the exact received word of the S10-converse surface. -/
theorem curveWord_line_eq (u : WordStack F (Fin 2) (Fin n)) (z : F) :
    (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t) = fun i => u 0 i + z * u 1 i := by
  funext i
  show (∑ t : Fin 2, (z ^ (t : ℕ)) • u t) i = _
  simp [Fin.sum_univ_two]

/-- Good-set membership at curve degree `k = 1` is exactly `δ`-proximity of the scalar fold
to the Reed–Solomon code. -/
theorem mem_lineGoodCoeffs_iff {deg : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) (Fin n)) (z : F) :
    z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ ↔
      δᵣ((fun i => u 0 i + z * u 1 i), ReedSolomon.code ωs deg) ≤ δ := by
  have h : z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ ↔
      δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code ωs deg) ≤ δ := by
    simp [RS_goodCoeffsCurve]
  rw [h, curveWord_line_eq]

end Line

/-! ## The core brick: close low-degree decodings divide the specialized interpolant -/

section Core

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The S10-converse divisibility for an arbitrary close low-degree polynomial.**

Let `Q` be a `K = F(Z)`-level GS interpolant for the generic fold (the S2 `Conditions`) with
integer representative `(d, Q₀)`.  At any `z` where the specialization survives, every
polynomial `W` of degree `< deg` whose evaluations lie within the GS Johnson radius of the
scalar fold `f_z = f₀ + z·f₁` is a matching factor of the specialized interpolant:
`(Y − C W) ∣ Q₀|_{Z:=z}`.

This upgrades `scalar_fold_decoded_divides_specialization` from the `codewordToPoly` shape to
an arbitrary close polynomial via the Lagrange interpolation round-trip. -/
theorem dvd_specialization_of_close {n deg m : ℕ} (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (W : F[X]) (hWdeg : W.degree < (deg : WithBot ℕ))
    (hdist : (hammingDist (fun i => f₀ i + z * f₁ i) (fun i => W.eval (ωs i)) : ℝ) / n <
      gs_johnson deg n m) :
    (Polynomial.X - Polynomial.C W) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  -- `W` is a Reed–Solomon codeword polynomial
  have hmem : ReedSolomon.evalOnPoints ωs W ∈ ReedSolomon.code ωs deg :=
    Submodule.mem_map.mpr ⟨W, Polynomial.mem_degreeLT.mpr hWdeg, rfl⟩
  have hWn : W.natDegree < n := by
    rcases eq_or_ne W 0 with rfl | hW
    · simpa using Nat.lt_of_lt_of_le (Nat.succ_pos deg) hk
    · exact Nat.lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt hW).mpr hWdeg)
        (Nat.le_of_succ_le hk)
  -- the Lagrange round-trip: `codewordToPoly` of the evaluation codeword is `W` itself
  have hcw : ReedSolomon.codewordToPoly (⟨ReedSolomon.evalOnPoints ωs W, hmem⟩ :
      ReedSolomon.code ωs deg) = W := by
    have h := GuruswamiSudan.interpolate_eq_of_degree_lt (ωs := ωs) W hWn
    simpa [ReedSolomon.codewordToPoly, ReedSolomon.evalOnPoints] using h
  have hmain := GuruswamiSudan.OverRatFunc.scalar_fold_decoded_divides_specialization
    ωs f₀ f₁ hQ hrep z hz hk hm ⟨ReedSolomon.evalOnPoints ωs W, hmem⟩
    (by rw [hcw]; convert hdist using 3; congr!)
  rwa [hcw] at hmain

variable {n : ℕ} [NeZero n]

/-- **Good-set family form of the S10-converse divisibility.**  For an arbitrary decoding
family `W : F → F[X]` (instantiate at the decoded family `P` for `hPdvd`, and at the
lift-specialisation family `liftSpec v₀ v₁` for `hQdvd`): per-`z` non-collapse, degree, and
fold-proximity hypotheses on the good set produce the matching divisibility family. -/
theorem dvd_specialization_family {deg m : ℕ} (ωs : Fin n ↪ F) {δ : ℝ≥0}
    (u : WordStack F (Fin 2) (Fin n))
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (W : F → F[X])
    (hgood : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hWdeg : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
      (W z).degree < (deg : WithBot ℕ))
    (hWdist : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
      (hammingDist (fun i => u 0 i + z * u 1 i) (fun i => (W z).eval (ωs i)) : ℝ) / n <
        gs_johnson deg n m) :
    ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
      (Polynomial.X - Polynomial.C (W z)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  fun z hz => dvd_specialization_of_close ωs (u 0) (u 1) hQ hrep hk hm z (hgood z hz)
    (W z) (hWdeg z hz) (hWdist z hz)

end Core

/-! ## The `F[X][Y]`-level separability supply (the unit-discriminant route) -/

section Sep

variable {F : Type} [Field F]

/-- **Per-`z` `F[X][Y]`-level separability from unit discriminant data.**  `Separable` over
the non-field `F[X]` is a unit-Bézout statement; its honest discriminant route is
`Polynomial.separable_of_leadingCoeff_isUnit_of_discr_isUnit`: per-`z` *unit* leading
coefficient and *unit* discriminant of the specialized interpolant give the exact `hsep`
field of `HenselMatchingPolySupply.InterpolantInput`.

(The residue-level `PerPlaceSeparabilitySupply` route lands one ring below — `F[Y]` over the
field `F` — and feeds `HenselDatum.hderiv` directly; it can NOT supply `hsep` at the
`F[X][Y]` level, which is why the unit conditions appear here as the named inputs.) -/
theorem hsep_of_discr_isUnit (Q₀ : (F[X])[X][Y]) {S : Finset F}
    (hdeg : ∀ z ∈ S,
      0 < (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).natDegree)
    (hlc : ∀ z ∈ S,
      IsUnit (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).leadingCoeff)
    (hdiscr : ∀ z ∈ S,
      IsUnit (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).discr) :
    ∀ z ∈ S, (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable :=
  fun z hz => Polynomial.separable_of_leadingCoeff_isUnit_of_discr_isUnit
    (hdeg z hz) (hlc z hz) (hdiscr z hz)

end Sep

/-! ## The bundled S10-converse surface and the assembled producers -/

section Assembly

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The S10-converse input bundle** for the Hensel lane at curve degree `k = 1` (the line
case, where the good-set curve word IS the S10 scalar fold `u 0 + z • u 1`).

Cargo: the `K = F(Z)`-level GS interpolant for the generic fold with its `Conditions` (S2),
an integer representative `(d, Q₀)` (in-tree producible by `exists_integer_representative`),
the Johnson-regime arithmetic side conditions, and the per-good-`z` residuals: non-collapse
of the specialization, degree + fold-proximity of BOTH competitors (the decoded family `P`
and the lift specialisation `liftSpec v₀ v₁` — the symmetric GS argument applies to each),
order-0 agreement, and `F[X][Y]`-level separability (unit-discriminant route:
`hsep_of_discr_isUnit`). -/
structure GSLineInput (deg m : ℕ) (ωs : Fin n ↪ F) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) (Fin n)) (P : F → Polynomial F) (v₀ v₁ : F[X]) : Type where
  /-- the `K = F(Z)`-level GS interpolant for the generic fold. -/
  Q : (RatFunc F)[X][Y]
  /-- the common denominator of the integer representative. -/
  d : F[X]
  /-- the integer representative of the interpolant, over `F[Z][X][Y]`. -/
  Q₀ : (F[X])[X][Y]
  /-- the S2 GS `Conditions` over `K` for the generic fold `u 0 + Z·u 1`. -/
  hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
    (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
    (GuruswamiSudan.OverRatFunc.genericFold (u 0) (u 1)) Q
  /-- the integer-representative identity `Q₀ ↦ C(C d)·Q`. -/
  hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
    Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q
  /-- Johnson-regime arity: `deg + 1 ≤ n`. -/
  hk : deg + 1 ≤ n
  /-- positive multiplicity parameter. -/
  hm : 1 ≤ m
  /-- the competitor is a codeword: `2 ≤ deg`. -/
  hdeg2 : 2 ≤ deg
  /-- per-good-`z` non-collapse of the specialization (the cofinite `d(z) ≠ 0` fact). -/
  hgood : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0
  /-- the decoded family has Reed–Solomon degree. -/
  hPdeg : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (P z).degree < (deg : WithBot ℕ)
  /-- the decoded family is within the GS Johnson radius of the fold. -/
  hPdist : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => u 0 i + z * u 1 i) (fun i => (P z).eval (ωs i)) : ℝ) / n <
      gs_johnson deg n m
  /-- the lift-specialisation competitor is within the GS Johnson radius of the fold. -/
  hQdist : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => u 0 i + z * u 1 i)
        (fun i => (liftSpec v₀ v₁ z).eval (ωs i)) : ℝ) / n <
      gs_johnson deg n m
  /-- per-`z` order-0 agreement of the two competitors (the common-approximation fact). -/
  h0 : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (P z).coeff 0 = (liftSpec v₀ v₁ z).coeff 0
  /-- per-`z` `F[X][Y]`-level separability of the specialized interpolant. -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable

/-- **`InterpolantInput` from the S10-converse GS surface (the assembly).**  The per-`z`
interpolant family is the specialization family `z ↦ Q₀|_{Z:=z}`; BOTH matching
divisibilities come from the same S10-converse brick (`dvd_specialization_of_close`), at the
decoded family `P` and at the lift-specialisation competitor respectively. -/
noncomputable def GSLineInput.toInterpolantInput {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (data : GSLineInput deg m ωs δ u P v₀ v₁) :
    HenselMatchingPolySupply.InterpolantInput
      (k := 1) (deg := deg) (domain := ωs) (δ := δ) u P v₀ v₁ where
  Q := fun z => data.Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  hPdvd := fun z hz =>
    dvd_specialization_of_close ωs (u 0) (u 1) data.hQ data.hrep data.hk data.hm z
      (data.hgood z hz) (P z) (data.hPdeg z hz) (data.hPdist z hz)
  hQdvd := fun z hz =>
    dvd_specialization_of_close ωs (u 0) (u 1) data.hQ data.hrep data.hk data.hm z
      (data.hgood z hz) (liftSpec v₀ v₁ z) (liftSpec_degree_lt data.hdeg2 v₀ v₁ z)
      (data.hQdist z hz)
  h0 := data.h0
  hsep := data.hsep

/-- **`HPzBridge.HenselDatum` from the S10-converse GS surface** — the composed corollary
through `HenselMatchingPolySupply.henselDatum_of_interpolantInput`. -/
noncomputable def GSLineInput.toHenselDatum {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (data : GSLineInput deg m ωs δ u P v₀ v₁) :
    HPzBridge.HenselDatum (k := 1) (deg := deg) (domain := ωs) (δ := δ) u P v₀ v₁ :=
  HenselMatchingPolySupply.henselDatum_of_interpolantInput data.toInterpolantInput

end Assembly

end InterpolantInputSupply

/-! ## The capstone: `hPz` from the S10-converse GS surface -/

section HPz

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **`hPz` from per-representative S10-converse GS data (the capstone).**  For every linear
representative `(v₀, v₁)` consistent with `γ`, a `GSLineInput` bundle (K-level GS interpolant
+ integer representative + per-good-`z` proximity/agreement/separability residuals) plus the
degree bounds yield the full `hPz` field: the per-`z` identity
`P z = ((map C v₀) + (C X)·(map C v₁)).eval (C z)` on the good set, DERIVED by Hensel
uniqueness through `hPz_of_interpolantInput` ∘ `GSLineInput.toInterpolantInput`. -/
theorem hPz_of_gs_line {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F}
    (hInput : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      InterpolantInputSupply.GSLineInput deg m ωs δ u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < 1 + 1 ∧ v₁.natDegree < 1 + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < 1 + 1 ∧ v₁.natDegree < 1 + 1 :=
  ArkLib.hPz_of_interpolantInput (k := 1)
    (fun v₀ v₁ hlin => (hInput v₀ v₁ hlin).toInterpolantInput) hdeg

end HPz

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolantInputSupply.liftSpec
#print axioms ArkLib.InterpolantInputSupply.liftSpec_eq
#print axioms ArkLib.InterpolantInputSupply.liftSpec_natDegree_le
#print axioms ArkLib.InterpolantInputSupply.degree_lt_of_natDegree_lt
#print axioms ArkLib.InterpolantInputSupply.liftSpec_degree_lt
#print axioms ArkLib.InterpolantInputSupply.curveWord_line_eq
#print axioms ArkLib.InterpolantInputSupply.mem_lineGoodCoeffs_iff
#print axioms ArkLib.InterpolantInputSupply.dvd_specialization_of_close
#print axioms ArkLib.InterpolantInputSupply.dvd_specialization_family
#print axioms ArkLib.InterpolantInputSupply.hsep_of_discr_isUnit
#print axioms ArkLib.InterpolantInputSupply.GSLineInput
#print axioms ArkLib.InterpolantInputSupply.GSLineInput.toInterpolantInput
#print axioms ArkLib.InterpolantInputSupply.GSLineInput.toHenselDatum
#print axioms ArkLib.hPz_of_gs_line
