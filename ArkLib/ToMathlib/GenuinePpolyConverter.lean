/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GenuineTruncationFin
import ArkLib.ToMathlib.ZLinearClosureAudit
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5GenuineZLinearQuadratic

/-!
# Issue #304 — F6: the genuine Prop-5.5 representative `hrepG` is UNSATISFIABLE for `d_H ≥ 2`,
and the corrected T-aware representative + converter

## FINDING F6 (the representative check — PROVEN refutation)

The genuine-monic bundles (`GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic`,
field `hrep`; `HvanishSupply.gammaGenuine_eq_trunc_of_localSeries[_dvd_sep]` and
`GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc`, hypothesis `hrepG`) all consume

  `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp`  with `Ppoly : F[X][Y]`.

But `polyToPowerSeries𝕃 H Ppoly = PowerSeries.mk (fun n => liftToFunctionField (Ppoly.coeff n))`
(`RationalFunctionsCore`, `coeff_polyToPowerSeries𝕃`), and `liftToFunctionField` embeds `F[X]` as
the **ground `F[Z]`-line** of `𝕃 H` (`coeffAsRatFunc c = C (univPolyHom c)` — constant in the
adjoined branch variable `T`).  Meanwhile `coeff 0 (gammaGenuine …) = α₀ = T/W`
(`gammaGenuine_constantCoeff`), which is **off** the ground line for every curve with `d_H ≥ 2`
(`ZLinearClosureAudit.α₀_ne_lift`).  Hence `hrepG` is unsatisfiable for `2 ≤ H.natDegree`
(`not_hrepG_of_two_le_natDegree` / `hrepG_unsat_of_two_le_natDegree` below): **no** `Ppoly` can
ever instantiate the `hrep`/`hrepG` fields of those producers/capstones at any curve of interest
(in particular at the in-tree monic-quadratic witnesses, `d_H = 2`).  This is the fourth
F-series statement-level finding on the #304 surface (after the three refuted statement bugs of
the faithful-surface audit): the consumers are not wrong, but their representative-shaped input
is empty for `d_H ≥ 2`, so the capstones gated on it are vacuous there.

`d_H = 1` is genuinely excluded from the refutation: there `T` itself is on the ground line
(`H = W·Y − c` makes `T/W` rational), and `hrepG` can hold.

## The corrected representative shape (minimal T-aware lift)

Claim 5.9 (T-form), where it is PROVEN (monic `d_H ≤ 2`,
`claim59_zLinear_of_monic_natDegree_le_two`), produces per coefficient exactly
`αGenuine t = lift c₀ + T·lift c₁`.  The minimal polynomial representative compatible with that
output is therefore a **pair** `P₀ P₁ : F[X][Y]` with

  `polyToPowerSeries𝕃T H P₀ P₁ := PowerSeries.mk fun t =>`
  `    liftToFunctionField (P₀.coeff t) + functionFieldT * liftToFunctionField (P₁.coeff t)`,

i.e. coefficients are `liftBivariate`-images of the Z-affine representatives
`C (P₀.coeff t) + Y·C (P₁.coeff t)` (`polyToPowerSeries𝕃T_eq_mk_liftBivariate`); the old shape is
the degenerate `P₁ = 0` slice (`polyToPowerSeries𝕃T_zero_right`), which F6 shows is unusable at
`d_H ≥ 2` — indeed any corrected representative of `gammaGenuine` is genuinely T-loaded already
at order `0` (`corrected_rep_T_loaded`).

## The converter and the surviving capstone

* `exists_corrected_representative_of_T_form_of_trunc` — **the converter**: per-coefficient
  T-form (exactly Claim 5.9's output shape) + the truncation identity `γ = trunc k γ` produce a
  corrected representative with coefficient support in `[0, k)`.
* `exists_corrected_representative_of_monic_natDegree_le_two` — the converter instantiated with
  the proven monic-quadratic Claim 5.9 closure: for monic `d_H ≤ 2`, the truncation identity
  ALONE yields the corrected representative.
* `htailDeg_genuine_of_corrected_representative` — the adapter: the algebraic tail datum
  (`αGenuine t = 0` past `max (deg P₀) (deg P₁)`) from the corrected representative — the
  corrected-rep version of `GenuineTruncationFin.htailDeg_genuine_of_representative`.
* `gammaGenuine_eq_trunc_of_graded_disc_corrected` — the truncation capstone of
  `GenuineTruncationFin` re-assembled on the corrected representative: same finite geometric
  inputs, `hrepG` replaced by the **satisfiable** `hrepT`.

## Honest residuals

* The converter consumes the truncation identity `γ = trunc k γ`; the corrected capstone here
  derives that identity from the corrected representative + finite geometric data.  Producing a
  corrected representative *ab initio* (without an already-known truncation) for `d_H = 2` needs
  the finite coefficient support to come from somewhere — that is precisely the Claim 5.8
  counting content, unchanged by this file.
* The corrected analogue of the old `hdegX : degreeX Ppoly ≤ 1` companion (the Prop-5.5 ground
  `Z`-degree budget, i.e. `degreeX P₀/P₁` bounds) is NOT produced by the converter:
  `claim59_zLinear_of_monic_natDegree_le_two` gives no degree bounds on `c₀ c₁` — that is the
  open #138 X-degree budget, isolated and untouched here.
* For monic `d_H ≥ 3` the per-coefficient T-form itself is open (span dichotomy,
  `ZLinearClosureAudit` FINDING 4); for non-unit leading coefficient it is false.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5.2.7 (Claim 5.9), Prop. 5.5, Appendix A.4.
-/

set_option linter.style.longLine false

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace GenuinePpolyConverter

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Part 1 — FINDING F6: the genuine Prop-5.5 representative is unsatisfiable for `d_H ≥ 2` -/

/-- **FINDING F6 (refutation).**  For every curve `H` with `d_H ≥ 2`, NO bivariate polynomial
`Ppoly : F[X][Y]` represents the genuine Hensel root through `polyToPowerSeries𝕃`: the order-`0`
coefficient of `polyToPowerSeries𝕃 H Ppoly` is `liftToFunctionField (Ppoly.coeff 0)` — on the
ground `F[Z]`-line — while `coeff 0 (gammaGenuine …) = α₀ = T/W` is off it
(`ZLinearClosureAudit.α₀_ne_lift`).  Consequently the `hrep`/`hrepG` fields of
`GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic`,
`HvanishSupply.gammaGenuine_eq_trunc_of_localSeries[_dvd_sep]` and
`GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc` can never be instantiated at
`d_H ≥ 2`. -/
theorem not_hrepG_of_two_le_natDegree (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) (Ppoly : F[X][Y]) :
    polyToPowerSeries𝕃 H Ppoly ≠ gammaGenuine x₀ R H hHyp := by
  intro h
  have h0 : liftToFunctionField (H := H) (Ppoly.coeff 0) = α₀ H := by
    have hc := congrArg (fun s : PowerSeries (𝕃 H) => PowerSeries.coeff 0 s) h
    simpa only [coeff_polyToPowerSeries𝕃, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      gammaGenuine_constantCoeff hHyp] using hc
  exact BCIKS20.ZLinearClosureAudit.α₀_ne_lift H hdeg (Ppoly.coeff 0) h0.symm

/-- **FINDING F6 (existential form).**  The representative-shaped input consumed by the
genuine-monic bundles is EMPTY for `d_H ≥ 2`. -/
theorem hrepG_unsat_of_two_le_natDegree (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ¬ ∃ Ppoly : F[X][Y], polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp :=
  fun ⟨Ppoly, h⟩ => not_hrepG_of_two_le_natDegree H hdeg hHyp Ppoly h

/-! ## Part 2 — the corrected (minimal, T-aware) representative shape -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The corrected representative lift.**  A pair `P₀ P₁ : F[X][Y]` represents the power series
whose `t`-th coefficient is the T-affine element
`lift (P₀.coeff t) + T · lift (P₁.coeff t)` of `𝕃 H` — exactly the per-coefficient output shape
of Claim 5.9 (T-form).  The legacy `polyToPowerSeries𝕃` is the `P₁ = 0` slice. -/
noncomputable def polyToPowerSeries𝕃T (H : F[X][Y]) (P₀ P₁ : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    liftToFunctionField (H := H) (P₀.coeff t)
      + functionFieldT (H := H) * liftToFunctionField (H := H) (P₁.coeff t)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
@[simp]
theorem coeff_polyToPowerSeries𝕃T (P₀ P₁ : F[X][Y]) (t : ℕ) :
    PowerSeries.coeff t (polyToPowerSeries𝕃T H P₀ P₁)
      = liftToFunctionField (H := H) (P₀.coeff t)
        + functionFieldT (H := H) * liftToFunctionField (H := H) (P₁.coeff t) :=
  PowerSeries.coeff_mk t _

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The legacy representative is the degenerate `P₁ = 0` slice of the corrected one. -/
theorem polyToPowerSeries𝕃T_zero_right (P₀ : F[X][Y]) :
    polyToPowerSeries𝕃T H P₀ 0 = polyToPowerSeries𝕃 H P₀ := by
  ext t
  rw [coeff_polyToPowerSeries𝕃T, coeff_polyToPowerSeries𝕃, Polynomial.coeff_zero, map_zero,
    mul_zero, add_zero]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The corrected representative's coefficients are `liftBivariate`-images of the Z-affine
canonical representatives `C (P₀.coeff t) + Y · C (P₁.coeff t)` — the shape requested by the
corrected Prop-5.5 reading. -/
theorem polyToPowerSeries𝕃T_eq_mk_liftBivariate (P₀ P₁ : F[X][Y]) :
    polyToPowerSeries𝕃T H P₀ P₁
      = PowerSeries.mk fun t => liftBivariate (H := H)
          (Polynomial.C (P₀.coeff t) + Polynomial.X * Polynomial.C (P₁.coeff t)) := by
  ext t
  rw [coeff_polyToPowerSeries𝕃T, PowerSeries.coeff_mk, map_add, map_mul, liftBivariate_C,
    liftBivariate_C, liftBivariate_X]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Series-level reading of the corrected representative: it is
`polyToPowerSeries𝕃 P₀ + C(T) · polyToPowerSeries𝕃 P₁`, matching the
`gammaGenuine_Z_linear_target` decomposition `γ = v₀ + C(T)·v₁`. -/
theorem polyToPowerSeries𝕃T_eq_add_C_mul (P₀ P₁ : F[X][Y]) :
    polyToPowerSeries𝕃T H P₀ P₁
      = polyToPowerSeries𝕃 H P₀
        + PowerSeries.C (functionFieldT (H := H)) * polyToPowerSeries𝕃 H P₁ := by
  ext t
  rw [map_add, PowerSeries.coeff_C_mul, coeff_polyToPowerSeries𝕃T, coeff_polyToPowerSeries𝕃,
    coeff_polyToPowerSeries𝕃]

/-- **T-loading.**  Any corrected representative of `gammaGenuine` at `d_H ≥ 2` is genuinely
T-loaded already at order `0`: the `P₁`-part cannot vanish there (else F6 reappears).  The
corrected shape is therefore not just sufficient but necessary-in-kind. -/
theorem corrected_rep_T_loaded (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} {hHyp : ClaimA2.Hypotheses x₀ R H} {P₀ P₁ : F[X][Y]}
    (hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp) :
    liftToFunctionField (H := H) (P₁.coeff 0) ≠ 0 := by
  intro hzero
  have h0 : liftToFunctionField (H := H) (P₀.coeff 0)
      + functionFieldT (H := H) * liftToFunctionField (H := H) (P₁.coeff 0) = α₀ H := by
    have hc := congrArg (fun s : PowerSeries (𝕃 H) => PowerSeries.coeff 0 s) hrepT
    simpa only [coeff_polyToPowerSeries𝕃T, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      gammaGenuine_constantCoeff hHyp] using hc
  rw [hzero, mul_zero, add_zero] at h0
  exact BCIKS20.ZLinearClosureAudit.α₀_ne_lift H hdeg (P₀.coeff 0) h0.symm

/-! ## Part 3 — the converter: per-coefficient T-form + truncation ⟹ corrected representative -/

/-- **The converter.**  From the per-coefficient T-form (exactly the output shape of Claim 5.9,
e.g. `claim59_zLinear_of_monic_natDegree_le_two`) together with the truncation identity
`γ = trunc k γ` (Claim 5.8′), a corrected representative `(P₀, P₁)` with coefficient support in
`[0, k)` exists: take `P_i := trunc k (mk c_i)` on chosen per-coefficient witnesses.  NOTE: no
`degreeX` bound on `P₀`/`P₁` is claimed — the ground Z-degree budget is the open #138 residual. -/
theorem exists_corrected_representative_of_T_form_of_trunc
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hT : ∀ t, ∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
    {k : ℕ}
    (htrunc : gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H))) :
    ∃ P₀ P₁ : F[X][Y], polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp
      ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0) := by
  classical
  choose c₀ c₁ hc using hT
  refine ⟨PowerSeries.trunc k (PowerSeries.mk c₀), PowerSeries.trunc k (PowerSeries.mk c₁),
    ?_, ?_, ?_⟩
  · ext t
    rw [coeff_polyToPowerSeries𝕃T, PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    by_cases ht : t < k
    · rw [if_pos ht, if_pos ht, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        show PowerSeries.coeff t (gammaGenuine x₀ R H hHyp) = αGenuine H x₀ R hHyp t from rfl]
      exact (hc t).symm
    · rw [if_neg ht, if_neg ht, map_zero, mul_zero, add_zero]
      conv_rhs => rw [htrunc]
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg ht]
  · intro t ht
    rw [PowerSeries.coeff_trunc, if_neg (not_lt.mpr ht)]
  · intro t ht
    rw [PowerSeries.coeff_trunc, if_neg (not_lt.mpr ht)]

/-- **The converter, instantiated with the PROVEN monic-quadratic Claim 5.9 closure.**  For monic
`H` with `d_H ≤ 2`, the truncation identity ALONE produces a corrected representative — the
per-coefficient T-form is unconditional there
(`claim59_zLinear_of_monic_natDegree_le_two`). -/
theorem exists_corrected_representative_of_monic_natDegree_le_two
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) {k : ℕ}
    (htrunc : gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H))) :
    ∃ P₀ P₁ : F[X][Y], polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp
      ∧ (∀ t, k ≤ t → P₀.coeff t = 0) ∧ (∀ t, k ≤ t → P₁.coeff t = 0) :=
  exists_corrected_representative_of_T_form_of_trunc H hHyp
    (fun t => claim59_zLinear_of_monic_natDegree_le_two H hHyp
      (Fact.out (p := 0 < H.natDegree)) hlc hd2 t) htrunc

/-! ## Part 4 — the adapter: the algebraic tail datum from the corrected representative -/

/-- **The corrected `htailDeg` producer** (the corrected-rep version of
`GenuineTruncationFin.htailDeg_genuine_of_representative`).  From the corrected representative
alone, the genuine Hensel coefficients vanish past `max (deg P₀) (deg P₁)` — pure coefficient
reading. -/
theorem htailDeg_genuine_of_corrected_representative
    {x₀ : F} {R : F[X][X][Y]} {hHyp : ClaimA2.Hypotheses x₀ R H} {P₀ P₁ : F[X][Y]}
    (hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp) :
    ∀ t, max P₀.natDegree P₁.natDegree < t → αGenuine H x₀ R hHyp t = 0 := by
  intro t ht
  have hα : αGenuine H x₀ R hHyp t
      = PowerSeries.coeff t (polyToPowerSeries𝕃T H P₀ P₁) := by
    rw [hrepT]; rfl
  rw [hα, coeff_polyToPowerSeries𝕃T,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_left _ _) ht),
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_max_right _ _) ht),
    map_zero, mul_zero, add_zero]

/-! ## Part 5 — the surviving truncation capstone on the corrected representative -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The truncation capstone, repaired.**  `gammaGenuine = trunc k gammaGenuine` from the SAME
finite geometric data as `GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc`, with the
F6-unsatisfiable `hrepG` replaced by the corrected representative `hrepT` (satisfiable at
`d_H = 2` by Part 3) and the tail index `Ppoly.natDegree` replaced by
`max (deg P₀) (deg P₁)`. -/
theorem gammaGenuine_eq_trunc_of_graded_disc_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ max P₀.natDegree P₁.natDegree → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.claim58prime_genuine_fin_of_monic H hHyp hmonic.leadingCoeff
    (GenuineTruncationFin.SβLargeAtFin_of_graded_disc H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hR
      hvanish hdisc hcover hbig)
    (htailDeg_genuine_of_corrected_representative H hrepT)

end Capstone

end GenuinePpolyConverter

end ArkLib

end

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GenuinePpolyConverter.not_hrepG_of_two_le_natDegree
#print axioms ArkLib.GenuinePpolyConverter.hrepG_unsat_of_two_le_natDegree
#print axioms ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T
#print axioms ArkLib.GenuinePpolyConverter.coeff_polyToPowerSeries𝕃T
#print axioms ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T_zero_right
#print axioms ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T_eq_mk_liftBivariate
#print axioms ArkLib.GenuinePpolyConverter.polyToPowerSeries𝕃T_eq_add_C_mul
#print axioms ArkLib.GenuinePpolyConverter.corrected_rep_T_loaded
#print axioms ArkLib.GenuinePpolyConverter.exists_corrected_representative_of_T_form_of_trunc
#print axioms ArkLib.GenuinePpolyConverter.exists_corrected_representative_of_monic_natDegree_le_two
#print axioms ArkLib.GenuinePpolyConverter.htailDeg_genuine_of_corrected_representative
#print axioms ArkLib.GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected
