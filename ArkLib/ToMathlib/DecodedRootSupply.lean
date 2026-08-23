/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedProximateRoot
import ArkLib.ToMathlib.RationalRootSupply

/-!
# Issue #304 — the decoded root supply: base-point roots PRODUCED from the GS split

`DecodedProximateRoot.mpFin_of_decoded` (and its `hvanish`/truncation capstones) consume two
per-place inputs that this file **produces** from the GS structure itself:

* `root : (z : F) → rationalRoot (H_tilde' H) z` — the branch roots; and
* `hbase : ∀ z ∈ matchingSet, (w.eval (C x₀)).eval z = (root z).1` — the base-point fact.

The production chain (all from named GS facts):

1. `centreFold_dvd` — the surface factor at the centre: `(Y′ − C w) ∣ R` specializes along
   `evalX (C x₀)` to `(Y′ − C (w.eval (C x₀))) ∣ evalX (C x₀) R` (one `map_dvd` through
   `evalX_eq_map`).
2. `evalEval_evalX_eq_zero` — hence the centre fold of the surface roots the specialized
   trivariate at every curve parameter: `(evalX (C x₀) R)(z, w(x₀, z)) = 0`.
3. `rootDecoded` — through the GS split `evalX (C x₀) R = H · G` (supplied by
   `hHyp.dvd_evalX`) and per-place **branch separation** `G(z, w(x₀,z)) ≠ 0`, the value
   `w(x₀, z)` roots `H` itself, yielding the rational root with value
   `lc_H(z) · w(x₀, z)` (`RationalRootSupply.rationalRoot_of_evalEval`).
4. `rootDecoded_val_monic` — for monic `H` the value **is** `w(x₀, z)`: the base-point fact
   `hbase` holds by construction.

Capstones re-stated with `root`/`hbase` **eliminated** (replaced by the split + per-place
branch separation, both honest §5 branch-assignment content):

* `mpFin_of_decoded_roots` — the finite-range `MatchingPoint` family;
* `hvanish_of_decoded_roots` — the `SβLargeAtFin` per-point vanishing;
* `gammaGenuine_eq_trunc_of_decoded_roots` — **Claim 5.8′ from**: the surface factor
  `(Y′ − C w) ∣ R` with `w.natDegree < k`, the GS split cofactor `G` with per-place branch
  separation, per-place `ξ`-nonvanishing at the produced roots, `R.Separable`, the genuine
  representative, discriminant counting, and the graded side conditions.

After this file the truncation lane's per-place inputs are exactly: branch separation
(`G(z, w(x₀,z)) ≠ 0`) and `ξ`-nonvanishing — both certified by polynomial nonvanishing at `z`
(the `ConditionDiscProduct` discriminant lane), closing the loop with the §6 counting that the
same discriminant feeds.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (the matching surface and branch assignment), Appendix A.3/A.5.2.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

namespace DecodedRootSupply

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The centre fold of the surface factor -/

/-- **The surface factor at the centre.**  `(Y′ − C w) ∣ R` specializes along the centre
evaluation `evalX (C x₀)` to the linear factor of the centre fold. -/
theorem centreFold_dvd {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀)))
      ∣ Bivariate.evalX (Polynomial.C x₀) R := by
  rw [Bivariate.evalX_eq_map]
  have h := Polynomial.map_dvd (Polynomial.evalRingHom (Polynomial.C x₀)) hdvd
  rwa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom]
    at h

/-- The centre fold of the surface roots the specialized trivariate at every curve
parameter: `(evalX (C x₀) R)(z, w(x₀, z)) = 0`. -/
theorem evalEval_evalX_eq_zero {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F) :
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  obtain ⟨c, hc⟩ := centreFold_dvd (x₀ := x₀) hdvd
  rw [hc, Polynomial.evalEval_mul]
  have hlin : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z)
      (Polynomial.X - Polynomial.C (w.eval (Polynomial.C x₀))) = 0 := by
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_X, Polynomial.evalEval_C, sub_self]
  rw [hlin, zero_mul]

/-! ## The decoded root -/

/-- **The decoded branch root.**  Through the GS split `evalX (C x₀) R = H · G` and the
per-place branch separation `G(z, w(x₀,z)) ≠ 0`, the centre value `w(x₀, z)` roots `H`
itself; the resulting rational root carries the value `lc_H(z) · w(x₀, z)`. -/
noncomputable def rootDecoded {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hH : 0 < H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0) :
    rationalRoot (H_tilde' H) z :=
  RationalRootSupply.rationalRoot_of_evalEval hH
    (RationalRootSupply.evalEval_eq_zero_of_factor_branch hsplit
      (evalEval_evalX_eq_zero hdvd z) hbranch)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The decoded root's value, in general: `lc_H(z) · w(x₀, z)`. -/
theorem rootDecoded_val {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hH : 0 < H.natDegree)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0) :
    (rootDecoded hH hsplit hdvd z hbranch).1
      = (H.coeff H.natDegree).eval z * ((w.eval (Polynomial.C x₀)).eval z) := rfl

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The base-point fact, by construction (monic case)**: for monic `H` the decoded root's
value is exactly the surface's centre value `w(x₀, z)` — the `hbase` input of
`DecodedProximateRoot.mpFin_of_decoded` holds definitionally. -/
theorem rootDecoded_val_monic {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0) :
    ((w.eval (Polynomial.C x₀)).eval z : F) = (rootDecoded hH hsplit hdvd z hbranch).1 := by
  rw [rootDecoded_val]
  have : H.coeff H.natDegree = 1 := hlc
  rw [this, Polynomial.eval_one, one_mul]

/-! ## The capstones with the roots eliminated -/

section Family

variable [Fintype F] [DecidableEq F]

/-- **The `mpFin` family with the roots PRODUCED.**  As
`DecodedProximateRoot.mpFin_of_decoded`, with `root`/`hbase` replaced by the GS split and
per-place branch separation. -/
noncomputable def mpFin_of_decoded_roots {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G : F[X][Y]} {k : ℕ}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hR : R.Separable) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z, ∀ hz : z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z
        (rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)) :=
  fun t hkt _ z hz =>
    DecodedProximateRoot.matchingPoint_of_decoded hHyp hξ hlc z
      (rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)) (hx z hz) hdeg hdvd
      (rootDecoded_val_monic (Fact.out) hlc hsplit hdvd z (hbranch z hz)) hR t hkt

omit [Fintype F] [DecidableEq F] in
/-- **The `hvanish` capstone with the roots produced**: the per-point vanishing input of
`GenuineTruncationFin.SβLargeAtFin_of_graded_disc`, from the GS split + surface factor +
branch separation. -/
theorem hvanish_of_decoded_roots {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G : F[X][Y]} {k : ℕ}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hR : R.Separable) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt htT z hz
  refine ⟨rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz), ?_⟩
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact (mpFin_of_decoded_roots hHyp hξ hlc hsplit hdeg hdvd hbranch hR T
    hx t hkt htT z hz).pi_z_eq_zero

/-- **Claim 5.8′ with the roots produced (the sharpest composed capstone).**
`gammaGenuine = trunc k gammaGenuine` from: the GS split `evalX (C x₀) R = H · G`, the
surface factor `(Y′ − C w) ∣ R` with `w.natDegree < k`, per-place branch separation and
`ξ`-nonvanishing, `R.Separable`, the genuine representative, the §6 discriminant counting,
and the graded side conditions.  No root section and no base-point hypothesis remain — both
are constructed. -/
theorem gammaGenuine_eq_trunc_of_decoded_roots {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F} {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hR : R.Separable)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepG
    (hvanish_of_decoded_roots hHyp hξ hmonic.leadingCoeff hsplit hdeg hdvd hbranch hR
      Ppoly.natDegree hx)
    hdisc hcover hbig

end Family

end DecodedRootSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.DecodedRootSupply.centreFold_dvd
#print axioms ArkLib.DecodedRootSupply.evalEval_evalX_eq_zero
#print axioms ArkLib.DecodedRootSupply.rootDecoded
#print axioms ArkLib.DecodedRootSupply.rootDecoded_val
#print axioms ArkLib.DecodedRootSupply.rootDecoded_val_monic
#print axioms ArkLib.DecodedRootSupply.mpFin_of_decoded_roots
#print axioms ArkLib.DecodedRootSupply.hvanish_of_decoded_roots
#print axioms ArkLib.DecodedRootSupply.gammaGenuine_eq_trunc_of_decoded_roots
