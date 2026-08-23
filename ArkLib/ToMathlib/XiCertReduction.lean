/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedCapstonesCorrected
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

/-!
# Issue #304 — the `ξ`-certificate nonvanishing REDUCED TO (and CLOSED FROM) structural GS facts

`BranchCertificates.gammaGenuine_eq_trunc_global` (and its F6-corrected restatement
`DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected`) carried the hypothesis

  `hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (C x₀)) ≠ 0`

— global nonvanishing of the `ξ`-regularity certificate along the decoded surface.  This file
**eliminates it**: for monic `H` the certificate is *provably a unit* (a nonzero constant of
`F[X]`), from the structural GS facts already present in the capstone hypothesis list.

## The closure chain (everything global, no per-place input)

Write `Q := evalX (C x₀) R` and `v := w.eval (C x₀)` (the centre fold).

1. `ξ_pre = ∂_Y Q` for monic `H` (`ξ_pre_eq_of_monic` + `evalX_derivative_comm`), and
   `H̃' = H` (`H_tilde'_eq_self_of_monic`); hence the certificate's bivariate is the
   **monic remainder** `canonicalRepOf𝒪 (ξ) = ∂_Y Q %ₘ H` (`canonicalRepOf𝒪_mk`).
2. The surface factor `(Y′ − C w) ∣ R` makes the centre fold a *global* root of `Q`:
   `Q.eval v = 0` (`evalX_eval_centreFold_eq_zero`, via `DecodedRootSupply.centreFold_dvd`);
   branch separation `G.eval v ≠ 0` then forces `H.eval v = 0` through the GS split `Q = H·G`
   (`H_eval_centreFold_eq_zero`).
3. Evaluating `∂_Y Q = H·(∂_Y Q /ₘ H) + (∂_Y Q %ₘ H)` along `Y = v` kills the `H` term, so the
   certificate **equals the derivative reading** `(∂_Y Q).eval v`
   (`xiCert_eq_derivativeCert`).
4. Separability `hHyp.separable_evalX : IsCoprime Q (∂_Y Q)` maps along `eval v` to
   `IsCoprime 0 ((∂_Y Q).eval v)`, i.e. `(∂_Y Q).eval v` is a **unit** of `F[X]`
   (`derivative_eval_centreFold_isUnit`).  Hence `hxi` holds (`xiCert_ne_zero`) and the
   certificate even has `natDegree = 0` (`xiCert_natDegree_eq_zero`).

## Consequences

* `gammaGenuine_eq_trunc_global_xiFree` / `gammaGenuine_eq_trunc_global_corrected_xiFree` —
  the two global capstones **without `hxi` and without `hξ`** (`ξ ≠ 0` also follows, from
  `embeddingOf𝒪Into𝕃_ξ_ne_zero`), and with the field-size inequality `hbig` *sharpened*: the
  `ξ`-certificate contributes zero degree, so only `(G.eval v).natDegree` remains.

* The witness-level reductions requested by the lane are also landed for arbitrary `a : 𝒪 H`
  (they are strictly weaker than the closure but document the reverse direction of
  `BranchCertificates.xiCert_eval_monic`):
  `cert_ne_zero_of_witness` (one nonzero value suffices), `xiCert_ne_zero_of_place` (one
  branch-separated place with `π_z a ≠ 0` suffices), `cert_eq_zero_iff_dvd` (identical
  vanishing ⟺ the branch `(Y − C v)` divides the representative), and the composition degree
  bounds `natDegree_eval_le` / `cert_natDegree_le` for the `hbig` accounting.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6, Appendix A.3–A.5 (the `ξ`-regularity along the decoded surface; here closed
  by the same separability that drives the Hensel lift).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace XiCertReduction

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Witness-level reductions (arbitrary `a : 𝒪 H`) -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **One nonzero value witnesses the certificate**: a polynomial of `F[X]` with a nonzero
evaluation is nonzero. -/
theorem cert_ne_zero_of_witness (hH : 0 < H.natDegree) (a : 𝒪 H) (v : F[X])
    (hwit : ∃ z : F, (((canonicalRepOf𝒪 hH a).eval v).eval z : F) ≠ 0) :
    (canonicalRepOf𝒪 hH a).eval v ≠ 0 := by
  obtain ⟨z, hz⟩ := hwit
  exact fun h0 => hz (by rw [h0, Polynomial.eval_zero])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Identical vanishing of the certificate is branch containment**: the certificate of
`a : 𝒪 H` along `v` vanishes identically iff the branch `(Y − C v)` divides the canonical
representative of `a`. -/
theorem cert_eq_zero_iff_dvd (hH : 0 < H.natDegree) (a : 𝒪 H) (v : F[X]) :
    (canonicalRepOf𝒪 hH a).eval v = 0 ↔
      (Polynomial.X - Polynomial.C v) ∣ canonicalRepOf𝒪 hH a :=
  (Polynomial.dvd_iff_isRoot).symm

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **One branch-separated place with nonzero `π_z`-reading witnesses the certificate**
(the REVERSE direction of `BranchCertificates.xiCert_eval_monic`): if at a single place `z`
with branch separation the reading `π_z a` at the decoded root is nonzero, the global
certificate of `a` is nonzero. -/
theorem xiCert_ne_zero_of_place {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (a : 𝒪 H)
    (hpi : (π_z z (DecodedRootSupply.rootDecoded hH hsplit hdvd z hbranch)) a ≠ 0) :
    (canonicalRepOf𝒪 hH a).eval (w.eval (Polynomial.C x₀)) ≠ 0 := by
  intro h0
  apply hpi
  rw [BranchCertificates.xiCert_eval_monic hH hlc hsplit hdvd z hbranch a, h0,
    Polynomial.eval_zero]

/-! ## The structural sources -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The centre fold is a global root of the specialized trivariate**:
`(evalX (C x₀) R).eval (w.eval (C x₀)) = 0`, from the surface factor `(Y′ − C w) ∣ R`. -/
theorem evalX_eval_centreFold_eq_zero {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Bivariate.evalX (Polynomial.C x₀) R).eval (w.eval (Polynomial.C x₀)) = 0 :=
  Polynomial.dvd_iff_isRoot.mp (DecodedRootSupply.centreFold_dvd hdvd)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The centre fold globally roots `H`**: through the GS split `evalX (C x₀) R = H·G` and
the global branch separation `G.eval v ≠ 0`, the centre fold `v` is a root of `H` itself. -/
theorem H_eval_centreFold_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    H.eval (w.eval (Polynomial.C x₀)) = 0 := by
  have h0 : H.eval (w.eval (Polynomial.C x₀)) * G.eval (w.eval (Polynomial.C x₀)) = 0 := by
    rw [← Polynomial.eval_mul, ← hsplit]
    exact evalX_eval_centreFold_eq_zero hdvd
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hbr

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Separability makes the derivative reading along the surface a UNIT**:
`IsCoprime Q (∂_Y Q)` evaluated along `Y = v` with `Q.eval v = 0` exhibits
`(∂_Y Q).eval v` as a unit of `F[X]` (a nonzero constant). -/
theorem derivative_eval_centreFold_isUnit {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    IsUnit (((Bivariate.evalX (Polynomial.C x₀) R).derivative).eval
      (w.eval (Polynomial.C x₀))) := by
  rw [Polynomial.separable_def] at hsep
  have hmap := hsep.map (Polynomial.evalRingHom (w.eval (Polynomial.C x₀)))
  simp only [Polynomial.coe_evalRingHom] at hmap
  rw [show Polynomial.eval (w.eval (Polynomial.C x₀)) (Bivariate.evalX (Polynomial.C x₀) R)
      = 0 from evalX_eval_centreFold_eq_zero hdvd] at hmap
  exact isCoprime_zero_left.mp hmap

/-! ## The closure: the `ξ`-certificate IS the derivative reading, hence a unit -/

/-- **The value identity (monic)**: the `ξ`-certificate equals the derivative reading along
the surface, `(canonicalRepOf𝒪 ξ).eval v = (∂_Y (evalX (C x₀) R)).eval v`.  The `%ₘ H`
remainder shift is killed by `H.eval v = 0`. -/
theorem xiCert_eq_derivativeCert {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
      = ((Bivariate.evalX (Polynomial.C x₀) R).derivative).eval
          (w.eval (Polynomial.C x₀)) := by
  -- the certificate's bivariate is the monic remainder `∂_Y Q %ₘ H`
  have hrep : canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)
      = (Bivariate.evalX (Polynomial.C x₀) R).derivative %ₘ H := by
    have hrfl : ξ x₀ R H hHyp
        = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξ_pre x₀ R H) := rfl
    rw [hrfl, canonicalRepOf𝒪_mk hH,
      BCIKS20.HenselNumerator.ξ_pre_eq_of_monic H x₀ R hlc,
      evalX_derivative_comm x₀ R,
      BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic H hlc]
  -- evaluate the division identity along `Y = v`; the `H` term dies
  have hHv : H.eval (w.eval (Polynomial.C x₀)) = 0 :=
    H_eval_centreFold_eq_zero hsplit hdvd hbr
  have hdm := Polynomial.modByMonic_add_div
    ((Bivariate.evalX (Polynomial.C x₀) R).derivative) H
  have hev := congrArg (Polynomial.eval (w.eval (Polynomial.C x₀))) hdm
  rw [Polynomial.eval_add, Polynomial.eval_mul, hHv, zero_mul, add_zero] at hev
  rw [hrep]
  exact hev

/-- **The `ξ`-certificate is a UNIT** (monic): the structural GS facts force the certificate
to be a nonzero constant of `F[X]`. -/
theorem xiCert_isUnit {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    IsUnit ((canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))) := by
  rw [xiCert_eq_derivativeCert hHyp hH hlc hsplit hdvd hbr]
  exact derivative_eval_centreFold_isUnit hHyp.separable_evalX hdvd

/-- **THE CLOSURE: `hxi` holds.**  The `ξ`-certificate nonvanishing of
`BranchCertificates.gammaGenuine_eq_trunc_global` follows from the structural GS facts
already in its hypothesis list: the GS split, the surface factor, the branch certificate, and
separability (inside `hHyp`).  No witness place, no extra hypothesis. -/
theorem xiCert_ne_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0 :=
  (xiCert_isUnit hHyp hH hlc hsplit hdvd hbr).ne_zero

/-- The `ξ`-certificate has degree zero: it contributes nothing to the `hbig` budget. -/
theorem xiCert_natDegree_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    ((canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))).natDegree = 0 :=
  Polynomial.natDegree_eq_zero_of_isUnit (xiCert_isUnit hHyp hH hlc hsplit hdvd hbr)

/-- **`ξ ≠ 0` holds unconditionally** (from `embeddingOf𝒪Into𝕃_ξ_ne_zero`): the `hξ`
hypothesis of the truncation capstones is also redundant. -/
theorem xi_ne_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) :
    ξ x₀ R H hHyp ≠ 0 := fun h0 =>
  BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp (by rw [h0, map_zero])

/-! ## Composition degree bounds (the `hbig` accounting) -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The composition degree bound**: substituting `v : F[X]` for the `Y` variable of a
bivariate `p` gives `natDegree (p.eval v) ≤ degreeX p + natDegreeY p · natDegree v`. -/
theorem natDegree_eval_le (p : F[X][Y]) (v : F[X]) :
    (p.eval v).natDegree ≤ Bivariate.degreeX p + p.natDegree * v.natDegree := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (p.coeff i).natDegree ≤ Bivariate.degreeX p :=
    Bivariate.coeff_natDegree_le_degreeX p i
  have h2 : (v ^ i).natDegree ≤ i * v.natDegree := Polynomial.natDegree_pow_le
  have h3 : i ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
  have h4 : i * v.natDegree ≤ p.natDegree * v.natDegree := Nat.mul_le_mul_right _ h3
  omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The certificate degree bound for arbitrary `a : 𝒪 H`: the `Y`-degree of the canonical
representative is capped by `deg H̃'`. -/
theorem cert_natDegree_le (hH : 0 < H.natDegree) (a : 𝒪 H) (v : F[X]) :
    ((canonicalRepOf𝒪 hH a).eval v).natDegree
      ≤ Bivariate.degreeX (canonicalRepOf𝒪 hH a) + (H_tilde' H).natDegree * v.natDegree := by
  refine (natDegree_eval_le _ _).trans ?_
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (canonicalRepOf𝒪_natDegree_le hH a)) _

/-! ## The capstones without `hxi` and without `hξ` -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **Claim 5.8′ from purely structural global data (legacy representative)**:
`BranchCertificates.gammaGenuine_eq_trunc_global` with `hxi` and `hξ` ELIMINATED (both are
now theorems) and `hbig` sharpened (the `ξ`-certificate contributes zero degree). -/
theorem gammaGenuine_eq_trunc_global_xiFree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + (G.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) := by
  have hxi := xiCert_ne_zero hHyp hH hmonic.leadingCoeff hsplit hdvd hbr
  have hmul : ((G.eval (w.eval (Polynomial.C x₀)))
      * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))).natDegree
      = (G.eval (w.eval (Polynomial.C x₀))).natDegree := by
    rw [Polynomial.natDegree_mul hbr hxi,
      xiCert_natDegree_eq_zero hHyp hH hmonic.leadingCoeff hsplit hdvd hbr, Nat.add_zero]
  exact BranchCertificates.gammaGenuine_eq_trunc_global hHyp (xi_ne_zero x₀ R hHyp) hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hrepG hsplit hdeg hdvd hR hbr hxi
    (by rw [hmul]; exact hbig)

/-- **Claim 5.8′ from purely structural global data (F6-corrected representative)**:
`DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected` with `hxi` and `hξ`
ELIMINATED and `hbig` sharpened. -/
theorem gammaGenuine_eq_trunc_global_corrected_xiFree {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (G.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  have hxi := xiCert_ne_zero hHyp hH hmonic.leadingCoeff hsplit hdvd hbr
  have hmul : ((G.eval (w.eval (Polynomial.C x₀)))
      * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))).natDegree
      = (G.eval (w.eval (Polynomial.C x₀))).natDegree := by
    rw [Polynomial.natDegree_mul hbr hxi,
      xiCert_natDegree_eq_zero hHyp hH hmonic.leadingCoeff hsplit hdvd hbr, Nat.add_zero]
  exact DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected hHyp
    (xi_ne_zero x₀ R hHyp) hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepT hsplit hdeg hdvd hR
    hbr hxi (by rw [hmul]; exact hbig)

end Capstone

end XiCertReduction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.XiCertReduction.cert_ne_zero_of_witness
#print axioms ArkLib.XiCertReduction.cert_eq_zero_iff_dvd
#print axioms ArkLib.XiCertReduction.xiCert_ne_zero_of_place
#print axioms ArkLib.XiCertReduction.evalX_eval_centreFold_eq_zero
#print axioms ArkLib.XiCertReduction.H_eval_centreFold_eq_zero
#print axioms ArkLib.XiCertReduction.derivative_eval_centreFold_isUnit
#print axioms ArkLib.XiCertReduction.xiCert_eq_derivativeCert
#print axioms ArkLib.XiCertReduction.xiCert_isUnit
#print axioms ArkLib.XiCertReduction.xiCert_ne_zero
#print axioms ArkLib.XiCertReduction.xiCert_natDegree_eq_zero
#print axioms ArkLib.XiCertReduction.xi_ne_zero
#print axioms ArkLib.XiCertReduction.natDegree_eval_le
#print axioms ArkLib.XiCertReduction.cert_natDegree_le
#print axioms ArkLib.XiCertReduction.gammaGenuine_eq_trunc_global_xiFree
#print axioms ArkLib.XiCertReduction.gammaGenuine_eq_trunc_global_corrected_xiFree
