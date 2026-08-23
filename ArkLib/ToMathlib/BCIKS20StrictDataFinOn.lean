/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingGeometryProducersOn
import ArkLib.ToMathlib.HcardDischarge
import ArkLib.ToMathlib.KeystoneAssembly

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace RootOn304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

/-! The On-form helper lemmas are imported from `MatchingGeometryProducersOn`
(`ArkLib.Match304.tail_zero_of_finite_card_and_degreeOn`). -/

/-! ## B. The satisfiable bundle `Section5StrictDataFinOn`

Identical to `HcardDischarge.Section5StrictDataFin` except:
* `root : (z : F) → rationalRoot (H_tilde' H) z`  ↦  `rootOn : ∀ z ∈ matchingSet, …`;
* `mpFin` is retyped at `rootOn z hz` (`mpFinOn`).
All other fields are verbatim. -/

section Bundle

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The satisfiable §5 per-decoding extraction datum** (#304): `Section5StrictDataFin` with the
unsatisfiable total root family replaced by the honest membership-dependent `rootOn`/`mpFinOn`
(finding #3: total families have empty fibres at non-split `z`; every consumption is at
matching-set members only). -/
structure Section5StrictDataFinOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- centre / curve data of [BCIKS20] §5. -/
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  /-- the **membership-dependent** rational-root family: roots are demanded only at matching-set
  members (the satisfiable form; the total family of `Section5StrictDataFin` has empty fibres at
  non-split `z`). -/
  rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z
  /-- the Lemma-A.1 truncation index: the largest tail index for which the fixed `matchingSet`
  dominates `weight(betaRec t)·d_H`. -/
  T : ℕ
  /-- ingredient-C per-point matching data over the finite counting range `k ≤ t ≤ T`, at the
  restricted roots `rootOn z hz`. -/
  mpFinOn : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz)
  /-- the L9/L10 weight bound over the finite counting range `k ≤ t ≤ T` (the satisfiable form
  of `hcard`). -/
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- the algebraic-degree datum: beyond the truncation index `T`, the Hensel-lift coefficients
  vanish for the bounded-`Z`-degree reason (Prop 5.5). -/
  htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0
  /-- validity of the BCIKS substitution `X ↦ X − x₀`. -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  /-- the Claim-5.9 substitution form of `γ` built from the genuine Hensel coefficients. -/
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  /-- the Prop-5.5 polynomial representative of `γ`. -/
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- the §5 specialisation bridge: at each good `z`, `P z` equals the linear representative at
      `Z = z` (per-point evaluation identity, NOT the per-coefficient conclusion). -/
  hPz : ∀ v₀ v₁ : F[X],
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

/-! ## C. Restriction: the total bundle yields the restricted one -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **Total ⟹ restricted.**  Any (over-strong, typically unsatisfiable) `Section5StrictDataFin`
restricts to a `Section5StrictDataFinOn` by evaluating the total root family at matching-set
members only.  The converse fails for non-fibrewise-totally-split GS factors (finding #3). -/
def Section5StrictDataFinOn.ofTotal {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := d.x₀, R := d.R, H := d.H, hIrr := d.hIrr, hPos := d.hPos, hHyp := d.hHyp,
    Bcoeff := d.Bcoeff, hH := d.hH, D := d.D, hD := d.hD, matchingSet := d.matchingSet,
    rootOn := fun z _ => d.root z, T := d.T,
    mpFinOn := fun t hkt htT z hz => d.mpFin t hkt htT z hz,
    hcardFin := d.hcardFin, htailDeg := d.htailDeg,
    hsubst := d.hsubst, hγ := d.hγ, Ppoly := d.Ppoly, hrep := d.hrep, hdegX := d.hdegX,
    hPz := d.hPz }

/-! ## D. The keystone consumption, mirrored

`HcardDischarge.curveCoeffPolys_of_section5DataFin` is the keystone consumer of
`Section5StrictDataFin`; the only root-dependent step in its proof is the α-tail vanishing
(`tail_zero_of_finite_card_and_degree`, consuming `root`/`mpFin`/`hcardFin`).  Everything
after `htail` (truncation, linear decomposition, `hPz`) and the conclusion
(`CurveCoeffPolys` on the good set) are root-free.  We re-prove it verbatim from the
restricted bundle, routing the tail through `tail_zero_of_finite_card_and_degreeOn`. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The satisfiable §5 datum yields the per-coefficient curve-polynomial datum on the good set —
same conclusion as `HcardDischarge.curveCoeffPolys_of_section5DataFin`, with the α-tail vanishing
routed through the restricted-root counting branch.  The conclusion is root-free. -/
theorem curveCoeffPolys_of_section5DataFinOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P := by
  haveI := d.hIrr
  haveI := d.hPos
  -- The repaired tail: restricted-root finite-range counting + algebraic-degree datum.
  have htail : ∀ t, k ≤ t → BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp d.Bcoeff t = 0 :=
    Match304.tail_zero_of_finite_card_and_degreeOn d.x₀ d.R d.H d.hHyp d.Bcoeff d.hH d.D d.hD k d.T
      d.mpFinOn d.hcardFin d.htailDeg
  -- Steps C–D of `curveCoeffPolys_of_betaRec`, verbatim (all root-free).
  have htrunc :
      γ d.x₀ d.R d.H d.hHyp =
        Polynomial.aeval (Claim59Conditional.shiftSeries d.x₀ d.H)
          (PowerSeries.trunc k
            (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta d.x₀ d.R d.H d.hHyp d.Bcoeff))) := by
    rw [d.hγ]
    exact subst_mk_eq_aeval_trunc_of_tail_zero d.hsubst htail
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one d.hdegX
  have hlin :
      γ d.x₀ d.R d.H d.hHyp = polyToPowerSeries𝕃 d.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
    rw [← d.hrep, hPpoly]
  obtain ⟨hPeval, hd₀, hd₁⟩ := d.hPz v₀ v₁ hlin
  exact BetaToCurveCoeffPolys.curveCoeffPolys_of_linear_representative v₀ v₁ hd₀ hd₁ hPeval

omit [Nonempty ι] [DecidableEq ι] in
/-- The satisfiable §5 datum yields the bundled `hcoeffPoly` existential the front door consumes —
same conclusion as `HcardDischarge.hcoeffPoly_witness_of_section5DataFin` (root-free). -/
theorem hcoeffPoly_witness_of_section5DataFinOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_section5DataFinOn d)

omit [Nonempty ι] [DecidableEq ι] in
/-- Consistency check: composing the restriction with the restricted consumer recovers the
original consumer's conclusion from the total bundle. -/
theorem curveCoeffPolys_of_section5DataFin_via_ofTotal {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
  curveCoeffPolys_of_section5DataFinOn (Section5StrictDataFinOn.ofTotal d)

/-! ## E. The KeystoneAssembly front doors from the restricted bundle

`KeystoneAssembly.correlatedAgreement_listDecoding_closed_fin` / `…_strict_fin` consume
`Section5StrictDataFin` only through `hcoeffPoly_witness_of_section5DataFin`; we mirror them
with `Section5StrictDataFinOn`-valued producers.  Conclusions are identical (root-free). -/

omit [DecidableEq ι] in
/-- Mirror of `KeystoneAssembly.correlatedAgreement_listDecoding_closed_fin` with the satisfiable
restricted-root bundle as the per-decoding extraction datum. -/
theorem correlatedAgreement_listDecoding_closed_finOn {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hExtractFinOn : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataFinOn (hExtractFinOn u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- Mirror of `KeystoneAssembly.correlatedAgreement_listDecoding_strict_fin` with the satisfiable
restricted-root bundle. -/
theorem correlatedAgreement_listDecoding_strict_finOn {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hExtractFinOn : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro hk u hprob hJ P hP
  exact hcoeffPoly_witness_of_section5DataFinOn (hExtractFinOn u hprob hJ P hP)

end Bundle

/-! ## Axiom audit -/

#print axioms ArkLib.RootOn304.Section5StrictDataFinOn
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.mk
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofTotal
#print axioms ArkLib.RootOn304.curveCoeffPolys_of_section5DataFinOn
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_section5DataFinOn
#print axioms ArkLib.RootOn304.curveCoeffPolys_of_section5DataFin_via_ofTotal
#print axioms ArkLib.RootOn304.correlatedAgreement_listDecoding_closed_finOn
#print axioms ArkLib.RootOn304.correlatedAgreement_listDecoding_strict_finOn

end RootOn304

end ArkLib
