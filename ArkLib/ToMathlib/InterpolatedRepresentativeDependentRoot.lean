/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.InterpolatedRepresentativeSliced
import ArkLib.ToMathlib.RationalRootSupply
import ArkLib.ToMathlib.XiAtIncidenceSupply

/-!
# Issue #304 — the dependent-root packager: `double_assignment` meets the sliced apex

**The satisfiability defect fixed here.**  The interpolation capstones
(`hrep_of_cleared_counting`, the line apexes) take a TOTAL root function
`root : (z : F) → rationalRoot (H_tilde' H) z` but consume it only at `z ∈ T` — and the
matching lane (`DoubleAssignmentChain.double_assignment`) produces rational roots only **on**
its matching set (from the branch incidence `evalEval z ((P z).eval x₀) H = 0`).  A total
function is generally unconstructible (`H̃′(z, ·)` need not have an `F`-root off the matching
set), so the total-root interface is uninstantiable from the lane — the same statement-level
bug class as the F-series findings.  This module re-derives the chain at the **dependent**
root `root : ∀ z ∈ T, rationalRoot (H_tilde' H) z` and packages the `double_assignment`
output shape directly:

* `eq_of_pi_z_eq_on_finset_dep` — the counting weld (Brick C1) at dependent roots;
* `alphaFromBeta_eq_lift_of_counting_dep` / `hrep_of_cleared_counting_dep` — Brick C3;
* `hvan_line_of_perz_data_dep` — Brick V at dependent roots + sliced separability;
* `hrep_line_of_perz_data_dep` / `exists_representative_pair_line_dep` — the apexes;
* `exists_representative_pair_of_matching_branch` — **the packager**: from a monic branch
  `H` with per-`z` incidence `evalEval z ((u₀ + z•u₁).eval x₀) H = 0` (exactly
  `double_assignment`'s output conjunct, with the root built by
  `rationalRoot_of_evalEval` and its value pinned by monicity), the per-`z` divisibilities,
  `ξ`-image nonvanishing, sliced separability, and the counting input, the bundle's
  terminal `(Ppoly, hrep, hdegX)` pair exists.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace InterpolatedRepresentativeDependentRoot

open InterpolatedRepresentative InterpolatedRepresentativeWiring
  InterpolatedRepresentativeSliced MappedSeparability

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Brick C1 at dependent roots -/

/-- **The counting weld with dependent roots** — `eq_of_pi_z_eq_on_finset` with the root
function required only on the agreement set. -/
theorem eq_of_pi_z_eq_on_finset_dep
    (hH : 0 < H.natDegree) {a b : 𝒪 H} (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ z (hz : z ∈ T), (π_z z (root z hz)) a = (π_z z (root z hz)) b)
    {B : ℕ} (hw : weight_Λ_over_𝒪 hH (a - b) D ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    a = b := by
  have hsub : (↑T : Set F) ⊆ S_β (a - b) := by
    intro z hz
    have hz' : z ∈ T := Finset.mem_coe.mp hz
    refine ⟨root z hz', ?_⟩
    rw [map_sub, sub_eq_zero]
    exact hvan z hz'
  have hmul : weight_Λ_over_𝒪 hH (a - b) D * (H.natDegree : WithBot ℕ)
      ≤ ((B * H.natDegree : ℕ) : WithBot ℕ) := by
    have hcast : ((B * H.natDegree : ℕ) : WithBot ℕ)
        = (B : WithBot ℕ) * (H.natDegree : WithBot ℕ) := by push_cast; ring
    rw [hcast]
    gcongr
  have hbig : (↑T.card : WithBot ℕ) > weight_Λ_over_𝒪 hH (a - b) D * H.natDegree :=
    lt_of_le_of_lt hmul (by exact_mod_cast hcard)
  have hemb : embeddingOf𝒪Into𝕃 H (a - b) = 0 :=
    embedding_eq_zero_of_finset_subset_S_β hH (a - b) D hD hsub hbig
  have hzero : a - b = 0 := by
    refine embeddingOf𝒪Into𝕃_injective hH ?_
    rw [map_zero]
    exact hemb
  exact sub_eq_zero.mp hzero

/-! ## Brick C3 at dependent roots -/

section Cleared

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)

/-- The per-coefficient identity from dependent-root counting. -/
theorem alphaFromBeta_eq_lift_of_counting_dep
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0) {c : F[X]} {t : ℕ}
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z hz)) (clearedCoeff x₀ R H hHyp c t))
    {B : ℕ}
    (hw : weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp c t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t
      = liftToFunctionField (H := H) c :=
  alphaFromBeta_eq_lift_of_betaRec_eq_cleared x₀ R H hHyp Bcoeff hξ
    (eq_of_pi_z_eq_on_finset_dep hH D hD root hvan hw hcard)

/-- **Brick C3 at dependent roots** — `hrep_of_cleared_counting` with the root function
required only on the counting set. -/
theorem hrep_of_cleared_counting_dep
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hξ : embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ≠ 0)
    {Ppoly : F[X][Y]} {k : ℕ}
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hvan : ∀ t, t < k → ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp Bcoeff t)
        = (π_z z (root z hz)) (clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t))
    {B : ℕ}
    (hw : ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t - clearedCoeff x₀ R H hHyp (Ppoly.coeff t) t) D
      ≤ (B : WithBot ℕ))
    (hcard : B * H.natDegree < T.card)
    (htailP : ∀ t, k ≤ t → Ppoly.coeff t = 0)
    (htailα : ∀ t, k ≤ t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff := by
  ext t
  rw [coeff_polyToPowerSeries𝕃, BetaToCurveCoeffPolys.coeff_gammaLocal]
  rcases Nat.lt_or_ge t k with htk | htk
  · exact (alphaFromBeta_eq_lift_of_counting_dep x₀ R H hHyp Bcoeff hH D hD hξ root
      (hvan t htk) (hw t htk) hcard).symm
  · rw [htailP t htk, map_zero, htailα t htk]

end Cleared

/-! ## Brick V + the apexes at dependent roots and sliced separability -/

section Apex

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The set-restricted sliced separability with explicit-membership reading (the form the
packager instantiates). -/
theorem hvan_line_of_perz_data_dep (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {u₀ u₁ : F[X]} {T : Finset F}
    (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ T), (π_z z (root z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z (hz : z ∈ T), ((u₀ + z • u₁).eval x₀ : F) = (root z hz).1)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z hz) (hx z hz)))).Separable) :
    ∀ (t : ℕ), ∀ z (hz : z ∈ T),
      (π_z z (root z hz)) (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t)
        = (π_z z (root z hz)) (InterpolatedRepresentative.clearedCoeff x₀ R H hHyp
            ((InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
              (Polynomial.taylor x₀ u₁)).coeff t) t) := by
  intro t z hz
  exact hvan_signed_of_match hHyp hlc z (root z hz) (hx z hz)
    (localSeries_eq_aPTaylor_sliced hHyp hξ hlc z (root z hz) (hx z hz) (hdvd z hz)
      (hval z hz) (hsep z hz))
    (coeff_eval_linearShape_taylor x₀ z u₀ u₁ t).symm

/-- **The line apex at dependent roots.** -/
theorem hrep_line_of_perz_data_dep (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : ∀ z ∈ T, rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ T), (π_z z (root z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z (hz : z ∈ T), ((u₀ + z • u₁).eval x₀ : F) = (root z hz).1)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z hz) (hx z hz)))).Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    polyToPowerSeries𝕃 H (InterpolatedRepresentative.linearShape
        (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁))
      = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) :=
  hrep_of_cleared_counting_dep x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD
    (emb_ξ_ne_zero hHyp hξ) root
    (fun t _ z hz =>
      hvan_line_of_perz_data_dep x₀ R H hHyp hξ hmonic.leadingCoeff root hx hdvd hval hsep
        t z hz)
    (hw_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
      (fun t _ => natDegree_coeff_linearShape_le_one _ _ t))
    hcard
    (fun t hkt => InterpolatedRepresentative.coeff_linearShape_eq_zero
      (by rw [Polynomial.natDegree_taylor]; exact h₀)
      (by rw [Polynomial.natDegree_taylor]; exact h₁) hkt)
    htailα

/-! ## The packager: `double_assignment`'s branch-incidence output, consumed directly -/

/-- **The packager.**  From the matching-branch data exactly as `double_assignment` emits it —
a monic branch `H` carrying per-`z` incidence `evalEval z ((u₀ + z•u₁).eval x₀) H = 0` on the
matching set — the dependent root is `rationalRoot_of_evalEval` and its value is pinned by
monicity (`(root z).1 = (u₀ + z•u₁).eval x₀` since the `Y`-leading coefficient is `1`), so
the bundle's terminal `(Ppoly, hrep, hdegX)` pair exists, given the per-`z` divisibilities,
`ξ`-image nonvanishing, sliced separability, the counting input, and the tail. -/
theorem exists_representative_pair_of_matching_branch (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F}
    (hinc : ∀ z ∈ T, Polynomial.evalEval z ((u₀ + z • u₁).eval x₀) H = 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hx : ∀ z (hz : z ∈ T),
      (π_z z (RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    (hsep : ∀ z (hz : z ∈ T),
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z
          (RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz))
          (hx z hz)))).Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k := by
  -- the dependent root from the branch incidence
  refine ⟨InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
    (Polynomial.taylor x₀ u₁),
    hrep_line_of_perz_data_dep x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hξ h₀ h₁
      (fun z hz => RationalRootSupply.rationalRoot_of_evalEval hH (hinc z hz))
      hx hdvd ?_ hsep hcard htailα,
    InterpolatedRepresentative.degreeX_linearShape_le_one _ _,
    lt_of_le_of_lt (InterpolatedRepresentative.natDegree_linearShape_le _ _)
      (by rw [Polynomial.natDegree_taylor, Polynomial.natDegree_taylor]; exact max_lt h₀ h₁)⟩
  -- the branch value is pinned by monicity: the Y-leading coefficient is 1
  intro z hz
  rw [RationalRootSupply.rationalRoot_of_evalEval_val]
  have hlc : H.coeff H.natDegree = 1 := hmonic.leadingCoeff
  rw [hlc]
  simp

end Apex

/-! ## The counting weld: `ξ`/leading-coefficient bad places subtracted by Bézout bounds -/

section MatchingCounting

variable [DecidableEq F]
variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The single-counting front door.**  From `double_assignment`'s raw matching set (per-`z`
incidence + divisibility, NO per-`z` side conditions) and ONE counting input — the budget plus
the two Bézout-bounded bad-set sizes (`ξ`-elimination resultant degree and slice
leading-coefficient degree) below the matching-set size — the bundle's terminal
`(Ppoly, hrep, hdegX)` pair exists.  The `ξ`-nonvanishing and sliced-separability places are
carved out internally (`xiBad_card_le` + the leading-coefficient root bound); no separability
or nonvanishing hypothesis of any kind remains. -/
theorem exists_representative_pair_of_matching_counting (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    (hRdeg : 0 < R.natDegree)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {matchingSet : Finset F}
    (hinc : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((u₀ + z • u₁).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hcount : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
        + (XiAtIncidenceSupply.xiResultant hH x₀ R hHyp).natDegree
        + (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.natDegree
      < matchingSet.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k := by
  classical
  set y : F → F := fun z => (u₀ + z • u₁).eval x₀ with hy
  set lc : F[X] := (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff with hlcdef
  -- the slice is nonzero, hence its leading coefficient is nonzero
  have hslice_ne : Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hcdeg
    omega
  have hlc_ne : lc ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hslice_ne
  -- the good set: ξ-representative nonvanishing AND lc-avoidance
  set T : Finset F := matchingSet.filter (fun z =>
    Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) ≠ 0
      ∧ lc.eval z ≠ 0) with hT
  have hTsub : T ⊆ matchingSet := Finset.filter_subset _ _
  -- bad-set cardinalities
  have hbadξ : (matchingSet.filter (fun z =>
      Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0)).card
      ≤ (XiAtIncidenceSupply.xiResultant hH x₀ R hHyp).natDegree :=
    XiAtIncidenceSupply.xiBad_card_le hHyp hH hmonic.leadingCoeff hinc
  have hbadlc : (matchingSet.filter (fun z => lc.eval z = 0)).card ≤ lc.natDegree := by
    have hsub : matchingSet.filter (fun z => lc.eval z = 0) ⊆ lc.roots.toFinset := by
      intro z hz
      rw [Finset.mem_filter] at hz
      exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hlc_ne, hz.2⟩)
    calc (matchingSet.filter (fun z => lc.eval z = 0)).card
        ≤ lc.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card lc.roots := Multiset.toFinset_card_le _
      _ ≤ lc.natDegree := Polynomial.card_roots' _
  -- the complement of T inside matchingSet is covered by the two bad sets
  have hsplit : (matchingSet.filter (fun z =>
      ¬ (Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) ≠ 0
        ∧ lc.eval z ≠ 0))).card
      ≤ (XiAtIncidenceSupply.xiResultant hH x₀ R hHyp).natDegree + lc.natDegree := by
    have hcover : matchingSet.filter (fun z =>
        ¬ (Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) ≠ 0
          ∧ lc.eval z ≠ 0))
        ⊆ (matchingSet.filter (fun z =>
            Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0))
          ∪ (matchingSet.filter (fun z => lc.eval z = 0)) := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rcases hz with ⟨hzm, hznot⟩
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hξz : Polynomial.evalEval z (y z)
          (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0
      · exact Or.inl ⟨hzm, hξz⟩
      · refine Or.inr ⟨hzm, ?_⟩
        by_contra hlcz
        exact hznot ⟨hξz, hlcz⟩
    calc (matchingSet.filter _).card
        ≤ ((matchingSet.filter (fun z =>
            Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) = 0))
          ∪ (matchingSet.filter (fun z => lc.eval z = 0))).card :=
          Finset.card_le_card hcover
      _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ _ := add_le_add hbadξ hbadlc
  -- T is big enough
  have hcardT : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := matchingSet) (fun z =>
        Polynomial.evalEval z (y z) (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)) ≠ 0
          ∧ lc.eval z ≠ 0)
    rw [← hT] at hpart
    omega
  -- per-z data on T
  have hincT : ∀ z ∈ T, Polynomial.evalEval z ((u₀ + z • u₁).eval x₀) H = 0 :=
    fun z hz => hinc z (hTsub hz)
  have hdvdT : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
    fun z hz => hdvd z (hTsub hz)
  -- the constructed roots coincide with the incidence roots (value-level)
  have hroot_eq : ∀ z (hz : z ∈ T),
      RationalRootSupply.rationalRoot_of_evalEval hH (hincT z hz)
        = BranchValuePigeonhole.incidenceRootFn (H := H) (hincT z hz) :=
    fun z hz => Subtype.ext rfl
  -- hx on T from the first filter conjunct
  have hxT : ∀ z (hz : z ∈ T),
      (π_z z (RationalRootSupply.rationalRoot_of_evalEval hH (hincT z hz)))
        (ξ x₀ R H hHyp) ≠ 0 := by
    intro z hz
    have hfilter := (Finset.mem_filter.mp hz).2
    rw [hroot_eq z hz]
    exact (XiAtIncidenceSupply.hx_iff_evalEval hHyp hH hmonic.leadingCoeff
      (hincT z hz)).mpr hfilter.1
  -- sliced separability on T from the second filter conjunct
  have hsepOn : MappedSeparability.MappedSliceSeparabilityOn T hHyp :=
    MappedSeparability.mappedSliceSeparabilityOn_of_slice_leadingCoeff hHyp hRdeg hcdeg
      (fun z hz => (Finset.mem_filter.mp hz).2.2)
  -- conclude via the packager
  exact exists_representative_pair_of_matching_branch x₀ R H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hξ h₀ h₁ hincT hdvdT hxT
    (fun z hz => hsepOn z hz _ (hxT z hz)) hcardT htailα

end MatchingCounting

end InterpolatedRepresentativeDependentRoot

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.eq_of_pi_z_eq_on_finset_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.alphaFromBeta_eq_lift_of_counting_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hrep_of_cleared_counting_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hvan_line_of_perz_data_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.hrep_line_of_perz_data_dep
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.exists_representative_pair_of_matching_branch
#print axioms ArkLib.InterpolatedRepresentativeDependentRoot.exists_representative_pair_of_matching_counting
