/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaInputSupply
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.BCIKS20ConcreteJohnson
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.KeystoneStrictResidual

/-!
# The final §5 concrete assembly — `BetaCurveInputFin` from the GS interpolant + a received word

This is the **last assembly layer** of the BCIKS20 §5 list-decoding agreement chain on the keystone
branch.  The two supply layers below it are already proven:

* `ArkLib.GSFactorData.of_section5Inputs` — the **R/H factorization** (Step 2 of the mission): from
  the GS interpolant `ModifiedGuruswami` (Prop 5.5) and the graph side conditions it produces the
  Appendix-A.2 curve datum `GSFactorData.Bundle x₀ = (R, H, Fact Irreducible, Fact pos, Hypotheses,
  hH, D, hD)`.  Nothing here re-proves it.
* `ArkLib.BetaInputSupply.betaCurveInputFin_of_section5` — the **per-field §5 input supply** (Steps
  3, the App-A.4 weight collapse, F1 centring): it builds the satisfiable `BetaCurveInputFin u`
  bundle field-by-field from primitive centred §5 data, discharging `hsubst` (at `x₀ = 0`), `hγ`
  (from the single numerator residual `hβ`), `hcard` (concrete arithmetic), and `hPz` (per-`z`
  Hensel datum), leaving the genuine §5 geometric inputs.

This file connects the two: `betaCurveInputFin_of_bundle` lifts the Bundle output of the GS
interpolant directly into the `betaCurveInputFin_of_section5` argument slots (the bundle's `R`/`H`/…
*are* the function-field setup `betaCurveInputFin_of_section5` consumes, centred at `x₀ = 0`), and
`section5Concrete_of_close_word` packages a per-received-word supplier of `BetaCurveInputFin` from
the GS interpolant plus the genuine §5 / App-A.4 residuals.

Finally `correlatedAgreement_affine_curves_johnson_concrete` is the **milestone**: it feeds that
per-`u` supplier to the strict keystone front door
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`, so the
literal BCIKS20 keystone goal `δ_ε_correlatedAgreementCurves` follows in the strict square-root
Johnson regime, with the list-decoding branch driven by the **real `betaRec`** capsule and the
inputs reduced to the genuine §5 geometric frontier.

## What stays a named residual (the true mathematical frontier)

Per the honest-fallback discipline, the deepest construction steps that touch live-session-owned
files or the deferred `L13`/`F1` drop-ins are isolated as **named hypotheses of the
supplier**, never `sorry` and never `≡` the conclusion:

* the GS interpolant `h_gs : ModifiedGuruswami …` (Prop 5.5; satisfiable in regime via
  `modified_guruswami_has_a_solution`) and the graph side conditions `hx0`/`hsep`/`hS_nonempty`/
  `A`/`hA`/`hcount`/`hlarge` — the §5 standing geometric inputs;
* `hβ` — the single App-A.4 numerator-identification residual (`β = betaRec`, the deferred L13);
* `mpFin` — the ingredient-C per-point matching geometry (built per point via
  `MpProducer.mkMatchingPoint`);
* the App-A weight-collapse budgets `hbB`/`hBzero`/`hbξ` + the concrete finite cardinality bound
  `hcardConcreteFin` + the algebraic-degree datum `htailDeg`;
* the §5 specialisation bridge `hHensel`/`hdegPz` (per-`z` Hensel root datum + degree bounds);
* the Prop-5.5 representative `Ppoly`/`hrep`/`hdegX`.

No `sorry`/`axiom`/`native_decide`; `#print axioms` at the bottom shows only
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.2/A.4.
-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace Section5Concrete

open KeystoneStrictResidual HPzBridge HcardDischarge BetaToCurveCoeffPolys
open BetaInputSupply
open ProximityGap Polynomial Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Bridge: `BetaCurveInputFin` from a centred GS-factor `Bundle`

`GSFactorData.Bundle (0 : F)` *is* the function-field head that `betaCurveInputFin_of_section5`
consumes (`b.R`, `b.H`, `b.hIrr`, `b.hPos`, `b.hHyp`, `b.hH`, `b.D`, `b.hD`).  We thread it through,
keeping the per-field §5 residuals as explicit arguments.  This is the gluing lemma that lets the
GS-interpolant output drive the keystone Johnson branch without re-stating the curve datum. -/

/-- **`BetaCurveInputFin` from a centred GS-factor `Bundle`.**

Lifts a `GSFactorData.Bundle (0 : F)` (the Appendix-A.2 curve datum produced by the GS interpolant)
into the keystone input bundle `BetaCurveInputFin u`, by supplying the bundle's
function-field fields
to `BetaInputSupply.betaCurveInputFin_of_section5` and carrying the remaining genuine §5 / App-A.4
residuals as explicit arguments. -/
noncomputable def betaCurveInputFin_of_bundle {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (T : ℕ)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec (0 : F) b.R b.H b.hHyp Bcoeff t)
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z))
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ (0 : F) b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    (hcardConcreteFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ))
    (htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta (0 : F) b.R b.H b.hHyp Bcoeff t = 0)
    (hMatchingDvd : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdegPz : ∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u :=
  betaCurveInputFin_of_section5 (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    b.R b.H b.hIrr b.hPos b.hHyp Bcoeff b.hH b.D b.hD matchingSet root T
    Ppoly hrep hdegX hβ mpFin hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin htailDeg
    hMatchingDvd hdegPz

/-! ## The per-received-word supplier `section5Concrete_of_close_word`

Packaging `betaCurveInputFin_of_bundle` into the *supplier shape* the keystone front door consumes:
for every received curve `u` (under the §5 regime conditions) a `BetaCurveInputFin u`.  The
GS-factor `Bundle` is the `(u, P)`-independent head (it depends only on the received affine-line
endpoints behind the construction), so it is supplied once; the per-`u` residual data — the genuine
§5 / App-A.4 geometric inputs isolated above — is supplied by the `perWord` producer.

This is the honest final supplier: the only inputs are the GS-factor `Bundle` (the proven output of
the GS interpolant chain) and, per received word, the named §5 residual frontier. -/

/-- **The per-received-word `BetaCurveInputFin` supplier from a centred GS-factor `Bundle`.**

For each received curve `u` satisfying the §5 regime conditions (the proximity probability
bound, the unique-decoding lower bound, the strict square-root upper bound), produces a
`BetaCurveInputFin u`
out of the (`u`-independent) GS-factor `Bundle (0 : F)` and a per-`u` producer of the genuine §5 /
App-A.4 residual data (numerator residual, per-point matching, weight budgets, concrete cardinality,
algebraic-degree datum, specialisation bridge, Prop-5.5 representative).

This is exactly the `hInput` shape consumed by
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`. -/
noncomputable def section5Concrete_of_close_word {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ (0 : F) b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec (0 : F) b.R b.H b.hHyp Bcoeff t)
    -- per received word `u`: the genuine §5 geometric residual data (matching set, root section,
    -- truncation index, Prop-5.5 representative, per-point matching, concrete cardinality, tail
    -- degree, specialisation bridge):
    (perWord : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Σ' (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' b.H) z) (T : ℕ)
         (Ppoly : F[X][Y]),
        (polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp) ×'
        (Polynomial.Bivariate.degreeX Ppoly ≤ 1) ×'
        (∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
          BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z)) ×'
        (∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
          > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ)) ×'
        (∀ t, T < t →
          BetaToCurveCoeffPolys.αFromBeta (0 : F) b.R b.H b.hHyp Bcoeff t = 0) ×'
        (∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) ×'
        (∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1))
    (u : WordStack F (Fin (k + 1)) ι) :
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u :=
  match perWord u with
  | ⟨matchingSet, root, T, Ppoly, hrep, hdegX, mpFin, hcardConcreteFin, htailDeg, hMatchingDvd, hdegPz⟩ =>
    betaCurveInputFin_of_bundle (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
      b Bcoeff matchingSet root T Ppoly hrep hdegX hβ mpFin
      hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin htailDeg hMatchingDvd hdegPz

/-! ## The milestone — the strict keystone consuming only genuine regime hypotheses

Feeding the per-`u` supplier into the strict Johnson front door yields the literal BCIKS20 keystone
goal `δ_ε_correlatedAgreementCurves` in the strict square-root regime.  The Johnson list-decoding
branch is driven by the real `betaRec` capsule (via the satisfiable `BetaCurveInputFin`), and the
inputs are the GS-factor `Bundle` (proven output of the GS interpolant chain) plus the genuine §5
geometric residual frontier carried by `section5Concrete_of_close_word`. -/

/-- **Milestone — the §5 correlated-agreement keystone from concrete GS-interpolant data.**

`δ_ε_correlatedAgreementCurves` (the literal `correlatedAgreement_affine_curves` goal) holds in the
strict square-root Johnson regime (`hδ : δ < 1 − √rate`) given:

* a GS-factor `Bundle (0 : F)` (the proven output of `GSFactorData.of_section5Inputs`, i.e. the GS
  interpolant `ModifiedGuruswami` + graph side conditions);
* the standing App-A weight/degree data `Bcoeff`/`hd1`/`hdH_le`/`hdH_D`/`hbB`/`hBzero`/`hbξ` and the
  single numerator residual `hβ`;
* a per-received-word producer `perWord` of the genuine §5 / App-A.4 geometric residual data.

The list-decoding branch is supplied by the satisfiable `BetaCurveInputFin` via
`section5Concrete_of_close_word`, so the keystone consumes a **real `β`**.  No `sorry`/`axiom`. -/
theorem correlatedAgreement_affine_curves_johnson_concrete {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (b : GSFactorData.Bundle (F := F) (0 : F))
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (hd1 : 1 ≤ b.R.natDegree) (hdH_le : b.H.natDegree ≤ b.R.natDegree)
    (hdH_D : b.H.natDegree ≤ b.D)
    (hbB : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        weight_Λ_over_𝒪 b.hH (Bcoeff i₁ p) b.D
          ≤ (WithBot.some ((b.D - Multiset.card p.parts)
              + (b.R.natDegree - betaδ i₁ - Multiset.card p.parts)
                * (b.D - b.H.natDegree)) : WithBot ℕ))
    (hBzero : ∀ (i₁ : ℕ) {m : ℕ} (p : Nat.Partition m),
        b.R.natDegree - betaδ i₁ < Multiset.card p.parts → Bcoeff i₁ p = 0)
    (hbξ : weight_Λ_over_𝒪 b.hH (ξ (0 : F) b.R b.H b.hHyp) b.D
        ≤ (WithBot.some ((b.R.natDegree - 1) * (b.D - b.H.natDegree + 1)) : WithBot ℕ))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec (0 : F) b.R b.H b.hHyp Bcoeff t)
    (perWord : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Σ' (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' b.H) z) (T : ℕ)
         (Ppoly : F[X][Y]),
        (polyToPowerSeries𝕃 b.H Ppoly = γ (0 : F) b.R b.H b.hHyp) ×'
        (Polynomial.Bivariate.degreeX Ppoly ≤ 1) ×'
        (∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
          BetaMatchingVanishes.MatchingPoint (0 : F) b.R b.H b.hHyp Bcoeff t z (root z)) ×'
        (∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
          > (((2 * t + 1) * b.R.natDegree * b.D * b.H.natDegree : ℕ) : WithBot ℕ)) ×'
        (∀ t, T < t →
          BetaToCurveCoeffPolys.αFromBeta (0 : F) b.R b.H b.hHyp Bcoeff t = 0) ×'
        (∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) ×'
        (∀ (_P : F → Polynomial F) (v₀ v₁ : F[X]),
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun _hk u _hprob _hJ _hsqrt =>
      section5Concrete_of_close_word (k := k) (deg := deg) (domain := domain) (δ := δ)
        b Bcoeff hd1 hdH_le hdH_D hbB hBzero hbξ hβ perWord u)

end Section5Concrete

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.Section5Concrete.betaCurveInputFin_of_bundle
#print axioms ArkLib.Section5Concrete.section5Concrete_of_close_word
#print axioms ArkLib.Section5Concrete.correlatedAgreement_affine_curves_johnson_concrete
