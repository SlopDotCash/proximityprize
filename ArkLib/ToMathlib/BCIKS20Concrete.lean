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
  3, the App-A.4 weight collapse, F1 centring): it builds the per-decoded-family
  `BetaCurveInputFin u P` bundle field-by-field from primitive centred §5 data, discharging
  `hsubst` (at `x₀ = 0`), `hγ` (from the single numerator residual `hβ`), `hcard` (concrete
  arithmetic), and `hPz` (the per-`z` matching-divisibility input for `P`), leaving the remaining
  §5 inputs as hypotheses.

This file connects the two: `betaCurveInputFin_of_bundle` lifts the Bundle output of the GS
interpolant directly into the `betaCurveInputFin_of_section5` argument slots (the bundle's `R`/`H`/…
*are* the function-field setup `betaCurveInputFin_of_section5` consumes, centred at `x₀ = 0`), and
`section5Concrete_of_close_word` packages a per-(received word, decoded family) supplier of
`BetaCurveInputFin` from the GS interpolant plus the remaining §5 / App-A.4 residuals.

Finally `correlatedAgreement_affine_curves_johnson_concrete` is the **milestone**: it feeds that
per-`(u, P)` supplier to the strict keystone front door
`KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict`, so the
literal BCIKS20 keystone goal `δ_ε_correlatedAgreementCurves` follows in the strict square-root
Johnson regime **from** these hypotheses, with the list-decoding branch routed through the
`betaRec` capsule.

## Status: conditional, and not satisfiable as assembled

Nothing in-tree supplies the hypotheses of the milestone. Before the audit-L72 repair the
specialisation inputs were quantified over every `P : F → Polynomial F`, which made every produced
bundle contradictory on a nonempty good set; they are now stated for the decoded family `P` only.
Two independent obstructions remain:

* the GS-factor head `b` (hence `γ (0 : F) b.R b.H b.hHyp`) is shared by **all** received words
  and decoded families. `hrep`/`hdegX` then give a single linear representative, and the
  per-`(u, P)` specialisation inputs force every decoded family of every received word to agree
  with it on its good set. `perWord` is quantified over every stack (it carries no regime
  premise), so the constant family `0` for the zero stack and the constant family `1` for the
  stack whose first row is the all-ones codeword (other rows zero) — both decoded at every
  parameter once `0 < deg` — would have to agree at every parameter: `perWord` cannot be supplied
  when `0 < deg`, which the milestone assumes (`[NeZero deg]`). This argument is recorded here,
  not kernel-checked. A faithful supplier must choose the head per `(u, P)`;
* the strict front door derives `StrictCoeffPolysResidual`, refuted in-tree at `k = 1`, `deg = 2`,
  `δ = 3/7` (`ProximityGap.StrictCanonicalCoeffPolysRefutation.not_strictCoeffPolysResidual`), and
  the bundle carries the further obstructions listed in the `KeystoneStrictResidual` module
  docstring.

## What stays a named residual

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
* the §5 specialisation bridge `hMatchingDvd`/`hdegPz` for the decoded family `P` (per-`z`
  matching-divisibility input + degree bounds);
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
into the keystone input bundle `BetaCurveInputFin u P` for the decoded family `P`, by supplying the
bundle's function-field fields to `BetaInputSupply.betaCurveInputFin_of_section5` and carrying the
remaining §5 / App-A.4 residuals (with the specialisation inputs stated for `P` only) as explicit
arguments. -/
noncomputable def betaCurveInputFin_of_bundle {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
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
    (hMatchingDvd : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdegPz : ∀ v₀ v₁ : F[X],
      γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  betaCurveInputFin_of_section5 (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    b.R b.H b.hIrr b.hPos b.hHyp Bcoeff b.hH b.D b.hD matchingSet root T
    Ppoly hrep hdegX hβ mpFin hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin htailDeg
    hMatchingDvd hdegPz

/-! ## The per-`(u, P)` supplier `section5Concrete_of_close_word`

Packaging `betaCurveInputFin_of_bundle` into the *supplier shape* the keystone front door consumes:
for every received curve `u` and every decoded family `P` on its good set, a
`BetaCurveInputFin u P`.  In this assembly the GS-factor `Bundle` is one head, supplied once and
shared by every `(u, P)`; the per-`(u, P)` residual data are supplied by the `perWord` producer.

Sharing the head is a limitation of this assembly, not a property of [BCIKS20] (there the GS
interpolant is built from the received curve itself): it forces the decoded families of all
received words onto a single linear representative, so `perWord` cannot be supplied once
`0 < deg` (see the module docstring). -/

/-- **The per-`(u, P)` `BetaCurveInputFin` supplier from a centred GS-factor `Bundle`.**

For each received curve `u` and each decoded family `P` on its good set, produces a
`BetaCurveInputFin u P` out of the shared GS-factor `Bundle (0 : F)` and a per-`(u, P)` producer
of the remaining §5 / App-A.4 residual data (matching set, root section, truncation index,
Prop-5.5 representative, per-point matching, concrete cardinality, algebraic-degree datum, and the
specialisation inputs for `P`).

Its uncurried form is the `hInput` shape consumed by
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
    -- per received word `u` and decoded family `P` on its good set: the remaining §5 residual
    -- data (matching set, root section, truncation index, Prop-5.5 representative, per-point
    -- matching, concrete cardinality, tail degree, specialisation inputs for `P`):
    (perWord : ∀ (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F),
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
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
        (∀ v₀ v₁ : F[X],
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) ×'
        (∀ v₀ v₁ : F[X],
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1))
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    (hP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) :
    BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  match perWord u P hP with
  | ⟨matchingSet, root, T, Ppoly, hrep, hdegX, mpFin, hcardConcreteFin, htailDeg, hMatchingDvd, hdegPz⟩ =>
    betaCurveInputFin_of_bundle (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
      (P := P) b Bcoeff matchingSet root T Ppoly hrep hdegX hβ mpFin
      hd1 hdH_le hdH_D hbB hBzero hbξ hcardConcreteFin htailDeg hMatchingDvd hdegPz

/-! ## The milestone — the strict keystone from the concrete assembly (conditional)

Feeding the per-`(u, P)` supplier into the strict Johnson front door yields the literal BCIKS20
keystone goal `δ_ε_correlatedAgreementCurves` in the strict square-root regime **from** these
hypotheses.  The Johnson list-decoding branch is routed through the `betaRec` capsule (via
`BetaCurveInputFin`), and the inputs are the shared GS-factor `Bundle` plus the per-`(u, P)`
residual data carried by `section5Concrete_of_close_word`.  As explained in the module docstring,
the shared head makes `perWord` impossible to supply once `0 < deg` (which `[NeZero deg]`
assumes); the theorem is a conditional reduction only. -/

/-- **Milestone — the §5 correlated-agreement keystone from concrete GS-interpolant data
(conditional).**

`δ_ε_correlatedAgreementCurves` (the literal `correlatedAgreement_affine_curves` goal) holds in the
strict square-root Johnson regime (`hδ : δ < 1 − √rate`) given:

* a GS-factor `Bundle (0 : F)` (as produced by `GSFactorData.of_section5Inputs` from the GS
  interpolant `ModifiedGuruswami` + graph side conditions), shared by all received words;
* the standing App-A weight/degree data `Bcoeff`/`hd1`/`hdH_le`/`hdH_D`/`hbB`/`hBzero`/`hbξ` and the
  single numerator residual `hβ`;
* a per-`(u, P)` producer `perWord` of the remaining §5 / App-A.4 residual data, for every decoded
  family `P` on the good set of `u`.

The list-decoding branch is supplied by `BetaCurveInputFin` via `section5Concrete_of_close_word`.
No `sorry`/`axiom`; but the hypotheses are not jointly satisfiable (the shared head rules out
`perWord` once `0 < deg`, and the route goes through the refuted `StrictCoeffPolysResidual`; see
the module docstring). -/
theorem correlatedAgreement_affine_curves_johnson_concrete [SampleableType F] {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
    (perWord : ∀ (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F),
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
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
        (∀ v₀ v₁ : F[X],
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          HenselDatumProducer.MatchingDvdInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) ×'
        (∀ v₀ v₁ : F[X],
          γ (0 : F) b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
            ((Polynomial.map Polynomial.C v₀)
              + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
          v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun _hk u _hprob _hJ _hsqrt P hP =>
      section5Concrete_of_close_word (k := k) (deg := deg) (domain := domain) (δ := δ)
        b Bcoeff hd1 hdH_le hdH_D hbB hBzero hbξ hβ perWord u P hP)

end Section5Concrete

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.Section5Concrete.betaCurveInputFin_of_bundle
#print axioms ArkLib.Section5Concrete.section5Concrete_of_close_word
#print axioms ArkLib.Section5Concrete.correlatedAgreement_affine_curves_johnson_concrete
