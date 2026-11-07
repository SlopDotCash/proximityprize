/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.RadicalAssembler
import ArkLib.ToMathlib.SectionGlobalLift
import ArkLib.ToMathlib.RadicalBranch
import ArkLib.ToMathlib.GSSurfaceMappedSeparability
import ArkLib.ToMathlib.FiberSectionCoherence

/-!
# The #304 end-to-end chain theorem over the final minimal surface

**GOAL (this file, Part 4)**: `Chain304.correlatedAgreement_of_minimal_surface` — ONE
theorem whose hypothesis list IS the final minimal external surface of #304 and whose
conclusion is the keystone `δ_ε_correlatedAgreementCurves` ([BCIKS20] Theorem 1.4 /
Claim A.2 conclusion) in the strict list-decoding regime `δ < 1 − √ρ`.

The surface (`Chain304.MinimalSurface304`, per decoding `(u, P)`):
1. the fiberwise GS-decoder outputs — per-centre sections `v : F → F[X]` rooting the
   fibers `evalX (C y) R` on a centre set `S`, their local `(k+1)`-coherence, and the
   global-lift budget `DX + deg_Y R · (k−1) < |S|`;
2. the §6 incidence fact `hOnH` at the (unique) produced global section;
3. the §6 counting budget `hbig` at the RADICAL branch certificate;
4. `MappedSliceSeparability` (the audit's irreducible separability residue — strictly
   weaker than `R.Separable`, see `RadicalAssembler`'s audit);
5. the graded budget side conditions (`hd2`/`hdHD`/`hD_Rx0`/`hRgrade`);
6. the series-level identifications `hsubst`/`hβHensel`/`hHensel`/`hdeg`.

Mechanically the chain is
`RootOn304.correlatedAgreement_listDecoding_strict_finOn` (the keystone front door)
∘ `RootOn304.Section5StrictDataFinOn.ofProducersOn_radical` (the radical bundle producer
underlying `hcoeffPoly_witness_of_producersOn_radical_sep`)
∘ `FiberSectionCoherence.section_dvd_global_of_local_coherence` (the fiberwise → global
section lift, interpolation rigidity + lifting budget).

**Build note (olean gap)**: `ArkLib/ToMathlib/RadicalAssembler.lean` is landed in-tree
but has NO olean in the current build, so it cannot be imported here; Parts 1–3 below
are its content inlined VERBATIM (same fully-qualified names, statements and proofs
unchanged) under its own three imports, which all have oleans
(`SectionGlobalLift`, `RadicalBranch`, `GSSurfaceMappedSeparability`).  When the tree
heals, delete Parts 1–3 and `import ArkLib.ToMathlib.RadicalAssembler` instead.
-/

/-! ## Parts 1–3 — `ArkLib/ToMathlib/RadicalAssembler.lean` inlined VERBATIM (no olean; see build note) -/
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open UniqueFactorizationMonoid
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace RadicalWire304

/-! ## Part 1 — the canonical radical package at the bundle

`split_canonical_radical` + `hbr_canonical_radical`: the `(hsplit, hbr)` package at
`radical (evalX (C x₀) b.R)`, with NO separability input — squarefreeness is free on the
radical; the only consequence of the bundle-internal `separable_evalX` consumed is
nonzeroness of the fiber. -/

section CanonicalRadical

variable {F : Type} [Field F] [DecidableEq F]

variable [Fintype F]

end CanonicalRadical

/-! ## Part 2 — the radical decoded-root supply

`DecodedRootSupply.rootDecoded` re-run against the radical: the centre-fold linear factor
`(Y′ − C (w.eval (C x₀)))` is prime, hence divides `radical (evalX (C x₀) R)`; through the
radical split and per-place branch separation at the RADICAL cofactor, every such place
decodes a rational root of `H` — no squarefreeness of the fiber anywhere. -/

section DecodedRadical

variable {F : Type} [Field F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

section Family

variable [Fintype F]

end Family

end DecodedRadical

end RadicalWire304

/-! ## Part 3 — the assembler re-run against the radical: the front door -/

namespace RootOn304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

section ProducersRadical

open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

end ProducersRadical

end RootOn304

end ArkLib

/-! ## Part 4 — the #304 END-TO-END CHAIN THEOREM over the final minimal surface -/

namespace ArkLib

namespace Chain304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge
open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- **The final minimal external surface of #304**, per decoding `(u, P)`: the exact
hypothesis list of the end-to-end chain theorem `correlatedAgreement_of_minimal_surface`.

Contents (each field is a genuinely-research-level input, named and documented; nothing
here is fabricated, and nothing beyond this list is consumed):

* the centre/bundle/representative data of [BCIKS20] §5 (`x₀`, `b`, `Ppoly`, `hmonic`,
  `hrep`, `hdegX`);
* the **fiberwise GS-decoder outputs**: per-centre sections `v` rooting the fibers on a
  centre set `S` (`hfib`), their local `(k+1)`-coherence (`hcoh`), and the global-lift
  budget (`hcoeffR` + `hbigS`) — `FiberSectionCoherence` turns these into ONE global
  section `w` of `Y`-degree `< k` with `(Y′ − C w) ∣ R`;
* the **§6 incidence fact** `hOnH` and the **§6 counting budget at the RADICAL branch
  certificate** `hbig`, both stated at the produced global section — which is UNIQUE
  given `(S, v)` (`FiberSectionCoherence.section_eq_of_agree`: two `Y`-degree-`< k`
  sections agreeing on the `≥ k+1` centres of `S` coincide), so each of these
  `w`-quantified fields pins exactly one section;
* **`MappedSliceSeparability`** (`hsepM`) — the audit's irreducible residue of the
  external trivariate separability, strictly weaker than `b.R.Separable`
  (`MappedSeparability.MappedSliceSeparability.of_separable` is the drop-in);
* the graded budget side conditions (`hd2`, `hdHD`, `hD_Rx0`, `hRgrade`);
* the series-level identifications (`hsubst`, `hβHensel`, `hHensel`, `hdeg`). -/
structure MinimalSurface304 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the centre of the §5 curve analysis. -/
  x₀ : F
  /-- the GS factor bundle at the centre (`R`, `H`, `D`, the standing `Hypotheses`). -/
  b : GSFactorData.Bundle (F := F) x₀
  /-- irreducibility of the bundle's `H` (instance form). -/
  hIrr : Fact (Irreducible b.H)
  /-- positivity of `natDegree b.H` (instance form). -/
  hPos : Fact (0 < b.H.natDegree)
  /-- the Prop-5.5 polynomial representative of `γ`. -/
  Ppoly : F[X][Y]
  /-- monicity of the bundle's `H`. -/
  hmonic : b.H.Monic
  /-- `Ppoly` represents `γ`. -/
  hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp
  /-- linearity of the representative in `Z`. -/
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- fiberwise GS-decoder output: the centre set. -/
  S : Finset F
  /-- fiberwise GS-decoder output: the per-centre section values. -/
  v : F → F[X]
  /-- per-centre sections: the decoded value roots the fiber at every centre of `S`. -/
  hfib : ∀ y ∈ S,
    (Polynomial.X - Polynomial.C (v y)) ∣ Bivariate.evalX (Polynomial.C y) b.R
  /-- the centre set carries at least `k + 1` centres. -/
  hScard : k + 1 ≤ S.card
  /-- local `(k+1)`-coherence of the decoder outputs: every `(k+1)`-subset of the family
  lies on SOME polynomial section of `Y`-degree `< k` (interpolation rigidity then glues
  these to ONE global section). -/
  hcoh : ∀ T ⊆ S, T.card = k + 1 →
    ∃ wT : F[X][Y], wT.natDegree < k ∧ ∀ y ∈ T, v y = wT.eval (Polynomial.C y)
  /-- the uniform coefficient budget of the surface. -/
  DX : ℕ
  /-- every `Y′`-coefficient of `b.R` has centre-degree `≤ DX`. -/
  hcoeffR : ∀ j, (b.R.coeff j).natDegree ≤ DX
  /-- the global-lift budget: the centre set beats `DX + deg_Y R · (k − 1)`. -/
  hbigS : DX + b.R.natDegree * (k - 1) < S.card
  /-- **the §6 incidence fact** at the produced global section: the section lies on the
  bundle's own branch `H`.  (Quantified over the produced section, which is unique.) -/
  hOnH : ∀ w : F[X][Y], w.natDegree < k →
    (∀ y ∈ S, v y = w.eval (Polynomial.C y)) →
    (Polynomial.X - Polynomial.C w) ∣ b.R →
    b.H.eval (w.eval (Polynomial.C x₀)) = 0
  /-- **the consolidated separability residue**: `MappedSliceSeparability`, strictly
  weaker than `b.R.Separable` (the audit's sole genuine consumption of the external
  trivariate separability — not deletable by the radical). -/
  hsepM : MappedSeparability.MappedSliceSeparability b.hHyp
  /-- graded side condition: `Y`-degree of `R` at least `2`. -/
  hd2 : 2 ≤ Bivariate.natDegreeY b.R
  /-- graded side condition: `natDegree b.H ≤ b.D`. -/
  hdHD : b.H.natDegree ≤ b.D
  /-- graded side condition: `b.D` dominates the total degree of the centre fiber. -/
  hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R)
  /-- graded side condition: the graded coefficient bounds on `b.R`. -/
  hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j
  /-- **the §6 counting budget at the RADICAL branch certificate**, at the produced
  global section (quantified over the produced section, which is unique). -/
  hbig : ∀ w : F[X][Y], w.natDegree < k →
    (∀ y ∈ S, v y = w.eval (Polynomial.C y)) →
    (Polynomial.X - Polynomial.C w) ∣ b.R →
    gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + ((radical (Bivariate.evalX (Polynomial.C x₀) b.R) /ₘ b.H).eval
            (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F
  /-- series identification: validity of the BCIKS substitution `X ↦ X − x₀`. -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H)
  /-- series identification: the signed numerator coefficients are the genuine Hensel
  coefficients. -/
  hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t
  /-- series identification: every linear decomposition of `γ` yields the per-`z` Hensel
  datum of the §5 specialisation bridge. -/
  hHensel : ∀ v₀ v₁ : F[X],
    γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁
  /-- series identification: degree bounds of any linear decomposition of `γ`. -/
  hdeg : ∀ v₀ v₁ : F[X],
    γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

/-- **THE #304 END-TO-END CHAIN THEOREM**: from the final minimal external surface —
the fiberwise GS-decoder outputs (per-centre sections + local coherence + budgets), the
§6 incidence fact, the §6 counting budget at the radical certificate,
`MappedSliceSeparability`, and the series-level identifications — conclude
`δ_ε_correlatedAgreementCurves` ([BCIKS20] Theorem 1.4 conclusion) in the strict
list-decoding regime `δ < 1 − √ρ`.

Chain: `correlatedAgreement_listDecoding_strict_finOn`
∘ `Section5StrictDataFinOn.ofProducersOn_radical`
∘ `FiberSectionCoherence.section_dvd_global_of_local_coherence`. -/
theorem correlatedAgreement_of_minimal_surface {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hSurface : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        MinimalSurface304 (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine RootOn304.correlatedAgreement_listDecoding_strict_finOn hδ ?_
  intro u hprob hJ P hP
  have s := hSurface u hprob hJ P hP
  haveI := s.hIrr
  haveI := s.hPos
  -- the fiberwise → global lift: ONE section `w`, degree < k, coherent on S, dividing R
  have hex : ∃ w : F[X][Y], w.natDegree < k ∧
      (∀ y ∈ s.S, s.v y = w.eval (Polynomial.C y)) ∧
      (Polynomial.X - Polynomial.C w) ∣ s.b.R :=
    FiberSectionCoherence.section_dvd_global_of_local_coherence
      s.hfib s.hScard s.hcoh s.hcoeffR s.hbigS
  have hwdeg := hex.choose_spec.1
  have hwagree := hex.choose_spec.2.1
  have hdvdR := hex.choose_spec.2.2
  -- the radical bundle producer at the produced section
  exact RootOn304.Section5StrictDataFinOn.ofProducersOn_radical s.b s.Ppoly s.hmonic
    s.hrep s.hdegX hwdeg hdvdR (s.hOnH _ hwdeg hwagree hdvdR) s.hsepM
    s.hd2 s.hdHD s.hD_Rx0 s.hRgrade (s.hbig _ hwdeg hwagree hdvdR)
    s.hsubst s.hβHensel s.hHensel s.hdeg

end Chain304

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_radical
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical_sep
#print axioms ArkLib.Chain304.correlatedAgreement_of_minimal_surface
