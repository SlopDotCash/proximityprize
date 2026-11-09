/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.CoeffExtract
import ArkLib.ToMathlib.IngredientCBridge

/-!
# Keystone capstone — the `hcoeffPoly` witness for the Johnson list-decoding branch

This file assembles the BCIKS20 §5 coefficient-polynomial witness from the supporting
function-field lemmas. The witness `hcoeffPoly` is consumed by the list-decoding theorem

  `ProximityGap.RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds`  (Curves.lean:1199)

whose `hcoeffPoly` hypothesis (Curves.lean:1214-1222) is, verbatim:

  `∀ P : F → Polynomial F,`
  `  (∀ z ∈ RS_goodCoeffsCurve u δ, (P z).natDegree < deg ∧ δᵣ(…, (P z).eval ∘ domain) ≤ δ) →`
  `  ∃ B : ℕ → Polynomial F,`
  `    (∀ j < deg, (B j).natDegree < k + 1) ∧`
  `    ∀ z ∈ RS_goodCoeffsCurve u δ, ∀ j < deg, (P z).coeff j = (B j).eval z`

i.e. the §5 statement *"each coefficient of the decoded curve polynomial is itself a polynomial of
degree `< k+1` in the curve parameter `z`, over the good set."*

## What this capstone proves, and what stays an explicit hypothesis

**Scope (compatibility only).** The theorems here (`hcoeffPoly_witness_of_curveCoeffPolys`,
`hcoeffPoly_of_johnson_regime`, `jointAgreement_of_johnson_regime`) do not derive the
per-coefficient curve polynomials from the §5 mathematics. They take the output-shaped
assumption `Section55CurveCoeffOutput` / `CurveCoeffPolys` (`hCurvePolys`: each coefficient index
`j` carries a degree-`< k+1` interpolant agreeing on the good set) as a hypothesis, which is
essentially the front-door `hcoeffPoly` obligation itself, and prove (kernel-clean, no `sorry`)
that it yields the bundled `hcoeffPoly` witness and hence `jointAgreement`. See also the note
before `Section55CurveCoeffOutput` below.

**Historical intent (not what is proved here).** The capstone was planned as the end of a
brick chain for the **abstract function-field core** of §5:

  `betaRec` (App-A.4 recursion, defined+terminating+lands-in-𝒪, `BetaRecursion`)
    → `betaRec_weight_le_concrete ≤ (2t+1)·d_R·D`     (`BetaWeightInduction` + `BetaWeightCollapse`)
    → `betaRec_matchingVanishes`                         (`BetaMatchingVanishes` + `CoeffExtract`)
    → `embeddingOf𝒪Into𝕃 (betaRec t) = 0`                 (`IngredientCBridge`, ingredient C)
    → curve `γ` is linear-in-`Z`, coeffs per-point   (`Claim59Conditional`/`Claim510Conditional`)

Several links of that chain are themselves conditional: `betaRec_matchingVanishes` consumes
per-point `MatchingPoint` bundles that are equivalent to its conclusion
(`betaRec_matchingVanishes_iff`), and the ingredient-C bridge consumes the per-point vanishing
plus a `Λ·d` count. The old ledger claimed that the chain bottoms out on a single §5 datum (the
Guruswami–Sudan interpolant's multiplicity-vanishing at the centre in the Johnson radius
`δ ≤ δ₀`) plus in-tree degree facts; that reduction is **not** established in this file, and the
geometric producer obligations (matching sets, per-point vanishing, counts, degree data) remain
explicit elsewhere. The current smaller route is `KeystoneAssembly.keystone_of_section5Inputs`,
whose explicit inputs are the corrected `Section5StrictDataFin` producer bundle and a boundary
datum.

No part claimed proven contains `sorry`/`admit`/`native_decide`; every genuine gap is an explicit
hypothesis.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace ArkLib

namespace KeystoneCapstone

open ProximityGap Polynomial Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The §5 list-decoding output, as an explicit bridge datum

`CurveCoeffPolys` is the conclusion of the BCIKS §5 list-decoding section in the form the front door
needs: for a candidate decoding `P : F → Polynomial F` of the curve, **every** coefficient index
`j < deg` is interpolated, *over the good set*, by a single polynomial `B j` of degree `< k+1`.

This is exactly what the verified abstract chain produces.  Concretely, ingredient C
(`IngredientC.embedding_eq_zero_of_matchingSet_large`) forces `embeddingOf𝒪Into𝕃 β = 0`, whence
Claims 5.9/5.10 (`Claim59Conditional.gamma_linear_in_Z_of_tail_zero`,
`Claim510.gamma_matches_word_concrete`) give the per-point linear-in-`Z` structure of the decoded
curve; the `(X − x₀)^t` coefficient reading (`CoeffExtract.coeff_extract_betaRec`) is what turns the
abstract vanishing into the scalar coefficient identities.  Generalising the line case (`k = 1`) to
arbitrary degree `< k+1` gives one interpolant `B j` per coefficient index `j`.

We keep this as a `Prop`-level datum so the capstone is a *finite composition under one explicit
regime hypothesis*, never a `sorry`. -/
def CurveCoeffPolys {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Prop :=
  ∀ j < deg, ∃ Bj : Polynomial F, Bj.natDegree < k + 1 ∧
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff j = Bj.eval z

/-! ## Bundling: per-index curve polynomials ⟹ the front-door `hcoeffPoly` shape

The front door wants a *single* `B : ℕ → Polynomial F` with the joint degree-and-eval conclusion.
`CurveCoeffPolys` gives one interpolant per index; we bundle them via choice into the required `B`.
This is genuine (non-`sorry`) Lean content: assembling the indexed existentials into one function
and discharging both the degree bound and the eval identity simultaneously. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **Bundling lemma (proven, kernel-clean).**  The per-coefficient curve-polynomial datum
`CurveCoeffPolys` yields the bundled `hcoeffPoly` existential the front door consumes: a single
`B : ℕ → Polynomial F` with `(B j).natDegree < k+1` for all `j < deg` and
`(P z).coeff j = (B j).eval z` on the good set. -/
theorem hcoeffPoly_witness_of_curveCoeffPolys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    (hCurvePolys : CurveCoeffPolys (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  -- For each index choose an interpolant if `j < deg`, otherwise `0`.
  refine ⟨fun j =>
      if h : j < deg then (hCurvePolys j h).choose else 0, ?_, ?_⟩
  · intro j hj
    simp only [hj, dif_pos]
    exact (hCurvePolys j hj).choose_spec.1
  · intro z hz j hj
    simp only [hj, dif_pos]
    exact (hCurvePolys j hj).choose_spec.2 z hz

/-! ## The old front-door output shape

`Section55CurveCoeffOutput` packages the literal output shape of the list-decoding branch: for
**every** candidate decoding `P` of the curve that is good on the good set (each `P z` of degree
`< deg` and within radius `δ`), the per-coefficient curve polynomials exist (`CurveCoeffPolys`).
This is exactly the front-door `hcoeffPoly` obligation, so it is not the canonical residual
input for the finished keystone path. The smaller current route is
`KeystoneAssembly.keystone_of_section5Inputs`, whose residual is the corrected
`Section5StrictDataFin` producer bundle.

Historically this capstone described the remaining §5 work as:

* `hMult` — the Guruswami–Sudan interpolant's multiplicity-vanishing at the centre
  (in-tree `ModifiedGuruswami.Q_multiplicity` / `gsQ_multiplicity`), the single genuine §5 datum;
* `hδ₀`  — the Johnson radius condition `δ ≤ δ₀` under which that multiplicity holds;
* degree facts (`d_H ≤ d_R ≤ D`, available in-tree from `weight_ξ_bound`/`hH`).

Those facts are now routed through smaller producer bundles elsewhere; this file keeps the old
output-shaped proposition only as a compatibility target for the front-door bundling lemmas. -/
def Section55CurveCoeffOutput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Prop :=
  ∀ P : F → Polynomial F,
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
    CurveCoeffPolys (k := k) (deg := deg) (domain := domain) (δ := δ) u P

/-! ## The capstone: `hcoeffPoly` from the old output-shaped target

This compatibility lemma confirms that the old output-shaped proposition is exactly enough to feed
the front-door `hcoeffPoly` hypothesis (Curves.lean:1214-1222). It should not be mistaken for the
canonical residual input; use `KeystoneAssembly.keystone_of_section5Inputs` for the smaller producer
interface. -/
omit [Nonempty ι] [DecidableEq ι] in
theorem hcoeffPoly_of_johnson_regime
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hSec55 : Section55CurveCoeffOutput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z := by
  intro P hP
  exact hcoeffPoly_witness_of_curveCoeffPolys u P (hSec55 P hP)

/-! ## End-to-end: `jointAgreement` through the front door

To confirm the capstone's conclusion is exactly the front-door `hcoeffPoly`, we feed it to
`ProximityGap.RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds` (Curves.lean:1199)
and obtain `jointAgreement`.  This type-checks the capstone against the *real* keystone
front door: every hypothesis other than `hcoeffPoly` is the standard probability-threshold
input the front door already takes (`hprob`, `hεsmall`, `hεlarge`), so the list-decoding
branch of Curves:1819 is, under
`Section55CurveCoeffOutput`, a front-door compatibility check. -/
omit [DecidableEq ι] in
theorem jointAgreement_of_johnson_regime
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{let z ← $ᵖ F}[
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hεsmall :
      (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain)
    (hεlarge :
      ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain)
    (hSec55 : Section55CurveCoeffOutput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) :=
  RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds
    (deg := deg) (domain := domain) (δ := δ) hk u hprob hεsmall hεlarge
    (fun P hP => hcoeffPoly_of_johnson_regime u hSec55 P hP)

end KeystoneCapstone

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys
#print axioms ArkLib.KeystoneCapstone.hcoeffPoly_of_johnson_regime
#print axioms ArkLib.KeystoneCapstone.jointAgreement_of_johnson_regime
