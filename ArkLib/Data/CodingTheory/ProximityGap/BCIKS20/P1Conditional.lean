/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# (P1) CONDITIONAL UNLOCK — the structured weight invariant and the P1 collapse, given lift identity

This file closes the **(P1)** Hensel-numerator weight bound
`Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D` of BCIKS20 Claim A.2, *conditional on the (P2) lift
identity* `βHensel_lift_identity`.  It imports `HenselNumerator` plus the shared A.4 infrastructure
in `AlphaWeight`.

## The wall, restated (wave-5 analysis, recorded in `HenselNumerator.lean`)

`βHensel_succ_term_weight_le` is UNPROVABLE through the loose induction hypothesis
`Λ(β_l) ≤ (2l+1)·d·D` — even the per-term product factor `(2(k+1−i1)+Σλ)·d·D` overshoots.  The only
route is the paper's **structured invariant**

  `Λ_𝒪(βHensel l) ≤ 1 + (l+1)·Λ(W) + e_l·Λ(ξ)`,   `e_l = 2l−1` for `l ≥ 1`, `e_0 = 0`,

which wave 5 PROVES is itself *underivable from the (A.1) recursion alone*: the sub-additive weight
calculus forces a constant `Λ(W)^0 Λ(ξ)^0` contribution of `Σλ + (D−Σλ) = D`, whereas the structured
target's constant is `1`; the gap `D−1` is exactly the multiplicative cancellation
`β_t = α_t · W^{t+1} · ξ^{e_t}` with `Λ(α_t) = Λ(Y) = 1`, i.e. the content of the (P2) lift identity
("an easier way is to consider the weight of `α_t`", BCIKS20 line 4276).

## The weight-from-identity link, and where the gap REALLY is (Task 1)

The lift identity `embeddingOf𝒪Into𝕃 (βHensel t) = αGenuine t · W^{t+1} · ξ^{e_t}` lives in the
FIELD `𝕃 H`, whereas `Λ_𝒪` is the weight of the canonical `F[X][Y]`-representative of
`βHensel t ∈ 𝒪 H`
(`weight_Λ_over_𝒪 = weight_Λ ∘ canonicalRepOf𝒪`), an `𝒪`-intrinsic quantity, NOT an `𝕃`-invariant.

The genuine bridge: `W^{t+1} = embedding (W𝒪)^{t+1}` and `ξ^{e_t} = embedding ξ^{e_t}` are *already*
embeddings of `𝒪`-elements (`W𝒪`, `ClaimA2.ξ ∈ 𝒪 H`).  Hence the ENTIRE right-hand side is the
embedding of an `𝒪`-element **iff** `αGenuine t` is — and the identity says it equals
`embedding (βHensel t)`, so it is.  The one missing fact is precisely the genuine A.4 content:

  `αGenuine t = embedding a_t` for some `a_t ∈ 𝒪 H` with `Λ_𝒪(a_t) ≤ 1`
  (i.e. `Λ(α_t) = Λ(Y) = 1`).

GIVEN that (the carved hypothesis `AlphaGenuineRegularWeightLe`), we PROVE — via the *injectivity*
of `embeddingOf𝒪Into𝕃` (`embeddingOf𝒪Into𝕃_injective`) — the `𝒪`-LEVEL factorization

  `βHensel t = a_t · W𝒪^{t+1} · ξ^{e_t}`   in `𝒪 H`,

and then read off `Λ_𝒪(βHensel t) ≤ Λ_𝒪(a_t) + (t+1)Λ(W) + e_t·Λ(ξ)` by the PROVEN over-`𝒪` weight
calculus (`weight_Λ_over_𝒪_mul_le`, `_pow_le`, `_W`, `nsmul_withBot_le`) — so `hlift` and
injectivity are genuinely load-bearing, and the gap is reduced to the SHARP, minimal A.4 fact
`Λ(α_t) ≤ 1` (plus
`α_t` regular).  This is the precise, non-faked location of the residual.

## What this file proves (the three tasks)

1. **THE WEIGHT-FROM-IDENTITY LINK** — `βHensel_eq_alpha_mul_of_lift`: from `hlift` + the carved
   `α_t = embedding a_t` (regularity), the `𝒪`-level factorization `β_t = a_t·W𝒪^{t+1}·ξ^{e_t}`, via
   injectivity.  This is the genuine transport; `hlift` is consumed here.
2. **The STRUCTURED INVARIANT** — `βHensel_weight_structured`: `Λ_𝒪(β_l) ≤ 1+(l+1)Λ(W)+e_l·Λ(ξ)`,
   PROVEN from the factorization + the over-`𝒪` weight calculus + `Λ(a_l) ≤ 1`.
3. **(P1)** — `βHensel_weight_bound_of_lift`: `Λ_𝒪(β_t) ≤ (2t+1)·natDegreeY R·D`, PROVEN from the
   structured invariant via the wave-5 `structured_weight_collapse`
   (`= βHensel_weight_bound_of_structured_weight`).

Given the final w16 vanishing residual `FaaDiBrunoSuccSumZeroResidual`, the P2 compatibility
theorem `βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero` supplies the repaired lift identity
and (P1) auto-unlocks (`βHensel_weight_bound_unlocked`): instantiate `hlift` with that direct P2
capstone, supply the carved `α_t`-regularity, and the regime hypotheses.

NO `axiom`/`admit`/`native_decide`/`bv_decide`/`sorry`.  Audited in-file via `#print axioms`.
-/

set_option linter.style.longLine false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

section P1Conditional

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ### 0. Shared A.4 infrastructure — imported from `AlphaWeight`

`embeddingOf𝒪Into𝕃_W𝒪`, `AlphaGenuineRegularWeightLe`, `βHensel_eq_alpha_mul_of_lift`, and
`βHensel_weight_structured` were originally re-stated here verbatim. Now that both modules are
tracked and registered, those four declarations are supplied by the canonical superset
`AlphaWeight.lean` (imported above), which restates them identically and adds the `DivWeightLe`
equivalence and the sharp `t = 0` obstruction. This file keeps only the genuinely-unique conditional
(P1) assembly below (`βHensel_weight_bound_of_lift`, `…'`, and the auto-unlock witness
`βHensel_weight_bound_unlocked`), which resolve the shared names from that import. -/

/-! ### 3. (P1) the loose weight bound — from the structured invariant by the wave-5 collapse -/

/-- **(P1) Task 3 — the loose weight bound, conditional.**  From the structured invariant
`βHensel_weight_structured` (under the lift identity + carved A.4 link + ξ-weight regime), the loose
Claim-A.2 target

  `Λ_𝒪(βHensel t) ≤ (2t+1)·natDegreeY R · D`

follows by the proven `ℕ`-arithmetic collapse `structured_weight_collapse`
(`= βHensel_weight_bound_of_structured_weight`), under the paper's faithful regime
`2 ≤ d`, `dH ≤ d`, `Λ(W)+dH ≤ D`. -/
theorem βHensel_weight_bound_of_lift (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  -- Step A (Tasks 1+2): the structured invariant at order `t`.
  have hstructured := βHensel_weight_structured H x₀ R hHyp hH hDH hlift hα hξ t
  -- Step B (Task 3): collapse to the loose target via the proven wave-5 arithmetic.
  exact βHensel_weight_bound_of_structured_weight H x₀ R hHyp hH hdR2 hdHR hW t hstructured

/-- **(P1) from the concrete divisibility residual.**  This is the same
weight-bound entry point as `βHensel_weight_bound_of_lift`, but callers may now
supply the `𝒪`-level clearing-divisibility form `DivWeightLe`; the equivalence
`alphaWeight_iff_divWeight` converts it to the carved regularity form needed by
the structured-weight proof. -/
theorem βHensel_weight_bound_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
    (alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv
  exact βHensel_weight_bound_of_lift H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα hξ t

/-! ### 3′. Structured-prefix invariant compatibility wrappers -/

/-- Package the structured prefix invariant from carved alpha regularity and the full lift identity,
using the canonical `AlphaWeight` proof. -/
theorem βHenselStructuredWeightInvariant_of_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight H x₀ R hHyp hH
    hDH hlift hα hξ k

/-- Package the structured prefix invariant from carved alpha regularity and the full lift identity,
with the `ξ` side condition discharged. -/
theorem βHenselStructuredWeightInvariant_of_lift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_lift H x₀ R hHyp hH hDH hlift hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Package the structured prefix invariant from separated carved-alpha base/successor cases and
the full lift identity. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_cases
    H x₀ R hHyp hH hDH hlift h0 hsucc hξ k

/-- Package the structured prefix invariant from separated carved-alpha base/successor cases,
with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_alphaWeight_cases H x₀ R hHyp hH hDH
    hlift h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-- Package the structured prefix invariant directly from `DivWeightLe`, lift-free. -/
theorem βHenselStructuredWeightInvariant_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH
    hDH hdiv hξ k

/-- Package the structured prefix invariant directly from `DivWeightLe`, with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_of_divWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight' H x₀ R hHyp hH
    hDH hDRx0 hdR2 hdiv k

/-- Package the structured prefix invariant from normalized base/successor divisibility targets. -/
theorem βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
    H x₀ R hHyp hH hDH h0 hsucc hξ k

/-- Package the structured prefix invariant from normalized base/successor divisibility targets,
with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_of_normalized_divWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 h0 hsucc k

/-- Package the structured prefix invariant from carved alpha regularity and successor-order lift
identities; the zero-order lift is supplied by the proved base theorem. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift
    H x₀ R hHyp hH hDH hliftSucc hα hξ k

/-- Package the structured prefix invariant from carved alpha regularity and successor-order lift
identities, with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα k

/-- Package the structured prefix invariant from separated carved-alpha cases and successor-order
lift identities. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
    H x₀ R hHyp hH hDH hliftSucc h0 hsucc hξ k

/-- Package the structured prefix invariant from separated carved-alpha cases and successor-order
lift identities, with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift H x₀ R hHyp hH
    hDH hliftSucc h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) k

/-! ### 3″. Structured-prefix invariant auto-unlock wrappers -/

/-- Structured-prefix invariant unlocked by the Faà-di-Bruno successor residual. -/
theorem βHenselStructuredWeightInvariant_unlocked
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero t)
    hα k

/-- Structured-prefix invariant unlocked by the Faà-di-Bruno successor residual, from concrete
divisibility. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  let hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
    fun t => βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero t
  exact βHenselStructuredWeightInvariant_unlocked H x₀ R hHyp hH hDH hDRx0 hdR2 hzero
    ((alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv) k

/-- Structured-prefix invariant unlocked by the Faà-di-Bruno successor residual, from separated
carved-alpha base/successor cases. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked H x₀ R hHyp hH hDH hDRx0 hdR2 hzero
    (AlphaGenuineRegularWeightLe.of_cases H x₀ R hHyp hH D h0 hsucc) k

/-- Structured-prefix invariant unlocked by full P2 vanishing. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t) hα k

/-- Structured-prefix invariant unlocked by full P2 vanishing, from concrete divisibility. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  let hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
    fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t
  exact βHenselStructuredWeightInvariant_unlocked_of_fullVanishes H x₀ R hHyp hH hDH
    hDRx0 hdR2 hvan ((alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv) k

/-- Structured-prefix invariant unlocked by the restricted P2 match. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t) hα k

/-- Structured-prefix invariant unlocked by the restricted P2 match, from concrete divisibility. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  let hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
    fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t
  exact βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch H x₀ R hHyp hH hDH
    hDRx0 hdR2 hmatch ((alphaWeight_iff_divWeight H x₀ R hHyp hH D hlift).2 hdiv) k

/-! ### 4. The fully-assembled conditional (P1), and the auto-unlock witness

`weight_ξ_bound` (PROVEN in `RationalFunctions`) discharges `hξ` under its regime, and
`βHensel_lift_identity` (in-tree) discharges `hlift`.  The SOLE genuine residual is the carved A.4
link `hα` (`Λ(α_t) ≤ 1`, `α_t` regular). -/

/-- **(P1) discharging `hξ` via the PROVEN `weight_ξ_bound`.**  Under the `2 ≤ d` regime and the two
total-degree budgets of `weight_ξ_bound`, the ξ-weight hypothesis is automatic; so the conditional
(P1) needs only `hlift` + the carved A.4 link `hα`. -/
theorem βHensel_weight_bound_of_lift' (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_lift H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hα ?_ t
  exact ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0

/-- **(P1)** from separated carved-alpha base/successor cases and the full lift identity. -/
theorem βHensel_weight_bound_of_alphaWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_cases H x₀ R hHyp hH
    hDH hdR2 hdHR hW hlift h0 hsucc hξ t

/-- **(P1)** from separated carved-alpha base/successor cases, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_alphaWeight_cases' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight_cases H x₀ R hHyp hH hDH hdR2 hdHR hW
    hlift h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- **(P1), with `hξ` discharged, from the concrete divisibility residual.**
After `weight_ξ_bound`, the remaining P1 inputs are exactly the lift identity
and `DivWeightLe`. -/
theorem βHensel_weight_bound_of_divWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  refine βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW hlift hdiv ?_ t
  exact ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0

/-- **(P1) from carved alpha regularity using only successor-order lift identities.**
This is the `P1Conditional` compatibility wrapper for the successor-lift API exposed in
`AlphaWeight`: the zero-order lift is supplied by the proved base theorem, so callers only supply
the successor-order family. -/
theorem βHensel_weight_bound_of_alphaWeight_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift H x₀ R hHyp hH
    hDH hdR2 hdHR hW hliftSucc hα hξ t

/-- **(P1) from carved alpha regularity and successor-order lift identities, with `ξ`
discharged.** -/
theorem βHensel_weight_bound_of_alphaWeight_succLift' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift' H x₀ R hHyp hH
    hDH hDRx0 hdR2 hdHR hW hliftSucc hα t

/-- **(P1)** from separated carved-alpha cases and successor-order lift identities. -/
theorem βHensel_weight_bound_of_alphaWeight_cases_succLift (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_cases_succLift H x₀ R hHyp hH
    hDH hdR2 hdHR hW hliftSucc h0 hsucc hξ t

/-- **(P1)** from separated carved-alpha cases and successor-order lift identities, with `ξ`
discharged. -/
theorem βHensel_weight_bound_of_alphaWeight_cases_succLift' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_alphaWeight_cases_succLift H x₀ R hHyp hH hDH hdR2 hdHR hW
    hliftSucc h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- **P1 direct route from `DivWeightLe`, lift-free compatibility wrapper.**  This exposes the
direct `AlphaWeight` consumer from the `P1Conditional` namespace for callers that no longer need
to pass through the alpha/lift equivalence. -/
theorem βHensel_weight_bound_direct_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_divWeight H x₀ R hHyp hH hDH hdR2 hdHR hW
    hdiv hξ t

/-- **P1 direct route from normalized `DivWeightLe` targets, lift-free compatibility wrapper.** -/
theorem βHensel_weight_bound_direct_of_normalized_divWeight_cases (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_normalized_divWeight_cases H x₀ R hHyp hH
    hDH hdR2 hdHR hW h0 hsucc hξ t

/-- **P1 direct route from `DivWeightLe`, with `ξ` discharged, lift-free compatibility wrapper.** -/
theorem βHensel_weight_bound_direct_of_divWeight' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0
    hdR2 hdHR hW hdiv t

/-- **P1 direct route from normalized `DivWeightLe` targets, with `ξ` discharged.** -/
theorem βHensel_weight_bound_direct_of_normalized_divWeight_cases' (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_normalized_divWeight_cases' H x₀ R hHyp hH
    hDH hDRx0 hdR2 hdHR hW h0 hsucc t

/-- **P1 direct unlocked route from normalized divisibility witnesses.**
This is the most local P1 front door for the current normalized #138 target: once the base and
successor `𝒪`-factor witnesses are supplied, the already-proved ξ bound discharges the remaining
weight side condition and no lift/P2 hypothesis is needed. -/
theorem βHensel_weight_bound_unlocked_of_normalized_divWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_direct_of_normalized_divWeight_cases' H x₀ R hHyp hH
    hDH hDRx0 hdR2 hdHR hW h0 hsucc t

/-- **AUTO-UNLOCK witness.**  Given the explicit w16 vanishing residual, the `hlift` hypothesis is
discharged by the direct P2 compatibility theorem
`βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero`.  This lemma exhibits that discharge:
feeding that theorem for `hlift`, the conditional (P1) needs ONLY the carved A.4 link `hα`
(`Λ(α_t) ≤ 1`) plus the paper's faithful regime hypotheses. -/
theorem βHensel_weight_bound_unlocked (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero t)
    hα t

/-- **AUTO-UNLOCK witness from concrete divisibility.**  This is the
`DivWeightLe` form of `βHensel_weight_bound_unlocked`: the Faà-di-Bruno
successor residual supplies the lift identity through the direct P2 compatibility theorem, and
the remaining A.4 input is the concrete `𝒪`-level clearing-divisibility residual. -/
theorem βHensel_weight_bound_unlocked_of_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => βHensel_lift_identity_of_faaDiBruno_succ_sum_eq_zero H x₀ R hHyp hzero t)
    hdiv t

/-- **AUTO-UNLOCK witness from separated carved-alpha cases.**  The Faà-di-Bruno successor
residual supplies the lift identity; the A.4 regularity input is provided as separate base and
successor cases. -/
theorem βHensel_weight_bound_unlocked_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hzero
    (AlphaGenuineRegularWeightLe.of_cases H x₀ R hHyp hH D h0 hsucc) t

/-- **P1 weight bound unlocked by full P2 vanishing.**
This consumes the sharper `FaaDiBrunoFullSumVanishes` endpoint, whose P2 capstone already provides
the lift identity needed by `βHensel_weight_bound_of_lift'`. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t) hα t

/-- **P1 weight bound unlocked by full P2 vanishing, from concrete
divisibility.**  This is the full-vanishing version of
`βHensel_weight_bound_of_divWeight'`. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 t) hdiv t

/-- **P1 weight bound unlocked by the restricted P2 match.**
`RestrictedFaaDiBrunoMatch` is the smallest carved P2 bridge currently exposed by `P2Vanish`;
given it, the P1 collapse no longer needs to mention the legacy successor-sum residual. -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_lift' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t) hα t

/-- **P1 weight bound unlocked by the restricted P2 match, from concrete
divisibility.** -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch_divWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_divWeight' H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 t) hdiv t

end P1Conditional

end BCIKS20.HenselNumerator

-- Axiom audit: every proof-carrying declaration in this file depends on exactly the three standard
-- axioms `[propext, Classical.choice, Quot.sound]` (no `sorry`/`admit`/`axiom`/`native_decide`).
#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_W𝒪
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_eq_alpha_mul_of_lift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alpha_eq_embedding_of_fact
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_structured
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_lift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_lift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_divWeight'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_lift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_lift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_divWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_direct_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_direct_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_direct_of_divWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_direct_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch_divWeight
