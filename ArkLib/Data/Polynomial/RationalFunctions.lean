/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.RationalFunctionsCore

/-!
# Definitions and Theorems about Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

This file is the public surface of the BCIKS20 Appendix-A function-field development.  The bulk of
the machinery (`H_tilde`, `𝕃`, `𝒪`, `embeddingOf𝒪Into𝕃`, `regularElms_set`, the weight calculus
`weight_Λ`/`weight_Λ_over_𝒪`, `Lemma_A_1`, the Claim-A.2 element `ξ`, …) now lives verbatim in the
sibling `RationalFunctionsCore.lean`; this file `import`s it and re-exports every name through the
same `BCIKS20AppendixA`/`BCIKS20AppendixA.ClaimA2` namespaces, adding only the legacy numerator
tail (`β_regular`/`β`/`α`/`γ`/`α'`/`γ'`), so every downstream consumer that `import`s
`RationalFunctions` continues to see the *full, unchanged* surface (and the *unchanged* import
environment — this file imports nothing beyond `Core`).

## The `L13` architectural split (this file)

The split exists for one reason: the genuine App-A.4 numerator recursion `ArkLib.betaRec`
(`BetaRecursion.lean`) needs only the `Core` machinery, so it `import`s `RationalFunctionsCore`
directly.  That breaks the historical import cycle `BetaRecursion → RationalFunctions → …`.  The
honest, `betaRec`-routed numerator (`β_strong`, with the embedding *pinned* to `betaRec`'s and the
numerator-identification residual discharged *by definition*) is therefore built one layer up in
`ArkLib/Data/Polynomial/RationalFunctionsStrong.lean`, which `import`s both this file and
`BetaRecursion`.  Keeping `betaRec` out of *this* file's import set is deliberate: the heavy
function-field consumers (`HenselNumerator`, `GammaGenuine`, …) that `import RationalFunctions`
retain the exact instance environment they had before the split.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

## Main Definitions

-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling `RationalFunctionsCore.lean`.
set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (0 < H.natDegree)]

/-- Denominator exponent used in the Claim-A.2 Hensel numerator formula. For `t = 0`, the
subtraction is truncated to zero. -/
def henselDenominatorExponent (t : ℕ) : ℕ :=
  if t = 0 then 0 else 2 * t - 1

lemma henselDenominatorExponent_zero : henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

lemma henselDenominatorExponent_succ (t : ℕ) :
    henselDenominatorExponent (t + 1) = 2 * (t + 1) - 1 := by
  simp [henselDenominatorExponent]

/-- There exist regular elements `β` with the *weight upper bound* of Claim A.2 of
Appendix A.4 of [BCIKS20].

**Honesty note (the §5 frontier).** This lemma asserts ONLY the weight upper bound
`Λ(β) ≤ (2t+1)·d_R·D`, which is satisfied vacuously by `β = 0` — and that is exactly
the witness used here (`fun _ => ⟨0, by simp⟩`). It is therefore a true but
*under-specified* statement: the `β` it produces is NOT the genuine recursive
Hensel-lift numerator of [BCIKS20] (A.1), and carries no functional relation to
`R`/`x₀`. The genuine numerator additionally satisfies the lift identity
`embeddingOf𝒪Into𝕃 (β t) = α_t · W^{t+1} · ξ^{e_t}` that Claims 5.8/5.8'/5.9 read off
(`α' t = 0 ⟺ embedding (β t) = 0` via `Lemma_A_1`).

**Status update (L13 / ingredient D).** The genuine recursive numerator *has now been
constructed*: `ArkLib.betaRec` (`ArkLib/ToMathlib/BetaRecursion.lean`) is the App-A.4
recursion (A.1), kernel-clean, defined+terminating, landing in `𝒪 H`, with the weight
bound `betaRec_weight_le_concrete ≤ (2t+1)·d_R·D` (`BetaWeightInduction` +
`BetaWeightCollapse`) and the ingredient-C vanishing `betaRec_embedding_eq_zero_of_
matchingSet_large` (`BetaMatchingVanishes`).  The end-to-end §5 capsule
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` derives the front-door
per-coefficient datum from `betaRec` (β load-bearing), and
`ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec`
wires that genuine β into the keystone `ProximityGap.correlatedAgreement_affine_curves`.

**Superseded (the L13 architectural fix).** `β_regular`/`β` below are kept *verbatim* for
downstream compatibility, but are now **superseded** by `β_regular_strong`/`β_strong`
(`ArkLib/Data/Polynomial/RationalFunctionsStrong.lean`): with `RationalFunctionsCore.lean`
carrying the machinery, `BetaRecursion.lean` imports *Core* (not this file), so the historical
import cycle is gone and the strong numerator there genuinely routes through `betaRec` with the
embedding pinned (`beta_strong_embedEq`).

**F1 caveat.** The in-tree `γ` below uses `PowerSeries.subst` of the shift series
`X ↦ X − x₀`, which is only a valid substitution when `x₀ = 0`
(`HasSubst (shiftSeries x₀ H) ↔ x₀ = 0`, kernel-proven in
`ArkLib/ToMathlib/SubstFieldCaveat.lean`).  The keystone wiring carries this as the
explicit hypothesis `hsubst`/`hγ` (automatic in the centred case); the off-centre fix is
to recenter via `PowerSeries.mk (α …)` rather than `subst`.

See `research/proximity-prize/dispositions/ingredient-D-{plan,result}.md` for the full
construction spec. -/
lemma β_regular (R : F[X][X][Y])
    (H : F[X][Y]) [_H_irreducible : Fact (Irreducible H)]
                [_H_natDegree_pos : Fact (0 < H.natDegree)]
                (hH : 0 < H.natDegree)
                {D : ℕ} (_hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H,
      weight_Λ_over_𝒪 hH β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D :=
  fun _ => ⟨0, by simp⟩

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  if hH : 0 < H.natDegree then
    (β_regular R H hH (Nat.le_refl _) t).choose
  else
    0

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) /
    (W ^ (t + 1) *
      (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t)

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H hHyp))

/-- The coefficient sequence obtained from a candidate sequence of regular numerators. -/
noncomputable def alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (βseq t) /
    (W ^ (t + 1) *
      (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t)

/-- The power series induced by a candidate sequence of regular numerators. -/
noncomputable def gammaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst)
    (PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq))

/-- Coefficients in `F[Z][X]` evaluated as power series over the function field: `Z` is sent to
the function-field coefficient embedding, and `X` is sent to the power-series variable. -/
noncomputable def liftCoeffToPowerSeries (H : F[X][Y]) :
    F[X][X] →+* PowerSeries (𝕃 H) :=
  Polynomial.eval₂RingHom (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
    PowerSeries.X

/-- Evaluation of the trivariate polynomial `R(X,Y,Z)` at a power series `Γ` for the `Y`
variable, with the `X` variable interpreted as the power-series variable and `Z` interpreted in
the function field of `H`. -/
noncomputable def evalRAtPowerSeries (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) : PowerSeries (𝕃 H) :=
  Polynomial.eval₂ (liftCoeffToPowerSeries H) Γ R

/-- A numerator sequence has the semantic content required by Claim A.2: it gives the Hensel
lift starting at `T / W`, and the induced power series is a root of `R(X,Y,Z)`. This is a
statement shape only; the current in-file `β` placeholder below intentionally does not claim it. -/
def IsHenselNumeratorSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) : Prop :=
  alphaOfNumerators x₀ R H hHyp βseq 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries H R (gammaOfNumerators x₀ R H hHyp βseq) = 0

/-- The semantic-wrapper coefficient sequence specializes to the in-file `α` when its
candidate numerator sequence is the in-file `β`. -/
@[simp]
theorem alphaOfNumerators_beta (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    alphaOfNumerators x₀ R H hHyp (β R) = α x₀ R H hHyp :=
  rfl

/-- The semantic-wrapper power series specializes to the in-file `γ` when its candidate
numerator sequence is the in-file `β`. -/
@[simp]
theorem gammaOfNumerators_beta (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    gammaOfNumerators x₀ R H hHyp (β R) = γ x₀ R H hHyp :=
  rfl

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

end ClaimA2
end
end BCIKS20AppendixA
