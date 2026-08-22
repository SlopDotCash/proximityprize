/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.ToMathlib.BetaRecursion

/-!
# The `L13` strengthening — the in-tree numerator routed through `betaRec`

This file is the upper layer of the `L13` architectural fix.  `RationalFunctionsCore.lean` holds the
BCIKS20 Appendix-A machinery; `RationalFunctions.lean` re-exports it plus the *legacy* numerator
tail (`β_regular`/`β`/`α`/`γ`), keeping the historical public surface and import environment
unchanged so
the heavy function-field consumers compile untouched.  `BetaRecursion.lean` now imports *Core*, so
the historical import cycle `BetaRecursion → RationalFunctions` is gone, and *this* file — importing
both `RationalFunctions` and `BetaRecursion` — finally supplies the honest replacement for the
opaque legacy numerator.

## Why the legacy `β` is opaque (recap of `BetaIdentify` route (a))

The legacy `β_regular` asserts *only* the weight upper bound `Λ(β) ≤ (2t+1)·d_R·D`, proved by the
trivial witness `fun _ => ⟨0, by simp⟩`.  Hence `β R t = (β_regular …).choose` is opaque: `0`,
`betaRec … t`, and infinitely many others all satisfy the weight inequality, so
`embeddingOf𝒪Into𝕃 H (β R t) = embeddingOf𝒪Into𝕃 H (betaRec … t)` is **unprovable** from it — this
is exactly the `BetaIdentify.BetaEmbedEq` residual, which every §5 consumer threads as a
*hypothesis*.

## What is delivered here (all kernel-clean)

* `β_regular_strong` — the existence statement whose *defining property pins the embedding*:
  `∃ b, embeddingOf𝒪Into𝕃 H b = embeddingOf𝒪Into𝕃 H (betaRec … t)`.  The witness is `betaRec … t`
  itself, so the property holds by `rfl` and (by injectivity of the embedding) determines `b`.
* `β_strong` — the honest in-tree numerator, `Exists.choose` of `β_regular_strong`,
  genuinely routing through `betaRec`.
* `beta_strong_embedEq` — `choose_spec`: `embeddingOf𝒪Into𝕃 H (β_strong …) = embeddingOf𝒪Into𝕃 H
  (betaRec … t)` **with no hypothesis**.  This is the numerator-identification residual *supplied by
  the definition* — the `BetaEmbedEq` of `BetaIdentify`, now a theorem rather than a hypothesis.
* `beta_strong_eq_betaRec` — the element-level upgrade `β_strong … t = betaRec … t` via injectivity.
* `α_strong` — the strong Hensel-lift coefficient, with denominators identical to `α`/`αFromBeta`.

No `sorry`/`axiom`/`native_decide`; the `#print axioms` block shows only
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]

/-- **The strong numerator-existence statement (L13).**  There exists a regular element whose image
in the function field `𝕃 H` *equals* the image of the genuine App-A.4 recursion `betaRec … t`.  The
witness is `betaRec … t` itself, so this is honest: the pinning property `embeddingOf𝒪Into𝕃 H b =
embeddingOf𝒪Into𝕃 H (betaRec … t)` holds by `rfl` on the witness, and (because
`embeddingOf𝒪Into𝕃 H` is injective for `0 < H.natDegree`) it determines the element uniquely — in
sharp contrast to the weight-only legacy `β_regular`, which `0` and infinitely many others
satisfy. -/
lemma β_regular_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    ∃ b : 𝒪 H,
      embeddingOf𝒪Into𝕃 H b
        = embeddingOf𝒪Into𝕃 H (ArkLib.betaRec x₀ R H hHyp Bcoeff t) :=
  ⟨ArkLib.betaRec x₀ R H hHyp Bcoeff t, rfl⟩

/-- **The strong in-tree numerator (L13 drop-in for `β`).**  Unlike the legacy `β`, this routes
through `betaRec`: it is `Exists.choose` of `β_regular_strong`, whose defining property *pins the
embedding* to `betaRec`'s.  This is the honest in-tree numerator the App-A.4 lift identity
targets. -/
noncomputable def β_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝒪 H :=
  (β_regular_strong x₀ R H hHyp Bcoeff t).choose

/-- **The embedding of `β_strong` is pinned to `betaRec` (L13, residual supplied by definition).**
This is `Exists.choose_spec` of `β_regular_strong`: the in-tree strong numerator's image in `𝕃 H`
*equals* the genuine recursion's image, with **no hypothesis** beyond the standing setup.  This is
exactly the embedding-level numerator-identification residual that `BetaIdentify.BetaEmbedEq`
carried
as a *hypothesis* for the legacy `β`; here it is a *theorem*. -/
@[simp] theorem beta_strong_embedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (β_strong x₀ R H hHyp Bcoeff t)
      = embeddingOf𝒪Into𝕃 H (ArkLib.betaRec x₀ R H hHyp Bcoeff t) :=
  (β_regular_strong x₀ R H hHyp Bcoeff t).choose_spec

/-- **`β_strong = betaRec` as `𝒪`-elements** (for `0 < H.natDegree`).  Because the embedding
`embeddingOf𝒪Into𝕃 H` is injective, the pinned embedding identity `beta_strong_embedEq` upgrades to
an element-level identity: the strong in-tree numerator *is* the App-A.4 recursion. -/
theorem beta_strong_eq_betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (hH : 0 < H.natDegree) (t : ℕ) :
    β_strong x₀ R H hHyp Bcoeff t = ArkLib.betaRec x₀ R H hHyp Bcoeff t :=
  embeddingOf𝒪Into𝕃_injective hH (beta_strong_embedEq x₀ R H hHyp Bcoeff t)

/-- **The strong Hensel-lift coefficient `α_strong`**, built from `β_strong` (the L13-honest
analogue of `α`).  Its denominators are *identical* to those of `α`/`αFromBeta`; the numerator is
the strong (betaRec-routed) one.  Because `beta_strong_embedEq` pins the numerator's embedding,
`α_strong` is definitionally the `betaRec`-built coefficient `BetaToCurveCoeffPolys.αFromBeta`. -/
noncomputable def α_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β_strong x₀ R H hHyp Bcoeff t) /
    (W ^ (t + 1) *
      (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ henselDenominatorExponent t)

end ClaimA2
end
end BCIKS20AppendixA

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms BCIKS20AppendixA.ClaimA2.β_regular_strong
#print axioms BCIKS20AppendixA.ClaimA2.β_strong
#print axioms BCIKS20AppendixA.ClaimA2.beta_strong_embedEq
#print axioms BCIKS20AppendixA.ClaimA2.beta_strong_eq_betaRec
#print axioms BCIKS20AppendixA.ClaimA2.α_strong
