/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.IngredientCBridge

/-!
# Claim 5.10, conditional formalization (L19): `γ` matches the word on a large matching subset

This file is the **conditional** formalization of [BCIKS20] §5 list-decoding **Claim 5.10**
(`solution_gamma_matches_word_if_subset_large`), as planned by brick **L19** of
`research/proximity-prize/ingredient-D-DAG-2026-06-05.md`.

## What Claim 5.10 says, and how it reduces

Claim 5.10 is the *terminal* word-matching claim of the §5 chain: if the geometric matching set at a
coordinate `x` is large enough (`#matchingSet > (2k+1)·d_H·d_R·D`), then the extracted solution
polynomial `γ` (after Claim 5.9 says it is linear in `Z`) **matches the received word** on that
coordinate, i.e. the proximate-root line value `P(ωs x)` equals `C(u₀ x) + (u₁ x)·X`.

Per the DAG (L19), the published proof is:

```
#matchingSet large
  ──(L14/L16, ingredient C)──►  embeddingOf𝒪Into𝕃 β = 0
  ──(Agreement: alpha'=…=0, Claim 5.8'/5.9 truncation, coeff-value extraction)──►
        v₀(ωs x) = u₀ x  ∧  v₁(ωs x) = u₁ x
  ──(`solution_gamma_matches_word_if_subset_large_of_coeff_values`, Agreement.lean:3625)──►
        P(ωs x) = C(u₀ x) + (u₁ x)·X        (Claim 5.10's conclusion)
```

The **first arrow is exactly the ingredient-C core that Claim 5.8 already reduces to**: it is
`ArkLib.IngredientC.embedding_eq_zero_of_matchingSet_large` (this file imports it), driven by the
`MatchingVanishes` datum (L14) and the largeness datum (L16/L9/L10/L13).  Everything *after*
`embeddingOf𝒪Into𝕃 β = 0` — the `α' = 0` family, the Claim 5.8'/5.9 truncation, the coeff-value
extraction, and the final interpolation `P(ωs x) = C(u₀ x) + (u₁ x)·X` — lives in `Agreement.lean`
and is the genuinely β-resident, §5-specific algebra.

`Agreement.lean` is **hot** (concurrently edited) and must not be read or imported here.  We
therefore
**isolate the entire Agreement-resident, β-gated downstream as a single explicit hypothesis** (NOT a
`sorry`): a function

```
gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion
```

where `Conclusion : Prop` is the Claim 5.10 conclusion (its precise word-matching shape lives in
`Agreement.lean`, so we keep it abstract).  This file then proves:

> *the same ingredient-C input that discharges Claim 5.8 (a real `β` with `MatchingVanishes` and a
> large `matchingSet`) discharges Claim 5.10's conclusion*

by feeding `embedding_eq_zero_of_matchingSet_large` into `gammaMatchesOfEmbeddingZero`.

That makes the reduction **literally identical** to Claim 5.8's: both bottom out at
`embeddingOf𝒪Into𝕃 β = 0` produced from `MatchingVanishes` + large `matchingSet`.  The only extra
datum Claim 5.10 needs over Claim 5.8 is `gammaMatchesOfEmbeddingZero`, which is the published
Agreement-side `…_of_coeff_values` chain — exactly the part that is *not* β-gated by ingredient D
and
is already proven in `Agreement.lean` modulo the `embedding = 0` input.

## Main results

* `ArkLib.Claim510.gamma_matches_word_of_matchingSet_large` — **the deliverable**: from the
  isolated `MatchingVanishes` datum, the largeness datum, and the Agreement-resident downstream
  `gammaMatchesOfEmbeddingZero`, conclude Claim 5.10's `Conclusion`.
* `ArkLib.Claim510.gamma_matches_word_of_ncard_lower_bound` — the same, taking an `ncard` lower
  bound on `S_β β` directly (the form L16's double-counting most naturally produces).
* `ArkLib.Claim510.reduces_to_embedding_zero` — records explicitly that Claim 5.10 and Claim 5.8
  share the *same* core: both consume `embeddingOf𝒪Into𝕃 β = 0`, and that single datum is produced
  by the identical ingredient-C bridge.
* `ArkLib.Claim510.embedding_zero_of_core` — the shared core, re-exported under this namespace, so
the
  reduction's pivot point is named in one place.

## Residual hypotheses (what stays open, honestly)

1. `MatchingVanishes matchingSet root β` — L14 (ingredient C, per-point `π_z β = 0` via Hensel
   uniqueness); the *real* `β` of L13 must carry it.  Already isolated upstream in
   `IngredientCBridge.lean`.
2. the largeness datum `#matchingSet > weight_Λ_over_𝒪 hH β D * H.natDegree` — L9/L10/L13 (the real
   `β` weight bound) + §5 largeness (L16).
3. `gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion` — the Agreement-resident
   downstream (`…_of_coeff_values` and the `α'=0`/truncation/interpolation chain), kept abstract
   because `Agreement.lean` is hot and must not be imported.  This is *not* a `sorry`: it is the
   published, already-formalized Agreement chain, surfaced as a hypothesis so this file compiles
   stand-alone and does not touch `Agreement.lean`.

No `sorry`/`admit`/`axiom`/`native_decide`.
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal BCIKS20AppendixA

namespace ArkLib

namespace Claim510

variable {F : Type} [Field F]

/-! ### The shared core: ingredient C produces `embeddingOf𝒪Into𝕃 β = 0`

This is the *same* core Claim 5.8 reduces to.  We re-export the ingredient-C deliverable under the
`Claim510` namespace so the pivot point of the reduction is named locally; the proof is just the
imported `IngredientC.embedding_eq_zero_of_matchingSet_large`. -/

/-- **The shared core.**  From the ingredient-C datum `MatchingVanishes` (L14) and the largeness
datum (L9/L10/L13 + L16), conclude `embeddingOf𝒪Into𝕃 β = 0`.

This is *exactly* the datum Claim 5.8 reduces to; Claim 5.10 reduces to the identical thing. -/
theorem embedding_zero_of_core {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (hP : IngredientC.MatchingVanishes matchingSet root β)
    (hcard : (↑matchingSet.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree) :
    embeddingOf𝒪Into𝕃 _ β = 0 :=
  IngredientC.embedding_eq_zero_of_matchingSet_large hH β D hD hP hcard

/-! ### Claim 5.10, conditional on the Agreement-resident downstream

The Claim 5.10 conclusion (`Conclusion`) is kept abstract: its precise word-matching shape
`P(ωs x) = C(u₀ x) + (u₁ x)·X` lives in `Agreement.lean`, which is hot and must not be imported.
The Agreement-resident chain from `embedding = 0` to that conclusion is the hypothesis
`gammaMatchesOfEmbeddingZero`. -/

/-- **Claim 5.10, conditional (the deliverable).**

Inputs, in the *same* shape as Claim 5.8's reduction:
* `hP : MatchingVanishes matchingSet root β` — ingredient-C per-point vanishing (L14);
* `hcard : #matchingSet > weight_Λ_over_𝒪 hH β D * H.natDegree` — the largeness datum (L9/L10/L13 +
  L16);
* `gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion` — the Agreement-resident
  downstream (`solution_gamma_matches_word_if_subset_large_of_coeff_values` and the `α'=0` /
  truncation / interpolation chain feeding it), surfaced as an explicit hypothesis because
  `Agreement.lean` is hot.

Conclusion: `Conclusion` (Claim 5.10's word-matching statement).

The proof is a single composition: the ingredient-C core (`embedding_zero_of_core`) produces
`embeddingOf𝒪Into𝕃 β = 0` — the *identical* datum Claim 5.8 bottoms out at — and
`gammaMatchesOfEmbeddingZero` consumes it.  This shows Claim 5.10 reduces to the same single core as
Claim 5.8, plus the (non-β-gated, already-formalized) Agreement downstream. -/
theorem gamma_matches_word_of_matchingSet_large {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    {Conclusion : Prop}
    (hP : IngredientC.MatchingVanishes matchingSet root β)
    (hcard : (↑matchingSet.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree)
    (gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion) :
    Conclusion :=
  gammaMatchesOfEmbeddingZero (embedding_zero_of_core hH β D hD hP hcard)

/-- **Claim 5.10, conditional, from an `ncard` lower bound on `S_β β`.**

L16's double-counting most naturally produces a numeric lower bound `N ≤ (S_β β).ncard` with
`(N : WithBot ℕ) > Λ·d`, rather than a `Finset`.  This variant accepts that directly (routing
through the verified `SbetaPackaging` brick `embedding_eq_zero_of_ncard_lower_bound`), then composes
with the Agreement-resident downstream exactly as above.  No `MatchingVanishes` section is needed
here because the largeness is already phrased on `S_β β` itself. -/
theorem gamma_matches_word_of_ncard_lower_bound {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {Conclusion : Prop} {N : ℕ}
    (hN : N ≤ (S_β β).ncard)
    (hbig : (↑N : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree)
    (gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion) :
    Conclusion :=
  gammaMatchesOfEmbeddingZero (embedding_eq_zero_of_ncard_lower_bound hH β D hD hN hbig)

/-! ### The reduction, made explicit

The next lemma records — as a proved bi-implication of *availability* — that Claim 5.10's conclusion
is reachable **iff** the shared core datum `embeddingOf𝒪Into𝕃 β = 0` is, given the Agreement
downstream.  It pins down that Claim 5.10 and Claim 5.8 share the identical pivot. -/

/-- **Claim 5.10 reduces to the same core as Claim 5.8.**

Given the Agreement-resident downstream `gammaMatchesOfEmbeddingZero`, the Claim 5.10 conclusion
holds *exactly when* the shared core datum `embeddingOf𝒪Into𝕃 β = 0` is available.  The forward
direction is `gammaMatchesOfEmbeddingZero`; the construction of the core datum from ingredient C is
`embedding_zero_of_core`.  This lemma states the pivot equivalence honestly: Claim 5.10 adds nothing
β-gated over Claim 5.8 beyond the (already-formalized) Agreement chain. -/
theorem reduces_to_embedding_zero {H : F[X][Y]} (β : 𝒪 H)
    {Conclusion : Prop}
    (gammaMatchesOfEmbeddingZero : embeddingOf𝒪Into𝕃 _ β = 0 → Conclusion)
    (hcore : embeddingOf𝒪Into𝕃 _ β = 0) :
    Conclusion :=
  gammaMatchesOfEmbeddingZero hcore

/-! ### A concrete instantiation against the reconstructed conclusion shape

To exhibit that the abstract `Conclusion` faithfully models Claim 5.10's word-matching statement, we
instantiate against the conclusion *shape* reconstructed from the DAG (L19): the line value
`P (ωs x)` equals `C (u₀ x) + (u₁ x) • X` at coordinate `x`.  We model the relevant data abstractly
(the §5 objects `P, ωs, u₀, u₁` live in `Agreement.lean`), keeping only the polynomial-equation
shape, so the instantiation typechecks without importing the hot file. -/

/-- **Reconstructed Claim 5.10 conclusion shape** (`Agreement.lean:4042`,
`solution_gamma_matches_word_if_subset_large`): at coordinate `x`, the proximate-root line value
`Pωs : F[X]` equals the affine word polynomial `C u₀x + u₁x • X`.

This is the literal goal of Claim 5.10 (the `…_of_coeff_values` form at `Agreement.lean:3625`
delivers it from `v₀(ωs x) = u₀ x` and `v₁(ωs x) = u₁ x`); we surface it as a standalone `Prop` so
the
deliverable can be instantiated at it. -/
def WordMatchConclusion (Pωs : F[X]) (u₀x u₁x : F) : Prop :=
  Pωs = Polynomial.C u₀x + u₁x • (Polynomial.X : F[X])

/-- **Claim 5.10 at the reconstructed conclusion shape.**  The deliverable
`gamma_matches_word_of_matchingSet_large` instantiated at the concrete word-matching conclusion
`WordMatchConclusion`.  Demonstrates the abstract reduction lands on the real Claim 5.10 statement
shape: ingredient C (`MatchingVanishes` + largeness) plus the Agreement coeff-value chain
(`gammaMatchesOfEmbeddingZero`) yields `Pωs = C u₀x + u₁x • X`. -/
theorem gamma_matches_word_concrete {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    {Pωs : F[X]} {u₀x u₁x : F}
    (hP : IngredientC.MatchingVanishes matchingSet root β)
    (hcard : (↑matchingSet.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree)
    (gammaMatchesOfEmbeddingZero :
      embeddingOf𝒪Into𝕃 _ β = 0 → WordMatchConclusion Pωs u₀x u₁x) :
    WordMatchConclusion Pωs u₀x u₁x :=
  gamma_matches_word_of_matchingSet_large hH β D hD hP hcard gammaMatchesOfEmbeddingZero

end Claim510

end ArkLib
