/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Erasure
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Toy problem definitions (ABF26 §6)

Statement-layer definitions for the toy problem of ABF26 §6 — the small
protocol whose analysis motivates mutual correlated agreement (MCA) over
mere correlated agreement (CA), and which doubles as a textbook example of
the complexities of real list-decoding-based protocol analyses.

This file is the code-theoretic foundation:

* `ToyProblem.relation` — Definition 6.1, the toy problem relation
  `R_C^ℓ` over a code `C` and constraint shape `ℓ`.
* `ToyProblem.relaxedRelation` — Definition 6.3, the `δ`-relaxed version
  used as the soundness target.
* Definition 6.4 (erasure-correction predicate) is realised directly by
  `CodingTheory.SupportsErasureCorrection` in
  [`ArkLib/Data/CodingTheory/Erasure.lean`](../../Data/CodingTheory/Erasure.lean)
  (the predicate is generic across proof systems; use the in-tree name
  directly rather than a paper-shape wrapper).
* `ToyProblem.winningSet` — Definition 6.11, the set of "winning"
  challenges `γ` for the simplified IOR attack of §6.4.
* `ToyProblem.relationFor`, `ToyProblem.relaxedRelationFor`, and
  `ToyProblem.winningSetFor` — fixed-encoding variants used when the
  paper argument depends on the code's chosen encoder rather than only
  its image.

Protocol-level items (Construction 6.2, Lemmas 6.6 / 6.8, Construction
6.9, Lemma 6.10) live in `ToyProblem/Spec/General.lean` and are stated
over ArkLib's `OracleReduction/` machinery, following the conventions
of `ProofSystem/Fri/Spec/` and `ProofSystem/Sumcheck/Spec/`. Soundness
bounds (L6.5, L6.12, L6.13) live in `ToyProblem/SoundnessBounds.lean`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal

variable {ι F : Type*} [Fintype ι] [Field F]

/-- **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`).

Given a base code `C ⊆ (ι → F)` (the paper writes `C : F^k → (F^s)^n`
for an `F`-additive code; we use the Set-form for compatibility with the
rest of ArkLib's coding-theory API), a constraint shape `(ℓ, k)`, a
linear-constraint vector `v : Fin k → F`, and constraint values
`μ : Fin ℓ → F`, the toy problem relation pairs an input
`((v, μ), W)`, where `W : Fin ℓ → ι → F` is a stack of `ℓ` words,
with the witness "underlying message matrix" `M : Fin ℓ → Fin k → F`
such that:

  * each row `W i` is a codeword of `C`, with `M i` an associated
    pre-image under some `F`-linear encoding,
  * the linear constraint `(M · v) i = μ i` holds for every `i`.

For the linear-code special case, the pre-image `M i` is unique (the
chosen encoding is a bijection from `Fin k → F` onto `C`); the
existence form below subsumes both linear and general `F`-additive
codes.

This is what the paper calls "constrained codes". -/
def relation {k ℓ : ℕ} (C : Set (ι → F))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ M : Fin ℓ → Fin k → F,
    (∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ i, W i = encode (M i)) ∧
    ∀ i, ∑ j, M i j * v j = μ i

/-- **Definition 6.3 of [ABF26]** (relaxed toy problem relation
`R̃_{C,δ}^ℓ`).

The relaxed relation only requires that the input word stack `W` is
`δ`-close (in interleaved Hamming distance) to a valid instance `W*`
of `relation C v μ`. This is both necessary (the verifier in the IOR
only reads a few entries of `W`) and sufficient (for downstream uses)
for soundness with respect to `δ`. -/
def relaxedRelation {k ℓ : ℕ} (C : Set (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ Wstar : Fin ℓ → ι → F,
    relation C v μ Wstar ∧
      -- Interleaved Hamming distance between the two word stacks is at
      -- most `δ`: at least `(1 - δ) · |ι|` coordinates agree on every
      -- row.
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i, ∀ j ∈ S, W i j = Wstar i j

-- Paper Definition 6.4 (erasure-correction predicate) is realised by
-- `CodingTheory.SupportsErasureCorrection` directly; use that name (no
-- paper-shape alias wrapper — see Definitions.lean module docstring).

/-- **Definition 6.11 of [ABF26]** (winning set `Ω^{f_1, f_2}_{v, μ_1, μ_2}`).

For the simplified IOR `T'[C, t]` of §6.4 (Construction 6.9), this is the
set of challenges `γ ∈ F` for which the "new instance" output by the
verifier — `(v, μ_1 + γ·μ_2, f_1 + γ·f_2)` — lies in the relaxed
relation `R̃_{C,δ}^1`. The soundness error of `T'` is then exactly
`max_{x,y} |Ω^y_x| / |F|` over inputs `(x, y)` whose original instance
`(v, μ_1, μ_2)` violates `R̃_{C,δ}^2`. -/
def winningSet {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F)
    (f₁ f₂ : ι → F) : Set F :=
  { γ | relaxedRelation (k := k) (ℓ := 1) C δ v
         (fun _ ↦ μ₁ + γ * μ₂)
         (fun _ j ↦ f₁ j + γ * f₂ j) }

/-! ## Fixed-encoding variants (for the §6.4.1 list-decoding attack)

The `relation`/`relaxedRelation`/`winningSet` above quantify the encoding
**existentially** (`∃ encode, …`), which faithfully covers general `F`-additive
codes. For the §6.4.1 list-decoding attack
(`ToyProblem.simplified_iop_soundness_listDecoding_lb`) this existential is *too
permissive*: an adversary can satisfy the relaxed relation at a target `(μ₁,μ₂)`
by reparameterising the linear constraint through a *different* linear encoding
with the same image. The paper's `R_C` uses **the code's fixed encoding**; the
`…For encode` variants below pin it down, so the attack's violation step (no
δ-close codeword stack under `encode` meets the constraint) is faithful and
provable. A fixed-encoding witness is in particular an existential one
(`relaxedRelationFor_imp`, `winningSetFor_subset`), so quantitative winning-set
bounds transfer up to `winningSet`. -/

/-- **Fixed-encoding toy relation** (cf. `relation`). The §6.1 relation `R_C^ℓ`
with the encoding pinned to a given `F`-linear `encode` (the code's encoding;
codewords are exactly `encode`'s image). -/
def relationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → F))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ M : Fin ℓ → Fin k → F, (∀ i, W i = encode (M i)) ∧ ∀ i, ∑ j, M i j * v j = μ i

/-- **Fixed-encoding relaxed relation** (cf. `relaxedRelation`). -/
def relaxedRelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ Wstar : Fin ℓ → ι → F, relationFor encode v μ Wstar ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i, ∀ j ∈ S, W i j = Wstar i j

/-- **Fixed-encoding winning set** (cf. `winningSet`). -/
def winningSetFor {k : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F) : Set F :=
  { γ | relaxedRelationFor (ℓ := 1) encode δ v
         (fun _ ↦ μ₁ + γ * μ₂) (fun _ j ↦ f₁ j + γ * f₂ j) }

/-- A fixed-encoding relaxed witness is in particular an existential-encoding one,
provided the encoding's image lies in `C`. -/
theorem relaxedRelationFor_imp {k ℓ : ℕ} {C : Set (ι → F)}
    {encode : (Fin k → F) →ₗ[F] (ι → F)} (hC : ∀ m, encode m ∈ C)
    {δ : ℝ≥0} {v : Fin k → F} {μ : Fin ℓ → F} {W : Fin ℓ → ι → F} :
    relaxedRelationFor (ℓ := ℓ) encode δ v μ W → relaxedRelation (ℓ := ℓ) C δ v μ W := by
  rintro ⟨Wstar, ⟨M, hWeq, hconstr⟩, S, hScard, hSag⟩
  exact ⟨Wstar, ⟨M, ⟨encode, hC, hWeq⟩, hconstr⟩, S, hScard, hSag⟩

/-- `winningSetFor encode ⊆ winningSet C` when `encode`'s image lies in `C`. -/
theorem winningSetFor_subset {k : ℕ} {C : Set (ι → F)}
    {encode : (Fin k → F) →ₗ[F] (ι → F)} (hC : ∀ m, encode m ∈ C)
    {δ : ℝ≥0} {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → F} :
    winningSetFor encode δ v μ₁ μ₂ f₁ f₂ ⊆ winningSet C δ v μ₁ μ₂ f₁ f₂ :=
  fun _ hγ ↦ relaxedRelationFor_imp hC hγ

end ToyProblem
