/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.ToyProblem.Definitions

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Extensions.Data.CodingTheory.Basic.Distance
import ArkLib.Extensions.Data.CodingTheory.Erasure
import ArkLib.Extensions.Data.CodingTheory.InterleavedCode

/-!
# Toy problem definitions (ABF26 §6)

Statement-layer definitions for the toy problem of ABF26 §6 — the small
protocol whose analysis motivates mutual correlated agreement (MCA) over
mere correlated agreement (CA), and which doubles as a textbook example of
the complexities of real list-decoding-based protocol analyses.

This file is the code-theoretic foundation:

* `ToyProblem.relation` — Definition 6.1, the toy problem relation
  `R_C^ℓ` over a code `C` and constraint shape `ℓ`, in an
  **existential-encoding** form: the encoder is chosen per instance and only
  required to map into `C`. This is strictly weaker than the paper's relation,
  which uses the code's fixed encoding (see the `relation` docstring).
* `ToyProblem.relaxedRelation` — Definition 6.3, the `δ`-relaxed version
  used as the soundness target (inherits the existential encoding).
* Definition 6.4 (erasure-correction predicate) is realised directly by
  `CodingTheory.SupportsErasureCorrection` in
  [`ArkLib/Data/CodingTheory/Erasure.lean`](../../Data/CodingTheory/Erasure.lean)
  (the predicate is generic across proof systems; use the in-tree name
  directly rather than a paper-shape wrapper).
* `ToyProblem.winningSet` — Definition 6.11, the set of "winning"
  challenges `γ` for the simplified IOR attack of §6.4 (existential encoding;
  for one row it ignores the constraint values, `mem_winningSet_iff_exists_agree`).
* `ToyProblem.relationFor`, `ToyProblem.relaxedRelationFor`, and
  `ToyProblem.winningSetFor` — the paper's fixed-encoding relations, for
  arguments that depend on the code's chosen encoder rather than only its
  image. The bridges to the existential forms are one-way, except at the zero
  constraint `v = 0` (see the section docstring below).

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

/-- **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`), in an
**existential-encoding** form that is strictly weaker than the paper's.

In the paper the code is an encoding map `C : F^k → (F^s)^n`, and `R_C^ℓ`
pairs an input `((v, μ), W)` with a message matrix `M` such that every row is
`W i = C(M i)` under **that fixed encoding** and `(M · v) i = μ i`. Here the
code is only a set `C ⊆ (ι → F)` (for compatibility with the rest of ArkLib's
coding-theory API), and the encoding is quantified **existentially, per
instance**: `relation C v μ W` holds iff there are a message matrix
`M : Fin ℓ → Fin k → F` and *some* `F`-linear
`encode : (Fin k → F) →ₗ[F] (ι → F)` with image contained in `C` such that

  * `W i = encode (M i)` for every row `i`, and
  * the linear constraint `(M · v) i = μ i` holds for every `i`.

The witness encoder is shared by the `ℓ` rows of one instance, but it need
not be the code's encoder, need not be injective or onto `C`, and may change
from one instance to the next. So this relation accepts every instance that
the fixed-encoding relation `relationFor encode` accepts when `encode` maps
into `C` (the relaxed form of this bridge is `relaxedRelationFor_imp`), and in
general strictly more:

  * over `F₃` with `k = 1`, one coordinate and `C = F₃`, the fixed identity
    encoding rejects `v = 1, μ = 1, W = 2` (the unique message `2` violates
    the constraint), but `encode m = 2 • m` with message `1` witnesses it here;
  * for a single row, a code closed under scalar multiplication, `k ≥ 2` and
    `v ≠ 0`, the constraint is vacuous: every codeword satisfies
    `relation C v μ` for **every** `μ`, by rank-one re-encoding
    (`relation_one_row_of_mem`).

Arguments that depend on the code's chosen encoder must use `relationFor`.
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
for soundness with respect to `δ`.

It inherits the existential encoding of `relation`, so it is weaker than the
paper's fixed-encoding `R̃_{C,δ}^ℓ`, which is `relaxedRelationFor`. -/
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

/-- **Definition 6.11 of [ABF26]** (winning set `Ω^{f_1, f_2}_{v, μ_1, μ_2}`),
over the existential-encoding `relaxedRelation`.

For the simplified IOR `T'[C, t]` of §6.4 (Construction 6.9), this is the
set of challenges `γ ∈ F` for which the "new instance" output by the
verifier — `(v, μ_1 + γ·μ_2, f_1 + γ·f_2)` — lies in the relaxed
relation `R̃_{C,δ}^1`. In the paper, where `R̃` uses the code's fixed
encoding, the soundness error of `T'` is `max_{x,y} |Ω^y_x| / |F|` over
inputs `(x, y)` whose original instance `(v, μ_1, μ_2)` violates
`R̃_{C,δ}^2`; the fixed-encoding winning set is `winningSetFor`.

With the existential encoding used here, the one-row relation does not see
the constraint values: for `k ≥ 2`, `v ≠ 0` and `C` closed under scalar
multiplication, `γ` wins exactly when the fold `f_1 + γ·f_2` is `δ`-close to
`C` (`mem_winningSet_iff_exists_agree`), whatever `μ_1, μ_2` are. The
supremum over existential-violating instances,
`ToyProblem.winningSetSoundness` in `ToyProblem/Metrics.lean`, is therefore
degenerate: it equals `1` at the KoalaBear leaderboard anchor
(`ArkLib.KoalaBearAttack.koalaIRS_soundnessError_eq_one`). -/
def winningSet {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F)
    (f₁ f₂ : ι → F) : Set F :=
  { γ | relaxedRelation (k := k) (ℓ := 1) C δ v
         (fun _ ↦ μ₁ + γ * μ₂)
         (fun _ j ↦ f₁ j + γ * f₂ j) }

/-! ### The existential encoding makes a single row's constraint vacuous

For one row, the per-instance encoder of `relation` can be chosen of rank one
through any codeword, so the linear constraint `⟨M 0, v⟩ = μ 0` no longer
restricts the word. These two lemmas record this weakness of the
existential-encoding language; their analogues for the fixed-encoding
`relationFor` / `winningSetFor` are false in general (for instance
`ArkLib.KoalaBearAttack.attackInstance_winningSetFor_eq_empty`). -/

omit [Fintype ι] in
/-- **One-row degeneracy of the existential encoding.** If `C` is closed under
scalar multiplication, `v j₀ ≠ 0` and `k` has a second index `j₁ ≠ j₀`, then
every codeword satisfies the one-row `relation C v μ`, for **every** constraint
value `μ`. The witness uses the message `x • e_{j₀} + e_{j₁}` with
`x = (μ 0 - v j₁) / v j₀` and the rank-one encoder `m ↦ m j₁ • W 0`. -/
theorem relation_one_row_of_mem {k : ℕ} {C : Set (ι → F)}
    (hC : ∀ (a : F) (c : ι → F), c ∈ C → a • c ∈ C)
    {v : Fin k → F} {j₀ j₁ : Fin k} (hj : j₁ ≠ j₀) (hv : v j₀ ≠ 0)
    (μ : Fin 1 → F) {W : Fin 1 → ι → F} (hW : W 0 ∈ C) :
    relation (ℓ := 1) C v μ W := by
  classical
  set x : F := (μ 0 - v j₁) / v j₀ with hx
  set m : Fin k → F := Pi.single j₀ x + Pi.single j₁ 1 with hm
  have hm₁ : m j₁ = 1 := by simp [hm, hj]
  have hmv : ∑ j, m j * v j = μ 0 := by
    simp only [hm, Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul,
      zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hx, div_mul_cancel₀ _ hv]
    ring
  refine ⟨fun _ ↦ m,
    ⟨(LinearMap.proj j₁ : (Fin k → F) →ₗ[F] F).smulRight (W 0), fun m' ↦ hC _ _ hW, ?_⟩, ?_⟩
  · intro i
    rw [Subsingleton.elim i 0, LinearMap.smulRight_apply, LinearMap.proj_apply]
    show W 0 = m j₁ • W 0
    rw [hm₁, one_smul]
  · intro i
    rw [Subsingleton.elim i 0]
    exact hmv

/-- **The existential one-row winning set ignores the constraint.** Under the
hypotheses of `relation_one_row_of_mem`, `γ` is winning exactly when the fold
`f₁ + γ • f₂` agrees with some codeword of `C` on a `(1 - δ)`-fraction of the
coordinates; the constraint values `μ₁, μ₂` play no role. In particular any
instance whose every fold is `δ`-close to `C` (e.g. `f₁, f₂ ∈ C` for a linear
`C`) has `winningSet = Set.univ`, whether or not it violates `relaxedRelation`. -/
theorem mem_winningSet_iff_exists_agree {k : ℕ} {C : Set (ι → F)}
    (hC : ∀ (a : F) (c : ι → F), c ∈ C → a • c ∈ C)
    {v : Fin k → F} {j₀ j₁ : Fin k} (hj : j₁ ≠ j₀) (hv : v j₀ ≠ 0)
    {δ : ℝ≥0} {μ₁ μ₂ : F} {f₁ f₂ : ι → F} {γ : F} :
    γ ∈ winningSet C δ v μ₁ μ₂ f₁ f₂ ↔
      ∃ c ∈ C, ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ j ∈ S, f₁ j + γ * f₂ j = c j := by
  constructor
  · rintro ⟨Wstar, ⟨M, ⟨enc, henc, hW⟩, -⟩, S, hS, hag⟩
    exact ⟨Wstar 0, by rw [hW 0]; exact henc _, S, hS, fun j hj ↦ hag 0 j hj⟩
  · rintro ⟨c, hc, S, hS, hag⟩
    exact ⟨fun _ ↦ c, relation_one_row_of_mem hC hj hv _ hc, S, hS, fun _ j hj ↦ hag j hj⟩

/-! ## Fixed-encoding variants (the paper's relations)

The `relation`/`relaxedRelation`/`winningSet` above quantify the encoding
**existentially** (`∃ encode, …`): it is chosen per instance and only required
to map into `C`. This is strictly more permissive than the paper's `R_C`, which
uses **the code's fixed encoding**: an adversary can satisfy the relaxed
relation at a target `(μ₁, μ₂)` by reparameterising the linear constraint
through a *different* linear encoding into `C` (for one row, a rank-one one;
see `relation_one_row_of_mem`). The `…For encode` variants below pin the
encoding to a given `encode`, so a violation step stated with them (no δ-close
codeword stack under `encode` meets the constraint) is the paper's.

The bridges between the two languages are **one-way**:

* a fixed-encoding witness is an existential one (`relaxedRelationFor_imp`,
  `winningSetFor_subset`). For a *fixed instance*, a lower bound on
  `|winningSetFor encode …|` is therefore a lower bound on `|winningSet C …|`,
  and an upper bound on `|winningSet C …|` bounds `|winningSetFor encode …|`;
* violation certificates transport only from the existential to the fixed
  language (`not_relaxedRelationFor_of_not_relaxedRelation`). An instance that
  violates `relaxedRelationFor encode` may satisfy `relaxedRelation C`, so an
  attack certified against the fixed-encoding relation is not thereby an attack
  in the existential language, and these lemmas transfer no bound between the
  two soundness suprema (over violating instances) in either direction;
* at the zero constraint `v = 0` the encoding is irrelevant: when
  `Set.range encode = C` the two languages coincide
  (`relaxedRelationFor_zero_iff`, `winningSetFor_zero_eq`). This is the regime
  of the correlated-agreement attack (ABF26 Lemma 6.13). -/

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

/-- **Violation transport (existential ⇒ fixed encoding).** An instance that
violates the existential relaxed relation also violates the fixed-encoding one,
for any encoder with image in `C`. The converse transport is false in general
(see the section docstring). -/
theorem not_relaxedRelationFor_of_not_relaxedRelation {k ℓ : ℕ} {C : Set (ι → F)}
    {encode : (Fin k → F) →ₗ[F] (ι → F)} (hC : ∀ m, encode m ∈ C)
    {δ : ℝ≥0} {v : Fin k → F} {μ : Fin ℓ → F} {W : Fin ℓ → ι → F}
    (h : ¬ relaxedRelation (ℓ := ℓ) C δ v μ W) :
    ¬ relaxedRelationFor (ℓ := ℓ) encode δ v μ W :=
  fun hFor ↦ h (relaxedRelationFor_imp hC hFor)

/-- **Exact bridge at the zero constraint.** With `v = 0` the linear constraint
does not involve the messages, so the choice of encoding is irrelevant: if
`encode` parametrizes `C` (`Set.range encode = C`), the fixed-encoding and
existential relaxed relations coincide. -/
theorem relaxedRelationFor_zero_iff {k ℓ : ℕ} {C : Set (ι → F)}
    {encode : (Fin k → F) →ₗ[F] (ι → F)} (hrange : Set.range encode = C)
    {δ : ℝ≥0} {μ : Fin ℓ → F} {W : Fin ℓ → ι → F} :
    relaxedRelationFor (ℓ := ℓ) encode δ 0 μ W ↔
      relaxedRelation (k := k) (ℓ := ℓ) C δ 0 μ W := by
  have hC : ∀ m, encode m ∈ C := fun m ↦ by rw [← hrange]; exact Set.mem_range_self m
  refine ⟨relaxedRelationFor_imp hC, ?_⟩
  rintro ⟨Wstar, ⟨M, ⟨enc', henc', hWeq⟩, hconstr⟩, S, hScard, hSag⟩
  have hpre : ∀ i, ∃ m, encode m = Wstar i := by
    intro i
    have hmem : Wstar i ∈ C := by rw [hWeq i]; exact henc' (M i)
    rw [← hrange] at hmem
    exact hmem
  choose M' hM' using hpre
  refine ⟨Wstar, ⟨M', fun i ↦ (hM' i).symm, fun i ↦ ?_⟩, S, hScard, hSag⟩
  simpa using hconstr i

/-- Winning-set form of `relaxedRelationFor_zero_iff`: at the zero constraint the
fixed-encoding and existential winning sets are equal when `Set.range encode = C`. -/
theorem winningSetFor_zero_eq {k : ℕ} {C : Set (ι → F)}
    {encode : (Fin k → F) →ₗ[F] (ι → F)} (hrange : Set.range encode = C)
    {δ : ℝ≥0} {μ₁ μ₂ : F} {f₁ f₂ : ι → F} :
    winningSetFor encode δ (0 : Fin k → F) μ₁ μ₂ f₁ f₂ =
      winningSet (k := k) C δ 0 μ₁ μ₂ f₁ f₂ := by
  ext γ
  exact relaxedRelationFor_zero_iff hrange

end ToyProblem
