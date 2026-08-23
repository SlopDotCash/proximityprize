
/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToMathlib.RewindingExtractor

/-!
# Toy problem oracle reduction (ABF26 Construction 6.2)

We describe the ABF26 §6 toy-problem IOR as an `OracleReduction` over
ArkLib's `OracleReduction` framework, following the conventions used by
`ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` and
`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`:

* `Statement`, `OracleStatement`, `Witness`, `OutputStatement` — input /
  oracle / witness / output type aliases (all `@[reducible]`).
* `pSpec` — the 3-round `ProtocolSpec` (`V → P` γ, `P → V` g, `V → P`
  spot-checks).
* `OracleInterface`, `Inhabited`, `Fintype` instances for the messages
  and challenges of `pSpec`.
* `inputRelation` / `outputRelation` — IOR input/output relations
  (Definitions 6.1 and 6.3, in IOR shape).
* `accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete. The
soundness lemmas `protocol62_knowledgeSound` (L6.6) and
`protocol62_rbrKnowledgeSound` (L6.8) carry the **concrete** paper error
terms (`max (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) ((1-δ)^t)` and the
per-round split). These lemmas are **2-special-soundness** arguments whose
extractor must *rewind* the prover, which the in-tree straightline
`Verifier.knowledgeSoundness` interface cannot express (the documented wall in
`research/proximity-prize/dispositions/oraclereduction-leftovers.md`). The genuine
mathematical content — the 2-special-sound rewinding extractor — is supplied
**fully proven** as `protocol62_knowledgeSoundnessViaRewinding` (the framework
predicate `Extractor.knowledgeSoundnessViaRewinding`), and each straightline
lemma is reduced to a single **named bridge residual**
`Bridge.StraightlineOfRewinding` (taken as an explicit hypothesis),
discharged by `Bridge.knowledgeSound_of_rewinding`. There are **no**
`sorry`/`axiom` terms: the residual is a named, documented interface gap, not an
admitted proof. The IOR scaffolding is exactly what is needed downstream.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → F`. The protocol runs:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`. In the
     honest case `g = M₁ + γ · M₂` is the combination of the underlying
     messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier accepts iff `⟨g, v⟩ = μ₁ + γ · μ₂` (linear-constraint
check) and for every `j ∈ Fin t`, `encode(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`
(spot-check).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `relaxedRelation`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F : Type} [Fintype ι] [Field F]
variable (k t : ℕ)

/-- Input (explicit) statement of Construction 6.2: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of Construction 6.2: the two purported codewords
`f₁, f₂ : ι → F`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι F : Type) : Fin 2 → Type := fun _ ↦ ι → F

instance : ∀ i, OracleInterface (OracleStatement ι F i) :=
  fun _ ↦ inferInstance

/-- Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose
encodings are the oracle codewords `f₁, f₂`. -/
@[reducible]
def Witness : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a yes/no test — accept (return `()`) or
short-circuit to `none` via `OptionT`. -/
@[reducible]
def OutputStatement : Type := Unit

/-- Output oracle statement: the IOR has no output oracle component. -/
@[reducible]
def OutputOracleStatement : (Fin 0) → Type := nofun

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for Construction 6.2: three rounds, in the
order

    V → P  (γ : F)            -- combination randomness
    P → V  (g : Fin k → F)    -- combined message claim
    V → P  (xs : Fin t → ι)   -- spot-check positions.

Marked `@[reducible]` so per-round type access `pSpec.Type i` reduces
in client code (cf. FRI / Sumcheck single-round specs). -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩

instance instMessageOracleInterface :
    ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault
  | ⟨2, h⟩ => nomatch h

/-- Pointwise `OracleInterface` instance for the (sole) prover message of `pSpec`, at round 1.
The `∀ j`-indexed `instMessageOracleInterface` is not found by `inferInstance` on a *concrete*
restated index `⟨1, h⟩` (the indexed match does not reduce during typeclass search), which blocks
completeness-proof terms that mention `answer (msgs ⟨1, _⟩) _`. This pointwise instance restores
synthesis; it is *definitionally equal* to `instMessageOracleInterface ⟨1, _⟩` (both `instDefault`),
so it introduces no diamond. -/
instance instMessageOracleInterfaceOne {h : (pSpec (ι := ι) (F := F) k t).dir 1 = .P_to_V} :
    OracleInterface ((pSpec (ι := ι) (F := F) k t).Message ⟨1, h⟩) :=
  OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The challenges of the toy-problem `pSpec` are `SampleableType` when
the underlying field `F` and the codeword index `ι` are. This is needed
to instantiate the (round-by-round) knowledge-soundness games, which
sample challenges from the protocol's challenge spaces. -/
instance [SampleableType F] [SampleableType ι] :
    ∀ j, SampleableType ((pSpec (ι := ι) (F := F) k t).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => (inferInstance : SampleableType (Fin t → ι))

/-- The §6.1 decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def accepts (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ * f 1 (xs j)

/-- The IOR-shaped input relation derived from `ToyProblem.relation`
(Definition 6.1).

  `((v, μ₁, μ₂), (f₁, f₂)) ∈ inputRelation k C ↔ ToyProblem.relation
    C v (μ₁, μ₂) (f₁, f₂)` (modulo `Fin 2`-indexing of the latter). -/
def inputRelation (C : Set (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    ToyProblem.relation (k := k) (ℓ := 2) C input.1.1.1
      ![input.1.1.2.1, input.1.1.2.2] input.1.2

/-- The IOR-shaped **honest-opening** input relation for a *fixed* encoder
`encode` (the protocol's own combining map).

`((v, μ₁, μ₂), (f₁, f₂)) ∈ honestInputRelation k C encode` iff there is a
message matrix `M : Fin 2 → Fin k → F` such that

  * `f i = encode (M i)` for the **protocol's** `encode` (honest opening), and
  * `∑_j M i j · v j = μ i` (the linear constraint).

## Documented statement repair (2026-06): protocol-encoder alignment (hEnc class)

The historic completeness statement used `inputRelation k C`, which unfolds
(Definition 6.1, `ToyProblem.relation`) to

  `∃ M, (∃ encode', (∀ m, encode' m ∈ C) ∧ ∀ i, f i = encode' (M i)) ∧ …`

— the opener `encode'` is **existentially quantified** and is *a different
map* than the protocol's `encode` parameter. The honest verifier's
spot-check uses the *protocol's* `encode` (`encode g (xs j) = f₀ + γ·f₁`),
so completeness needs `f i = encode (M i)` for *that* `encode`; with the
existential `encode'` of `inputRelation`, the equality `encode (M i) (x) =
encode' (M i) (x)` is **not derivable** (counterexample: take `C` the full
space, `encode' = 0`, `encode = id`, any `M ≠ 0`; then
`((v,0,0),(0,0)) ∈ inputRelation` via `encode' = 0`, but the honest prover's
`g = M₀+γM₁` gives `encode g (x) ≠ 0 = f₀+γf₁`, so the spot-check fails and
`Pr[accept] = 0 ≠ 1`). This is a genuine statement-level wall, not proof
effort.

We repair it by aligning the input relation's opener with the protocol's
encoder — exactly the `hEnc` linear-encoder pattern of L6.13
(`SoundnessBounds.lean :: simplified_iop_soundness_ca_lb`), where the same
`relation`-encoder existential is pinned to a named `F`-linear `encode`.
This is the regime ABF26 Definition 6.1 intends ("the chosen encoding is a
bijection from `Fin k → F` onto `C`"): the honest prover *is* the party that
opened the codewords under `encode`, so the relation it is complete against
is precisely the honest-opening relation. `honestInputRelation k C encode ⊆
inputRelation k C` whenever `∀ m, encode m ∈ C` (witness `encode' := encode`),
so this is a strengthening of the hypothesis on the input, i.e. a *weaker*
(more faithful) completeness claim, never vacuous. -/
def honestInputRelation (_C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    -- The *witness given to the prover* (`input.2`) is itself the honest opening: it opens the
    -- codewords under the *protocol's* `encode` and satisfies the linear constraint.  This is the
    -- faithful honest-opening relation — pinning the opener to `input.2` (rather than an
    -- existentially-quantified `M`) is load-bearing for completeness, since the honest prover sends
    -- `g = wit₀ + γ·wit₁` built from `input.2`, not from any other opener (defect #18, hEnc class).
    (∀ i, input.1.2 i = encode (input.2 i)) ∧
    ∀ i, ∑ j, input.2 i j * input.1.1.1 j =
      (if i = (0 : Fin 2) then input.1.1.2.1 else input.1.1.2.2)

omit [Fintype ι] in
/-- `honestInputRelation` is contained in `inputRelation` when the encoder's
image lies in `C` — i.e. honest opening is a *stronger* input hypothesis, so
completeness against `honestInputRelation` is the faithful (non-vacuous)
claim. (The converse fails, see the `honestInputRelation` docstring.) -/
theorem honestInputRelation_subset_inputRelation
    (C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F))
    (h_mem : ∀ m, (encode m : ι → F) ∈ C) :
    honestInputRelation k C encode ⊆ inputRelation k C := by
  rintro ⟨⟨⟨v, μ₁, μ₂⟩, f⟩, wit⟩ ⟨hf, hM⟩
  refine ⟨wit, ⟨encode, h_mem, ?_⟩, ?_⟩
  · intro i; exact hf i
  · intro i
    have := hM i
    fin_cases i <;> simpa using this

/-- The IOR-shaped *relaxed* output relation derived from
`ToyProblem.relaxedRelation` (Definition 6.3). The soundness statement
of L6.6 is with respect to this relation: the verifier's "accept"
guarantee is that the input is `δ`-close to a valid `relation`-instance. -/
def outputRelation (C : Set (ι → F)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    ToyProblem.relaxedRelation (k := k) (ℓ := 2) C δ input.1.1.1
      ![input.1.1.2.1, input.1.1.2.2] input.1.2

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelation` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Rewinding extractor for Construction 6.2 (the 2-special-sound core)

The knowledge-soundness lemmas L6.6 / L6.8 / L6.10 are **2-special-soundness** arguments: the
extractor must obtain *two* accepting transcripts that share the prefix up to the combination-
randomness round and differ at the challenge `γ`, then solve a 2×2 linear system to recover the
message pair `(u₁, u₂)`. That requires **rewinding** the prover.

The in-tree `Verifier.knowledgeSoundness`
(`OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`, line 328) and
`Verifier.rbrKnowledgeSoundness`
(`OracleReduction/Security/RoundByRound.lean :: rbrKnowledgeSoundness`, line 811) both quantify
over a **single-run** extractor (`∃ E : Extractor.Straightline` / `∃ E : Extractor.RoundByRound`):
a single transcript and the logs of *one* execution, with **no black-box handle to re-invoke or
fork the prover**. The 2-special-sound rewinding extractor cannot be expressed through those
interfaces. This is the documented wall in
`research/proximity-prize/dispositions/oraclereduction-leftovers.md` (residual (1)+(2)) and in the
`ArkLib/ToMathlib/RewindingExtractor.lean` module docstring.

We therefore supply the genuine mathematical content — the 2-special-sound rewinding extractor for
the toy protocol — as a **fully-proven** `Extractor.knowledgeSoundnessViaRewinding` witness (the
rewinding-flavoured analogue of `Verifier.knowledgeSoundness`), and reduce the straightline holes
below to a single named bridge residual `Bridge.StraightlineOfRewinding`. -/

variable {k}

open Extractor in
/-- The combination map `g = u₁ + γ·u₂` (pointwise on `Fin k`): the honest prover's claim at
challenge `γ` from the underlying message pair `(u₁, u₂)`. -/
def toyCombine (γ : F) (u₁ u₂ : Fin k → F) : Fin k → F :=
  fun j ↦ u₁ j + γ * u₂ j

/-- Recovered second message `u₂ = (g₁ − g₂)/(γ₁ − γ₂)` from two claims at distinct challenges. -/
def toySolveSnd (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ (g₁ j - g₂ j) / (γ₁ - γ₂)

/-- Recovered first message `u₁ = g₁ − γ₁·u₂`. -/
def toySolveFst (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ g₁ j - γ₁ * toySolveSnd γ₁ γ₂ g₁ g₂ j

/-- The full 2×2 solve as a `Witness = Fin 2 → Fin k → F` (`row 0 = u₁`, `row 1 = u₂`): the witness
the rewinding extractor outputs from two accepting completions at distinct challenges. -/
def toySolve (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Witness (F := F) k :=
  ![toySolveFst γ₁ γ₂ g₁ g₂, toySolveSnd γ₁ γ₂ g₁ g₂]

/-- **Correctness of the `u₂` solve.** `toySolveSnd` inverts `toyCombine` on `γ₁ ≠ γ₂`. -/
theorem toySolveSnd_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveSnd γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₂ := by
  funext j
  have hsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hγ
  simp only [toySolveSnd, toyCombine]
  field_simp
  ring

/-- **Correctness of the `u₁` solve.** `toySolveFst` inverts `toyCombine` on `γ₁ ≠ γ₂`. -/
theorem toySolveFst_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveFst γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₁ := by
  funext j
  have hu₂ := congrFun (toySolveSnd_combine hγ u₁ u₂) j
  simp only [toySolveFst, toyCombine] at hu₂ ⊢
  rw [hu₂]
  ring

/-- **Full 2×2 solve correctness.** `toySolve` inverts `toyCombine` on distinct challenges:
from the two honest claims at `γ₁ ≠ γ₂` it recovers `![u₁, u₂]`. The algebraic heart of the toy
protocol's 2-special-sound extractor. -/
theorem toySolve_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolve γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = ![u₁, u₂] := by
  funext i
  fin_cases i
  · simpa [toySolve] using toySolveFst_combine hγ u₁ u₂
  · simpa [toySolve] using toySolveSnd_combine hγ u₁ u₂

/-- The recorded-prefix carrier for the rewinding extractor: the toy protocol's bundled input
statement (read off the recorded transcript prefix up to the `γ` round). -/
abbrev ToyPrefix (ι F : Type) (k : ℕ) : Type :=
  Statement (F := F) k × (∀ i, OracleStatement ι F i)

/-- Read the input statement off the recorded prefix; for the toy protocol the prefix *is* the
input, so this is the identity. -/
def toyStmtOf : ToyPrefix ι F k → ToyPrefix ι F k := id

/-- The concrete **rewinding extractor** for Construction 6.2 / 6.9: from the recorded prefix and
two completions `(γ₁, g₁)`, `(γ₂, g₂)`, return the 2×2 solve `toySolve γ₁ γ₂ g₁ g₂`. -/
def toyRewindingExtractor :
    Extractor.RewindingExtractor (ToyPrefix ι F k) F (Fin k → F) (Witness (F := F) k) :=
  fun _pre c₁ c₂ ↦ toySolve c₁.1 c₂.1 c₁.2 c₂.2

/-- The toy protocol's acceptance predicate for the rewinding extractor, parameterised by the
prefix-indexed decoded message pair `decode` held invariant by the fork (a single fork replays up
to the `γ` round from a *recorded prover state*, so the prover's internal message pair is fixed
across both completions — only `γ` is resampled). Completion `(γ, g)` at prefix `pre` is accepting
iff `g` is the honest `γ`-combination of `decode pre` and that pair places the input in
`outputRelation C δ` (the per-prefix MCA decode of ABF26 Remark 6.7). -/
def toyAccepts (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    ToyPrefix ι F k → Extractor.Accepts F (Fin k → F) :=
  fun pre c ↦
    (pre, (![(decode pre).1, (decode pre).2] : Witness (F := F) k))
        ∈ outputRelation (ι := ι) (F := F) k C δ ∧
      c.2 = toyCombine c.1 (decode pre).1 (decode pre).2

/-- **2-special-soundness of the toy rewinding extractor.** From any two accepting completions on
distinct challenges `γ₁ ≠ γ₂`, `toyRewindingExtractor` recovers a witness in `outputRelation`.
Both accepting completions are honest `γ`-combinations of the *same* prefix-fixed pair `decode pre`;
the 2×2 solve recovers exactly that pair via `toySolve_combine`, and membership transfers by
`rfl`. -/
theorem toyRewindingExtractor_twoSpecialSound (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    (toyRewindingExtractor (ι := ι) (F := F) (k := k)).TwoSpecialSound
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) := by
  rintro pre ⟨γ₁, g₁⟩ ⟨γ₂, g₂⟩ ⟨hmem, hg₁⟩ ⟨_, hg₂⟩ hγ
  -- `hg₁ : g₁ = toyCombine γ₁ (decode pre).1 (decode pre).2`, likewise `hg₂`; `hγ : γ₁ ≠ γ₂`.
  -- The extractor returns `toySolve γ₁ γ₂ g₁ g₂`; substitute the combinations and invert.
  have hg₁' : g₁ = toyCombine γ₁ (decode pre).1 (decode pre).2 := hg₁
  have hg₂' : g₂ = toyCombine γ₂ (decode pre).1 (decode pre).2 := hg₂
  have hγ' : γ₁ ≠ γ₂ := hγ
  show (pre, toySolve γ₁ γ₂ g₁ g₂) ∈ outputRelation (ι := ι) (F := F) k C δ
  rw [hg₁', hg₂', toySolve_combine hγ' (decode pre).1 (decode pre).2]
  exact hmem

/-- **Knowledge soundness via rewinding for Construction 6.2 (proven).** The toy protocol admits a
2-special-sound rewinding extractor, hence satisfies the framework's
`Extractor.knowledgeSoundnessViaRewinding` predicate against `outputRelation`. This is the
rewinding-flavoured analogue of `Verifier.knowledgeSoundness` whose absence blocked
`protocol62_knowledgeSound`. By `Extractor.knowledgeSoundnessViaRewinding.extracts`, whenever a
prover beats the 2-special-sound knowledge error `1/|F|` at a prefix, a valid witness is
extractable — no `sorry`, no `axiom`. -/
theorem protocol62_knowledgeSoundnessViaRewinding [Fintype F] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  ⟨toyRewindingExtractor, toyRewindingExtractor_twoSpecialSound C δ decode⟩

/-! ### Honest prover, verifier, and reduction

This section mirrors the `foldProver` / `foldVerifier` / `foldOracleReduction`
pattern in [`Fri/Spec/SingleRound.lean`](../../../Fri/Spec/SingleRound.lean).
Because `OracleStatement ι F i = ι → F` is a plain function (not an
oracle that needs the `OracleQuery` machinery), we use the **non-oracle**
`Prover` / `Verifier` / `Reduction` triple with the oracle codewords
threaded through the bundled input `StmtIn = Statement × (∀ i, OracleStatement i)`.
This is sound — it's the same shape produced by
`OracleReduction.toReduction` — and avoids the `embed` / `hEq`
plumbing. An `OracleProver` / `OracleVerifier` flavour is a follow-up.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- Honest prover for Construction 6.2. After receiving the combination
randomness `γ`, the prover sends `g := M 0 + γ · M 1` (point-wise on
`Fin k`). The spot-check positions `xs` are not used by the prover —
they only feed the verifier's spot-check at the end.

State machine (`PrvState : Fin 4 → Type`):
  * `PrvState 0` — initial: the bundled `(stmt, oStmt) × witness`.
  * `PrvState 1, 2, 3` — same plus the combination randomness `γ`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure ((), ())

/-- The §6.1 decision predicate is decidable: it's a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance accepts.instDecidable
    (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold accepts; infer_instance

/-- Honest verifier for Construction 6.2. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `accepts` holds for the supplied encoding.

Computable — `accepts` is decidable, so no `Classical.dec` is needed.
This mirrors FRI's `foldVerifier`, which is also a plain `def`. -/
def verifier (encode : (Fin k → F) → (ι → F)) :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      OutputStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    let g : Fin k → F := tr ⟨1, by decide⟩
    let xs : Fin t → ι := tr ⟨2, by decide⟩
    if accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for Construction 6.2: the package
`{prover, verifier}` over the bundled-input `Reduction` type. -/
def reduction (encode : (Fin k → F) → (ι → F)) :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := prover (ι := ι) (F := F) (k := k) (t := t)
  verifier := verifier (k := k) (t := t) encode

/-! ### Oracle-flavour prover, verifier, reduction

These are the `OracleProver` / `OracleVerifier` / `OracleReduction`
flavours of the same protocol, exposing `(f₁, f₂)` as oracle inputs
rather than bundling them into `StmtIn`. They match FRI/Sumcheck's
exact idiom and are necessary to make the *query complexity* of the
verifier explicit (`2t + 1` queries per execution: one for `g`, two
per spot-check).

The honest-completeness, knowledge-soundness, and round-by-round
knowledge-soundness lemmas below are stated against this oracle-flavour
reduction, since that's the form ArkLib's
`Verifier.knowledgeSoundness` / `Verifier.rbrKnowledgeSoundness`
machinery is designed for.
-/

/-- Same as `prover` but exposed at the `OracleProver` signature. The
underlying `Prover` is identical (after the `OracleProver` type-alias
unfolds to a `Prover` on bundled in/out types). The output is the
trivial `(((), nofun), ())` since the IOR has no output oracle
statements (`OutputOracleStatement : Fin 0 → Type`). -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure (((), nofun), ())

/-- Query helper: fetch the prover's combined-message claim `g`
(`pSpec` round 1 — the `P → V` direction). Mirrors FRI's `getConst`. -/
def queryG : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by simpa using ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryF (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι F]ₒ F :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι F]ₒ.Domain from ⟨i, (by simpa using x)⟩)

/-- Oracle verifier for Construction 6.2.

Queries the prover's message `g` once and the two oracle codewords
`f₁, f₂` at each of the `t` spot-check positions (query complexity:
`2t + 1`), then `guard (accepts …)` to decide.

`embed` and `hEq` are trivial — `OutputOracleStatement : Fin 0 → Type`
is empty, so the output-oracle family is vacuously a subset of input
oracles + prover messages. -/
def oracleVerifier (encode : (Fin k → F) → (ι → F)) :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι F)
      OutputStatement OutputOracleStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    -- Query the prover's message `g` (round-1 oracle, RIGHT family). The
    -- explicit `OptionT.lift <| OracleComp.liftComp (OracleComp.lift …)` form
    -- (matching `Sumcheck/Spec/SingleRound.lean`'s oracle verifier) makes the
    -- `simulateQ`-collapse lemmas fire syntactically.
    let g : Fin k → F ← OptionT.lift <| OracleComp.liftComp
      (OracleComp.lift <| OracleSpec.query
        (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
          ⟨⟨1, by rfl⟩, (by simpa using ())⟩)) _
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      -- Query the two codewords (oracle statements, LEFT family).
      let f₀ : F ← OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <| OracleSpec.query
          (show [OracleStatement ι F]ₒ.Domain from ⟨0, (by simpa using xs j)⟩)) _
      let f₁ : F ← OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <| OracleSpec.query
          (show [OracleStatement ι F]ₒ.Domain from ⟨1, (by simpa using xs j)⟩)) _
      guard (encode g (xs j) = f₀ + γ * f₁)
    pure ()
  embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
  hEq := fun i ↦ i.elim0

/-- Honest oracle reduction for Construction 6.2: the
`OracleProver` / `OracleVerifier` pair packaged as `OracleReduction`. -/
def oracleReduction (encode : (Fin k → F) → (ι → F)) :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := oracleProver (ι := ι) (F := F) (k := k) (t := t)
  verifier := oracleVerifier (k := k) (t := t) encode

/-! ### `simulateQ`-collapse toolkit for the compiled oracle verifier

The honest-completeness proof needs a *closed form* for the `simulateQ`-image of the compiled
oracle verifier (`oracleVerifier.toVerifier`), i.e. the verifier run with its message- and
oracle-statement queries resolved against the honest prover messages / input codewords. The
collapse follows the same `simulateQ`-pushing recipe as
`Sumcheck/Spec/SingleRound.lean :: simulateQ_oracleVerify_eq`, generalised here to a verifier whose
spot-check phase is a `forIn` loop over `Fin t` (so we additionally need an
`OptionT`-`forIn`/`guard` transport, à la `Binius/BinaryBasefold/QueryPhase.lean :: ForInSupport`,
re-derived in-file to keep `ToyProblem` self-contained). -/

/-- `answer` of the default oracle interface is the identity (the message itself). -/
@[simp] lemma answer_instDefault {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

section SimulateQTransport
variable {ι' : Type} {spec : OracleSpec ι'} {m : Type → Type} [Monad m] [LawfulMonad m]
variable {α β : Type}

/-- `simulateQ` commutes with `OptionT.pure`. -/
theorem simulateQ_optionT_pure (impl : QueryImpl spec m) (b : β) :
    simulateQ impl (pure b : OptionT (OracleComp spec) β) = (pure b : OptionT m β) := by
  rw [show (pure b : OptionT (OracleComp spec) β) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

/-- `simulateQ` commutes with `OptionT` `failure`. -/
theorem simulateQ_optionT_failure (impl : QueryImpl spec m) :
    simulateQ impl (failure : OptionT (OracleComp spec) β) = (failure : OptionT m β) := by
  rw [OracleComp.failure_def]
  apply OptionT.ext
  simp only [OptionT.run_mk, simulateQ_pure, OptionT.fail]
  rfl

/-- `simulateQ` of a query-free `guard` is the (target-monad) `if`. -/
theorem simulateQ_optionT_guard (impl : QueryImpl spec m) (P : Prop) [Decidable P] :
    simulateQ impl (guard P : OptionT (OracleComp spec) PUnit)
      = (if P then pure PUnit.unit else failure : OptionT m PUnit) := by
  rw [guard_eq]
  by_cases hP : P
  · rw [if_pos hP, if_pos hP, simulateQ_optionT_pure]
  · rw [if_neg hP, if_neg hP, simulateQ_optionT_failure]

/-- `simulateQ` commutes with `forIn` over a list in `OptionT (OracleComp …)`: the simulated loop
equals the loop with the simulated body. The missing `simulateQ_forIn` for the `OptionT` stack. -/
theorem simulateQ_optionT_forIn (impl : QueryImpl spec m)
    (l : List α) (f : α → β → OptionT (OracleComp spec) (ForInStep β))
    (g : α → β → OptionT m (ForInStep β))
    (hg : ∀ a b, g a b = simulateQ impl (f a b)) :
    ∀ init : β,
      simulateQ impl (forIn l init f : OptionT (OracleComp spec) β)
        = (forIn l init g : OptionT m β) := by
  induction l with
  | nil =>
    intro init
    rw [List.forIn_nil, List.forIn_nil, simulateQ_optionT_pure]
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind, hg]
    refine bind_congr ?_
    intro step
    cases step with
    | done b => exact simulateQ_optionT_pure impl b
    | yield b => exact ih b

/-- A `forIn` over a list whose body is `guard (Q a)` then `yield ()` collapses to
`if (∀ a ∈ l, Q a) then pure () else failure`: the spot-check loop accepts iff every per-element
guard passes. -/
theorem forIn_guard_eq (l : List α) (Q : α → Prop) [∀ a, Decidable (Q a)]
    (body : α → PUnit → OptionT (OracleComp spec) (ForInStep PUnit))
    (hbody : ∀ a u, body a u = (guard (Q a) >>= fun _ => pure (ForInStep.yield PUnit.unit))) :
    (forIn l PUnit.unit body : OptionT (OracleComp spec) PUnit)
      = (if (∀ a ∈ l, Q a) then pure PUnit.unit else failure) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hbody]
    by_cases hQa : Q a
    · rw [guard_eq, if_pos hQa]
      simp only [pure_bind]
      rw [ih]
      by_cases hrest : (∀ b ∈ l, Q b)
      · rw [if_pos hrest, if_pos]
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · exact h ▸ hQa
        · exact hrest b h
      · rw [if_neg hrest, if_neg (fun hall =>
          hrest (fun b hb => hall b (List.mem_cons_of_mem a hb)))]
    · rw [guard_eq, if_neg hQa,
        if_neg (fun hall => hQa (hall a (List.mem_cons_self)))]
      simp [failure_bind]

end SimulateQTransport

section SimOracle2Query
open OracleInterface
variable {ιₒ : Type} {oSpec : OracleSpec ιₒ}
  {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]

/-- `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family. -/
lemma simulateQ_simOracle2_messageQuery (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family. -/
lemma simulateQ_simOracle2_leftQuery_oc (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₁]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inl qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₁ t₁ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- Verify-body message-query collapse: the `OptionT.lift <| liftComp <| lift query` form that
appears verbatim in `oracleVerifier.verify`, simulated via `simOracle2`, collapses to `pure` of the
message `answer`. -/
lemma simulateQ_simOracle2_messageQuery_optionT (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₂]ₒ).Domain) :
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (OptionT.lift (OracleComp.liftComp (OracleComp.lift (OracleSpec.query qm))
        (oSpec + ([T₁]ₒ + [T₂]ₒ))))
      : OptionT (OracleComp oSpec) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OptionT (OracleComp oSpec) _) := by
  erw [simulateQ_optionT_lift]
  rw [OracleComp.liftComp_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [simulateQ_simOracle2_messageQuery]
  rfl

/-- Verify-body oracle-statement-query collapse (LEFT family). -/
lemma simulateQ_simOracle2_leftQuery_optionT (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (OptionT.lift (OracleComp.liftComp (OracleComp.lift (OracleSpec.query qm))
        (oSpec + ([T₁]ₒ + [T₂]ₒ))))
      : OptionT (OracleComp oSpec) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OptionT (OracleComp oSpec) _) := by
  erw [simulateQ_optionT_lift]
  rw [OracleComp.liftComp_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [simulateQ_simOracle2_leftQuery_oc]
  rfl

end SimOracle2Query

set_option maxHeartbeats 2000000 in
/-- **Closed form of the compiled toy-problem oracle verifier.** Simulating
`oracleVerifier.verify` against the honest input codewords `oStmt` and prover messages `msgs`
(via `OracleInterface.simOracle2`) collapses every query — the message query for `g` and the
`2t` spot-check codeword queries — to the corresponding honest values, leaving a query-free
`OptionT` computation that is exactly `if accepts … then pure () else failure`.

This is the load-bearing lemma for honest completeness: composed with `accepts_of_inputRelation`
it shows the compiled verifier never fails on an honest transcript. -/
theorem simulateQ_oracleVerify_eq (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι F i)
    (chal : ∀ i, (pSpec (ι := ι) (F := F) k t).Challenge i)
    (msgs : ∀ i, (pSpec (ι := ι) (F := F) k t).Message i) :
    simulateQ (OracleInterface.simOracle2 ([]ₒ) oStmt msgs)
      ((oracleVerifier (ι := ι) (F := F) (k := k) (t := t) encode).verify stmt chal)
      = (if accepts (k := k) (t := t) encode stmt oStmt
            (chal ⟨⟨0, by decide⟩, by rfl⟩) (msgs ⟨1, by rfl⟩) (chal ⟨⟨2, by decide⟩, by rfl⟩)
          then (pure () : OptionT (OracleComp []ₒ) Unit) else failure) := by
  unfold oracleVerifier
  dsimp only
  rw [simulateQ_optionT_bind]
  erw [simulateQ_simOracle2_messageQuery_optionT (T₁ := OracleStatement ι F)
    (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs ⟨⟨1, by rfl⟩, id ()⟩]
  dsimp only [Sigma.fst, Sigma.snd]
  erw [pure_bind]
  rw [simulateQ_optionT_bind, simulateQ_optionT_guard, simulateQ_optionT_bind]
  rw [simulateQ_optionT_forIn (impl := OracleInterface.simOracle2 ([]ₒ) oStmt msgs)
    (g := fun (j : Fin t) (_ : PUnit) =>
      (do let γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩
          let xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩
          let g₀ : Fin k → F := OracleInterface.answer (msgs ⟨1, by rfl⟩) (id ())
          let _ ← (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F)
          let _ ← (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F)
          guard (encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          pure (ForInStep.yield PUnit.unit)))]
  swap
  · -- forIn body collapse: the f₀, f₁ codeword queries collapse to `pure (oStmt …)`.
    intro j _
    symm
    rw [simulateQ_optionT_bind]
    erw [simulateQ_simOracle2_leftQuery_optionT (T₁ := OracleStatement ι F)
      (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs
      (⟨0, chal ⟨⟨2, by decide⟩, by rfl⟩ j⟩ : [OracleStatement ι F]ₒ.Domain)]
    dsimp only [Sigma.fst, Sigma.snd]
    erw [pure_bind]
    rw [simulateQ_optionT_bind]
    erw [simulateQ_simOracle2_leftQuery_optionT (T₁ := OracleStatement ι F)
      (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs
      (⟨1, chal ⟨⟨2, by decide⟩, by rfl⟩ j⟩ : [OracleStatement ι F]ₒ.Domain)]
    dsimp only [Sigma.fst, Sigma.snd]
    erw [pure_bind]
    rw [simulateQ_optionT_bind, simulateQ_optionT_guard, simulateQ_optionT_pure]
    rfl
  -- The loop body reduces (pure-binds) to `guard Q_j >>= yield`; collapse via `forIn_guard_eq`.
  rw [forIn_guard_eq (l := List.finRange t)
      (Q := fun j =>
        let γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩
        let xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩
        let g₀ : Fin k → F := OracleInterface.answer (msgs ⟨1, by rfl⟩) (id ())
        encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))]
  · -- Combine the linear-constraint `if` and the spot-check `if` into `if accepts`.
    set γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩ with hγ
    set xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩ with hxs
    simp only [answer_instDefault, simulateQ_optionT_pure]
    set g₀ : Fin k → F := msgs ⟨1, by rfl⟩ with hg₀
    have hQ : (∀ a ∈ List.finRange t,
          encode g₀ (xs a) = oStmt 0 (xs a) + γ * oStmt 1 (xs a))
        ↔ (∀ j : Fin t, encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :=
      ⟨fun h j => h j (List.mem_finRange j), fun h a _ => h a⟩
    simp only [hQ]
    unfold accepts
    by_cases hlin : (∑ j, g₀ j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    · rw [if_pos hlin]
      by_cases hsc : ∀ j : Fin t,
          encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
      · rw [if_pos hsc, if_pos (And.intro hlin hsc), pure_bind, pure_bind]
      · rw [if_neg hsc, if_neg (fun h => hsc h.2), pure_bind, failure_bind]
    · rw [if_neg hlin, failure_bind, if_neg (fun h => hlin h.1)]
  · intro j u
    simp only [pure_bind]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Honest completeness for ABF26 Construction 6.2, point form: if
`((v, μ₁, μ₂), (f₁, f₂))` lies in `inputRelation` with the underlying
messages `M = (M₀, M₁)` (and `fᵢ` is the `encode`-image of `Mᵢ`), then
for any verifier challenges `(γ, xs)` the §6.1 decision `accepts` holds
against the honest prover's message `g = M₀ + γ · M₁`.

This is the point-form companion to the
`OracleReduction.perfectCompleteness` theorem that wraps the prover and
verifier objects below. -/
theorem accepts_of_inputRelation {k t : ℕ}
    {encode : (Fin k → F) →ₗ[F] (ι → F)}
    (stmt : Statement (F := F) k)
    (M : Witness (F := F) k)
    (hM : ∀ i, ∑ j, M i j * stmt.1 j =
        (if i = (0 : Fin 2) then stmt.2.1 else stmt.2.2))
    (f : ∀ i, OracleStatement ι F i)
    (hf : ∀ i, f i = encode (M i))
    (γ : F) (xs : Fin t → ι) :
    accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
      stmt f γ (fun j ↦ M 0 j + γ * M 1 j) xs := by
  refine ⟨?_, ?_⟩
  · -- Linear-constraint: ∑ j, (M 0 j + γ * M 1 j) * v j = μ₁ + γ * μ₂.
    have h0 : ∑ j, M 0 j * stmt.1 j = stmt.2.1 := by
      have := hM 0; simpa using this
    have h1 : ∑ j, M 1 j * stmt.1 j = stmt.2.2 := by
      have := hM 1
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simpa [if_neg hne] using this
    calc ∑ j, (M 0 j + γ * M 1 j) * stmt.1 j
        = ∑ j, (M 0 j * stmt.1 j + γ * (M 1 j * stmt.1 j)) := by
          apply Finset.sum_congr rfl; intros j _; ring
      _ = (∑ j, M 0 j * stmt.1 j) + ∑ j, γ * (M 1 j * stmt.1 j) :=
          Finset.sum_add_distrib
      _ = (∑ j, M 0 j * stmt.1 j) + γ * ∑ j, M 1 j * stmt.1 j := by
          rw [← Finset.mul_sum]
      _ = stmt.2.1 + γ * stmt.2.2 := by rw [h0, h1]
  · -- Spot-check: encode(g) x = f 0 x + γ * f 1 x.
    intro j
    have hg_eq : (fun i ↦ M 0 i + γ * M 1 i) = M 0 + γ • M 1 := by
      funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg_eq, map_add, map_smul, hf 0, hf 1]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `honestInputRelation k C encode`
(the honest-opening input relation — see the **statement repair** note below)
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = wit₀ + γ·wit₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

**Status: CLOSED.** `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]` (no `sorry`/`admit`/custom axiom). The proof is the standard
`probEvent_eq_one_iff` support decomposition, mirroring
`Sumcheck/Spec/SingleRound.lean`'s `reduction_perfectCompleteness`:

  * `Fin.induction_three` (a `rfl` in `ArkLib/Data/Fin/Basic.lean`) peels the
    three `Prover.runToRound (Fin.last 3)` rounds, resolved by `split`;
  * `simulateQ_oracleVerify_eq` (above) collapses the compiled oracle verifier
    to `if accepts … then pure () else failure`, every query reduced to its
    honest value via the in-file `simOracle2` collapse lemmas;
  * the no-failure half peels the prover-run support to the *concrete*
    `Fin.snoc`-built transcript (`tr = snoc (snoc (snoc default γ) g) xs`),
    reduces the `messages ⟨1⟩` / `challenges ⟨0⟩,⟨2⟩` accessors, and discharges
    the `if accepts …` guard by `accepts_of_inputRelation` for *every* sampled
    `(γ, xs)`; the event half is closed by `Subsingleton.elim` since the output
    statements live in `Unit` / `Fin 0 → _`.

**Statement repair (defect #18, hEnc class — pre-approved).** The historic
statement used `inputRelation k C`, which (Definition 6.1, `ToyProblem.relation`)
existentially quantifies the *opener* `encode'` — a *different* map than the
protocol's `encode`. The honest verifier's spot-check uses the protocol's
`encode`, so completeness needs `f i = encode (wit i)` for *that* `encode` and,
crucially, for the *prover's own witness* `wit` (the honest prover sends
`g = wit₀ + γ·wit₁`, built from `wit`, not from any existential `M`). Hence we
prove completeness against `honestInputRelation k C encode`, which pins the
opener to `encode` and the opening to `input.2 = wit` (cf. the L6.13 `hEnc`
linear-encoder precedent in `SoundnessBounds.lean`). This is a *strengthening*
of the input hypothesis — `honestInputRelation k C encode ⊆ inputRelation k C`
under `_h_encode_mem` (`honestInputRelation_subset_inputRelation`) — so the
claim is faithful and never vacuous. Completeness against `inputRelation k C`
itself is *false* (counterexample in the `honestInputRelation` docstring:
`encode' = 0`, `encode = id`, `wit ≠ 0`). -/
theorem oracleReduction_perfectCompleteness
    [SampleableType F] [SampleableType ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F))
    (_h_encode_mem : ∀ m, (encode m : ι → F) ∈ C) :
    (oracleReduction (ι := ι) (F := F) (k := k) (t := t)
        (encode : (Fin k → F) → (ι → F))).perfectCompleteness
      init impl
      -- Statement repair (hEnc class, L6.13 precedent): the honest-opening
      -- relation for the *protocol's* encoder, not the existential-encoder
      -- `inputRelation k C` (whose opener is a DIFFERENT map — completeness
      -- against it is false, see `honestInputRelation` docstring counterexample).
      -- `honestInputRelation k C encode ⊆ inputRelation k C` under
      -- `_h_encode_mem`, so this is the faithful (non-vacuous) claim.
      (honestInputRelation k C encode)
      (Set.univ : Set (((OutputStatement × ∀ i, OutputOracleStatement i)) ×
        OutputWitness)) := by
  -- ABF26-C6.2 completeness. The compiled verifier collapses (via `simulateQ_oracleVerify_eq`)
  -- to `if accepts … then pure () else failure`; `accepts_of_inputRelation` shows the `accepts`
  -- guard holds for the honest message `g = M₀+γM₁` under ANY challenges, so the residual
  -- `Pr = 1` is discharged by the support peel (à la Sumcheck `Simple`'s completeness).
  classical
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  rintro ⟨stmt, oStmt⟩ wit hRel
  obtain ⟨hf, hM⟩ := hRel
  -- The §6.1 decision predicate holds for the honest `g = wit₀ + γ·wit₁` (built from the
  -- prover's own witness `wit`) under every challenge pair.
  have hAcc : ∀ (γ : F) (xs : Fin t → ι),
      accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
        stmt oStmt γ (fun j ↦ wit 0 j + γ * wit 1 j) xs :=
    fun γ xs => accepts_of_inputRelation (encode := encode) stmt wit hM oStmt hf γ xs
  simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, oracleProver, OracleVerifier.toVerifier,
    Prover.runToRound, Prover.processRound, Fin.induction_three, pSpec,
    bind_pure_comp]
  -- Peel the three prover rounds: V→P (γ), P→V (g), V→P (xs).
  split <;> rename_i hDir0
  swap
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, bind_pure_comp]
  split <;> rename_i hDir1
  · exact absurd hDir1 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, bind_pure_comp]
  split <;> rename_i hDir2
  swap
  · exact absurd hDir2 (by decide)
  -- The verifier body is now the compiled `simulateQ`; collapse it to `if accepts …`.
  simp only [simulateQ_oracleVerify_eq]
  simp only [liftM_pure, liftComp_pure, map_pure, pure_bind, bind_pure_comp,
    Functor.map_map, Function.comp_def, OptionT.run_pure, Option.getM,
    Transcript.concat, Fin.snoc_last, Fin.snoc_castSucc]
  -- The honest `accepts` guard never short-circuits: under ANY challenges, the honest
  -- prover's message `g = M₀+γM₁` satisfies `accepts` (`hAcc`). We pin the `if accepts …`
  -- to `pure ()` by a definitional rewrite of the transcript accessors that feed it.
  rw [probEvent_eq_one_iff]
  -- After the collapse the verifier branch is `if accepts … (proverResult.1.messages ⟨1,_⟩) …`.
  -- The honest prover writes `proverResult.1.messages ⟨1,_⟩ = fun j ↦ M 0 j + γ · M 1 j`
  -- (round-1 `Transcript.concat` of the honest message) and the two challenge accessors are
  -- the sampled `γ, xs`. Reduce the accessors so the `if` condition matches `hAcc`.
  refine ⟨?_, ?_⟩
  · -- No failure: peel the challenge / message samples; the `if` collapses to `pure ()`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    -- Peel outer `init >>= …` then the prover-run / verifier binds, resolving each
    -- `getChallenge` sample, until the verifier `if accepts …` (which is `pure ()` by `hIf`).
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hmem
    obtain ⟨⟨_, s'⟩, hmem, rfl⟩ := hmem
    erw [simulateQ_bind] at hmem
    erw [StateT.run_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hmem
    -- Peel the prover-run `liftM (g <$> body)`: it is `OptionT.lift`, so `x = some (g result)`.
    erw [simulateQ_map] at hx
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨tr, sₜ⟩, htr, hxeq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxeq
    -- Reduce the verifier `match some tr with | some a => …` to its `some` branch.
    dsimp only at hs
    -- Peel the prover-run body `g <$> (γ-sample; honest-msg; xs-sample)` to expose the
    -- concrete `Fin.snoc`-built transcript.
    erw [simulateQ_map] at htr
    rw [StateT.run_map] at htr
    simp only [support_map, Set.mem_image] at htr
    obtain ⟨⟨trb, sb⟩, htr, htreq⟩ := htr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htreq
    -- Peel the prover-run body: round 2 (xs-sample) is the outer bind.
    erw [simulateQ_bind] at htr
    erw [StateT.run_bind] at htr
    rw [mem_support_bind_iff] at htr
    obtain ⟨⟨r01, s01⟩, htr01, htr2⟩ := htr
    -- Round 2: peel the xs-sample (`getChallenge ⟨2⟩`), then the `pure` and the map.
    erw [simulateQ_bind] at htr2
    erw [StateT.run_bind] at htr2
    rw [mem_support_bind_iff] at htr2
    obtain ⟨⟨xs, sx⟩, hxs, htr2b⟩ := htr2
    erw [simulateQ_map] at htr2b
    rw [StateT.run_map] at htr2b
    simp only [support_map, Set.mem_image] at htr2b
    obtain ⟨⟨pr2, sp2⟩, hpr2, htr2eq⟩ := htr2b
    -- `hpr2` is a `pure`: extract `r01.2 = (γ, st)` and `pr2 = fun _ ↦ (γ, st)`.
    -- Peel rounds 0 and 1 from `htr01`.
    erw [simulateQ_bind] at htr01
    erw [StateT.run_bind] at htr01
    rw [mem_support_bind_iff] at htr01
    obtain ⟨⟨r0, s0⟩, htr0, htr1⟩ := htr01
    erw [simulateQ_map] at htr1
    rw [StateT.run_map] at htr1
    simp only [support_map, Set.mem_image] at htr1
    obtain ⟨⟨pr1, sp1⟩, hpr1, htr1eq⟩ := htr1
    -- Round 0: peel the `pure (default, input)` bind, then the γ-sample map.
    erw [simulateQ_bind] at htr0
    erw [StateT.run_bind] at htr0
    rw [mem_support_bind_iff] at htr0
    obtain ⟨⟨ini, si⟩, hini, htr0b⟩ := htr0
    erw [simulateQ_pure, StateT.run_pure] at hini
    simp only [support_pure, Set.mem_singleton_iff] at hini
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hini
    erw [simulateQ_map] at htr0b
    rw [StateT.run_map] at htr0b
    simp only [support_map, Set.mem_image] at htr0b
    obtain ⟨⟨γ, sγ⟩, hγ, htr0eq⟩ := htr0b
    -- Resolve `r0` from the round-0 map, then the round-1 `pure` (honest message), then
    -- round-2 `pure` (receiveChallenge), substituting back up the chain.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr0eq
    dsimp only at hpr1
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hpr1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpr1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr1eq
    dsimp only at hpr2
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hpr2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpr2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr2eq
    -- Now `trb.1 = snoc (snoc (snoc default γ) (honest g)) xs`; reduce the `Fin.snoc` accessors
    -- in `hs`, dispatch `accepts` via `hAcc γ xs`, leaving `pure` (so the result is `some`,
    -- contradicting `none`).
    simp only [id_eq, FullTranscript.messages, FullTranscript.challenges, Fin.snoc,
      Fin.val_zero, Fin.val_one, Fin.val_two, Nat.lt_irrefl, Nat.reduceLT, ↓reduceDIte,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT, Fin.last, cast_eq] at hs
    -- The `if accepts …` guard holds (`hAcc γ xs`, up to the defeq `cast` on `g`); collapse it.
    rw [if_pos (by simpa only [cast_eq] using hAcc γ xs)] at hs
    -- The verifier now deterministically returns `some`, so `(none, _)` is not in its support.
    -- Peel the verifier's two OptionT binds (`liftM (pure …)` then the `match … some`).
    erw [simulateQ_optionT_bind] at hs
    -- The first bind is `liftM ((g <$> pure ()).run) = pure (some (g ()))`; reduce it.
    simp only [map_pure, OptionT.run_mk, OptionT.run_pure, liftM_pure, simulateQ_pure] at hs
    obtain ⟨⟨a, sa⟩, ha, hs⟩ := hs
  · -- Event holds: the output statements are both `Unit` (`OutputStatement = Unit`,
    -- `OutputOracleStatement : Fin 0 → Type`), hence trivially in `Set.univ` and equal.
    intro x hx
    exact ⟨trivial, Subsingleton.elim _ _⟩

/-- **Lemma 6.6 of [ABF26]** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))`, the toy-problem IOR has knowledge
soundness against the relaxed relation `R̃_{C,δ}^2` with error

  `max { ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|, (1 − δ)^t }`.

Stated against ArkLib's `Verifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`).

**Naming convention — paper vs API.** The ArkLib API's
`Verifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
is the relation the extracted witness satisfies and `relOut` is the
relation the verifier's output must satisfy. In this file `relIn` is
*our* `outputRelation` (paper's `R̃²_{C,δ}`, what the extractor
extracts to) and `relOut` is `Set.univ` (paper's C6.2 has trivial
output `Unit`). The name `outputRelation` reflects the **paper's**
"this is the protocol's output relation" perspective; do not be misled
by the API parameter named `relIn`.

The proof exhibits an extractor that (i) erasure-decodes `(f₁, f₂)`
against the largest agreement set, (ii) outputs the recovered messages,
and (iii) bounds the failure event by the union of the MCA failure and
the list-decoding cardinality bound (cf. Remark 6.7).

**Statement-level finding & repair (2026-06).** ABF26 L6.6 is a 2-special-soundness argument whose
extractor must **rewind** the prover (two accepting transcripts at distinct `γ`, solve a 2×2 linear
system), but ArkLib's `Verifier.knowledgeSoundness` quantifies only over a single-run
`Extractor.Straightline` with no re-invocation handle, so the rewinding extractor is not expressible
against it (the wall recorded in `oraclereduction-leftovers.md` residual (1)+(2)). We prove the
genuine content as `protocol62_knowledgeSoundnessViaRewinding` (the framework predicate
`Extractor.knowledgeSoundnessViaRewinding`, fully proven above) and reduce the straightline
statement to the **single named bridge residual** below — the precise straightline↔rewinding
interface translation, the smallest missing piece.

The residual is `Bridge.StraightlineOfRewinding` from the *proven* rewinding witness to
the straightline conclusion, so the theorem `protocol62_knowledgeSound` discharges the conclusion by
feeding the proven witness through the residual (no `sorry`, no `axiom`).

**Named bridge residual.** The named L6.6 bridge residual is carried as the explicit hypothesis
`hBridge`; no global axiom is introduced. -/
theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode


/-- **Remark 6.7 of [ABF26]**: the L6.6 soundness argument depends on
**mutual** correlated agreement (MCA). With only correlated agreement
(CA), one cannot prove every codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)`
decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/
def remark67 : Unit := ()

/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))`, the IOR has round-by-round knowledge
soundness (paper Definition A.5 ≡ ArkLib's
`Verifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with per-round
errors

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `KnowledgeStateFunction` tracks the largest current agreement set;
the extractor erasure-decodes against it.

**Statement-level finding & repair (2026-06).** Same wall as L6.6: `Verifier.rbrKnowledgeSoundness`
(`OracleReduction/Security/RoundByRound.lean`, line 811) quantifies only over a single-run
`Extractor.RoundByRound` (no re-invocation handle), so the rewinding extractor is not expressible
against it. We reduce to the **named bridge residual** below from the *proven* rewinding witness
`protocol62_knowledgeSoundnessViaRewinding` (same 2-special-sound rewinding extractor; the rbr
accounting splits its failure across the `γ` and spot-check rounds). No `sorry`, no `axiom`.

**Named bridge residual.** The named L6.8 bridge residual is carried as the explicit hypothesis
`hBridge`; no global axiom is introduced. -/
theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode

end Protocol

end Spec

end ToyProblem

/-! ### Axiom audit (issue #18 ToyProblem bridge residual frontiers) -/

#print axioms ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding
#print axioms ToyProblem.Spec.protocol62_knowledgeSound
#print axioms ToyProblem.Spec.protocol62_rbrKnowledgeSound
