/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.RewindingExtractor

/-!
# The straightline ↔ rewinding bridge (framework)

An earlier version of `ArkLib/ToMathlib/RewindingExtractor.lean` and of the ABF26 §6 toy
docstrings named two objects — `Bridge.knowledgeSound_of_rewinding` (a "shape" lemma) and
`Bridge.StraightlineOfRewinding` (the claimed straightline↔rewinding residual, carried as a
hypothesis `hBridge`) — that did not exist in-tree. This file defines and proves them abstractly, in
the `Extractor.Bridge` namespace, over the same carriers as `RewindingExtractor.lean`.

**Scope.** Both objects are *abstract per-prefix repackagings* of
`knowledgeSoundnessViaRewinding.extracts`; `StraightlineOfRewinding` is a tautology at this level.
Neither mentions `Verifier.knowledgeSoundness`, a concrete verifier, its transcripts or query logs,
an error term, or a replay execution, so neither transports anything to protocol security. No
in-tree toy-protocol theorem takes `hBridge` as a hypothesis; the toy aliases
`protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound` / `simplifiedIOR_knowledgeSound`
restate the abstract rewinding predicate at the relation-assuming acceptance predicate `toyAccepts`
and are not proofs of ABF26 L6.6 / L6.8 / L6.10 (those are the canonical straightline theorems
`ToyProblem.Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound`,
`ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase`, and
`ToyProblem.SimplifiedIOR.verifier_knowledgeSoundness`).

## What this file delivers

1. `Bridge.StraightlineExtraction` — the straightline-shaped *operational conclusion*: at a given
   recorded prefix, whenever the prover beats the `1/|Challenge|` knowledge error there exist two
   completions on which *some* rewinding extractor lands a witness in the relation. This is exactly
   the form the straightline interface needs the rewinding witness to deliver.

2. `Bridge.knowledgeSound_of_rewinding` — **PROVEN** (no `sorry`, no axiom): a
   `knowledgeSoundnessViaRewinding` witness yields `Bridge.StraightlineExtraction` at every prefix.
   This is `knowledgeSoundnessViaRewinding.extracts` repackaged into the bridge shape; it is the
   "shows the *shape*" lemma the prose promised.

3. `Bridge.StraightlineOfRewinding` — the **named residual**: the precise remaining interface gap,
   the implication `(rewinding witness) → (straightline-shaped per-prefix extraction)` packaged as a
   single `Prop`. It is *discharged* by `Bridge.straightlineOfRewinding_holds` (proven below from
   `knowledgeSound_of_rewinding`), i.e. at this abstract level it is a tautology; it is **not** the
   genuine protocol-level straightline↔rewinding translation, which remains unformalized.

The only thing this framework deliberately does *not* do is identify the abstract carriers
(`Prefix`, `Challenge`, `Response`) with the concrete `Verifier.knowledgeSoundness` transcript /
query-log data of a *specific* protocol and average the per-prefix bound into the single
`Pr[...] ≤ ε` statement; that protocol-specific plumbing is the genuine remaining surface, recorded
honestly in the issue. What is provided here is the faithful, axiom-free *shape* lemma the prose
claimed already existed.

## References

* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*][AFK22]
* [Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*][ABF26]
-/

noncomputable section

open scoped NNReal ENNReal
open ProbabilityTheory

namespace Extractor

namespace Bridge

variable {Prefix Challenge Response WitIn StmtIn : Type}
  [Fintype Challenge] [Nonempty Challenge]

/-- **Straightline-shaped extraction conclusion at a prefix.**

This is the operational guarantee that the straightline `Verifier.knowledgeSoundness` interface
needs the rewinding machinery to supply: *at the recorded prefix `pre`*, if the prover's
single-challenge success probability (over a fresh uniform challenge, with the fixed continuation
`resp`) beats the 2-special-sound knowledge error `1/|Challenge|`, then there exist two completions
on which *some* rewinding extractor `E` outputs a witness in the relation.

It is phrased as an existential over `E : RewindingExtractor ...` precisely so it can be fed by the
existential-carrying `knowledgeSoundnessViaRewinding` predicate. -/
def StraightlineExtraction
    (relIn : Set (StmtIn × WitIn))
    (stmtOf : Prefix → StmtIn)
    (accepts : Prefix → Accepts Challenge Response)
    (pre : Prefix) : Prop :=
  ∀ resp : Challenge → Response,
    (Fintype.card Challenge : ENNReal)⁻¹ <
        Pr_{ let r ← $ᵖ Challenge}[accepts pre (r, resp r)] →
      ∃ (E : RewindingExtractor Prefix Challenge Response WitIn)
        (c₁ c₂ : Completion Challenge Response), (stmtOf pre, E pre c₁ c₂) ∈ relIn

/-- **The shape lemma the prose promised — PROVEN.**

`Bridge.knowledgeSound_of_rewinding`: from a `knowledgeSoundnessViaRewinding` witness one obtains, at
*every* prefix where the prover beats the knowledge error, an extracted witness in `relIn`. This is
exactly the statement quoted in the `RewindingExtractor.lean` bridge sketch
("shows the *shape*: from a rewinding knowledge-soundness witness ... one obtains, at every prefix
where the prover beats the error, an extracted witness").

The proof is `knowledgeSoundnessViaRewinding.extracts` (the forking lemma lifted through the
existential), so it carries **no** new axiom and **no** `sorry`. -/
theorem knowledgeSound_of_rewinding
    {relIn : Set (StmtIn × WitIn)}
    {stmtOf : Prefix → StmtIn}
    {accepts : Prefix → Accepts Challenge Response}
    (h : knowledgeSoundnessViaRewinding relIn stmtOf accepts) :
    ∀ pre : Prefix, StraightlineExtraction relIn stmtOf accepts pre := by
  intro pre resp hwin
  exact knowledgeSoundnessViaRewinding.extracts h pre resp hwin

/-- **The named straightline↔rewinding interface residual.**

`Bridge.StraightlineOfRewinding relIn stmtOf accepts` is the implication from the rewinding
knowledge-soundness witness to the per-prefix extraction conclusion. It is discharged below by
`straightlineOfRewinding_holds`, so it is not a genuine residual: the protocol-level gap (a concrete
verifier's acceptance event, replay execution, and averaged error bound) is not expressed by it. -/
def StraightlineOfRewinding
    (relIn : Set (StmtIn × WitIn))
    (stmtOf : Prefix → StmtIn)
    (accepts : Prefix → Accepts Challenge Response) : Prop :=
  knowledgeSoundnessViaRewinding relIn stmtOf accepts →
    ∀ pre : Prefix, StraightlineExtraction relIn stmtOf accepts pre

/-- **The named residual is a theorem, not a hole.**

`Bridge.StraightlineOfRewinding` holds for *every* relation / prefix-reader / acceptance predicate:
it is discharged by `knowledgeSound_of_rewinding`. This is an abstract tautology; it does not
transport any rewinding statement to `Verifier.knowledgeSoundness`. -/
theorem straightlineOfRewinding_holds
    (relIn : Set (StmtIn × WitIn))
    (stmtOf : Prefix → StmtIn)
    (accepts : Prefix → Accepts Challenge Response) :
    StraightlineOfRewinding relIn stmtOf accepts :=
  fun h pre => knowledgeSound_of_rewinding h pre

end Bridge

end Extractor

end

/-! ### Axiom audit (issue #105 StraightlineOfRewinding bridge) -/

#print axioms Extractor.Bridge.knowledgeSound_of_rewinding
#print axioms Extractor.Bridge.straightlineOfRewinding_holds
