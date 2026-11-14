/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Extensions.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Toy-IOR rewinding algebra: kernel-dependency audit & framework usage (not a security proof)

This module sits *downstream* of the toy-problem spec files and serves two purposes:

1. **Kernel-dependency audit.** It re-checks (via `#print axioms`) that the rewinding-extractor content — the
   2×2 solve `toySolve`, its correctness `toySolve_combine`, the 2-special-soundness theorem
   `toyRewindingExtractor_twoSpecialSound`, and the fully-proven framework witness
   `protocol62_knowledgeSoundnessViaRewinding` — depends on **no** `sorry` and **no** project-level
   assumed constant (only Lean's standard `propext`/`Classical.choice`/`Quot.sound`).

2. **Usage demonstration of the abstract framework.** It shows the rewinding witness driving the
   framework's operational guarantee `Extractor.knowledgeSoundnessViaRewinding.extracts`.

## Scope (read before citing)

This is **not** an end-to-end security result for the toy IOR. The success event measured here
is the abstract predicate `toyAccepts C δ decode pre`, not acceptance by the actual Construction
6.2 / 6.9 verifier against a malicious prover. `toyAccepts` already contains, as a conjunct, the
membership of the input in `outputRelation C δ` (with the supplied decoded pair), and
`outputRelation` reads only the statement, never the witness component. So the "extracted"
membership is exactly the assumed one; the 2×2 solve is valid algebra but is not needed for it.
No verifier spot checks, spot-check count `t`, MCA / list-size error, decoder validity, or
replay/rewinding execution bridge appear in any statement below.

The actual knowledge-soundness theorems for the toy protocols are the canonical
`ToyProblem.Spec.oracleVerifier_knowledgeSoundness_winningSetUpperBound` (L6.6,
`ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean`),
`ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundnessWorstCase` (L6.8,
`ArkLib/ProofSystem/ToyProblem/Spec/General.lean`), and
`ToyProblem.SimplifiedIOR.verifier_knowledgeSoundness` (L6.10,
`ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean`), which use straightline extractors.

## Where the rewinding-algebra content lives

* `ArkLib/Extensions/ProofSystem/ToyProblem/Spec/General.lean` —
  `toyCombine`, `toySolve`, `toySolve_combine`, `toyRewindingExtractor`, `toyAccepts`,
  `toyRewindingExtractor_twoSpecialSound`, `protocol62_knowledgeSoundnessViaRewinding`, and the
  legacy aliases `protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound` (which, despite
  their names, restate the same abstract predicate and are not proofs of L6.6 / L6.8).
* `ArkLib/Extensions/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean` —
  the legacy alias `simplifiedIOR_knowledgeSound` (likewise not a proof of L6.10).

The abstract framework consumed by all of the above is
`ArkLib/ToMathlib/RewindingExtractor.lean`.

## References

* [Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*][ABF26] §6
* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*][AFK22]
-/

noncomputable section

open scoped NNReal ENNReal

namespace ToyProblem.Spec

open Extractor
-- Activate the scoped `Pr_{ … }[ … ]` probability notation (its `macro_rules` are
-- `scoped` under `ProbabilityTheory`); without this the `Pr_{ … }` syntax in
-- `toyProtocol_extracts` parses but has no elaborator.
open scoped ProbabilityTheory

variable {ι F : Type} [Fintype ι] [Field F]
variable {k : ℕ}

/-- **Framework usage example (abstract acceptance predicate).** At a recorded prefix `pre`, if
the abstract predicate `toyAccepts C δ decode pre` holds for more than a `1/|F|` fraction of
challenges `γ`, then some rewinding extractor lands in `outputRelation C δ`.

This is the framework's `knowledgeSoundnessViaRewinding.extracts` instantiated at
`protocol62_knowledgeSoundnessViaRewinding`. It is **not** an end-to-end guarantee against a
malicious prover of the actual toy verifier: `hwin` measures `toyAccepts`, which already assumes
the conclusion's relation membership, rather than verifier acceptance. -/
theorem toyProtocol_extracts [Fintype F] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F))
    (pre : ToyPrefix ι F k) (resp : F → (Fin k → F))
    (hwin : (Fintype.card F : ENNReal)⁻¹ <
        Pr_{ let r ← $ᵖ F }[toyAccepts (ι := ι) (F := F) (k := k) C δ decode pre (r, resp r)]) :
    ∃ (E : RewindingExtractor (ToyPrefix ι F k) F (Fin k → F) (Witness (F := F) k))
      (c₁ c₂ : Completion F (Fin k → F)),
      (toyStmtOf (ι := ι) (F := F) (k := k) pre, E pre c₁ c₂)
        ∈ outputRelation (ι := ι) (F := F) k C δ :=
  knowledgeSoundnessViaRewinding.extracts
    (protocol62_knowledgeSoundnessViaRewinding C δ decode) pre resp hwin

end ToyProblem.Spec

/-! ## Kernel-dependency audit

Each `#print axioms` below must report only Lean's standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) — i.e. **no** `sorryAx` and **no** project-level
assumed constant in the rewinding-extractor content or the framework witness. -/

-- 2×2 solve and its correctness (pure field algebra):
#print axioms ToyProblem.Spec.toySolve
#print axioms ToyProblem.Spec.toySolve_combine

-- 2-special-soundness of the concrete toy rewinding extractor:
#print axioms ToyProblem.Spec.toyRewindingExtractor_twoSpecialSound

-- The fully-proven framework witness (the rewinding-flavoured knowledge soundness):
#print axioms ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding

-- The operational extraction guarantee in this file:
#print axioms ToyProblem.Spec.toyProtocol_extracts
