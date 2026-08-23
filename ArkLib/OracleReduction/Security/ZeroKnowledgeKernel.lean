/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
# Witness-independence sufficient conditions for honest-verifier zero-knowledge (issue #112)

This file adds the reusable *research kernel* that reduces every concrete perfect-HVZK obligation
to a witness-independence check on the honest transcript distribution.

The honest transcript distribution `honestTranscriptDist init impl reduction stmtIn witIn`
(`ArkLib/OracleReduction/Security/ZeroKnowledge.lean`) records the honest verifier's *view* of the
interaction. The canonical simulator for an honest-verifier zero-knowledge proof of a public-coin
reduction simply re-runs the honest interaction; the only thing it lacks is the prover's witness, so
it substitutes a *witness selector* `w₀ : StmtIn → WitIn` that depends on the statement alone. The
simulator is then perfect exactly when the honest transcript distribution does not depend on which
witness was used — the classical statement that *the verifier's view is witness-independent*.

* `witnessSelectorSimulator` — the canonical simulator: run the honest interaction with the
  statement-selected witness.
* `perfectHVZK_witnessSelectorSimulator` — the selector simulator is perfect HVZK whenever the
  honest transcript distribution at the selected witness matches the one at the true witness on the
  relation.
* `isHVZK_of_witnessIndependent` — existential form: a witness-independent honest transcript
  distribution gives honest-verifier zero-knowledge.
* `isHVZK_of_witnessOblivious` — the cleanest structural sufficient condition: if the honest
  transcript distribution is literally independent of the witness for each fixed statement, the
  reduction is HVZK for every relation.

These are the plug-in lemmas every concrete protocol HVZK proof needs: they isolate the genuine
content (a distribution-level witness-independence fact about a specific protocol) from the
boilerplate of exhibiting a simulator. They sit directly on the promoted transcript-level HVZK API
and are axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

noncomputable section
open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- The canonical simulator built from the honest transcript distribution and a witness
selector `w₀ : StmtIn → WitIn`: on input `stmtIn`, run the honest interaction with the
statement-selected witness `w₀ stmtIn`. This is the post-interpretation form of "the simulator
re-runs the honest prover with a witness it chose from the statement". -/
def witnessSelectorSimulator
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn) :
    TranscriptSimulator oSpec StmtIn pSpec :=
  fun stmtIn => honestTranscriptDist init impl reduction stmtIn (w₀ stmtIn)

/-- **Witness-independence sufficient condition for perfect HVZK.** If the honest transcript
distribution at the selected witness `w₀ stmtIn` agrees (as a distribution) with the one at the
true witness for every related pair, then the canonical witness-selector simulator achieves
perfect HVZK. This reduces every concrete perfect-HVZK obligation to a witness-independence check
on the honest transcript distribution. -/
theorem perfectHVZK_witnessSelectorSimulator
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn)
    (hwi : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl reduction stmtIn (w₀ stmtIn)) =
        evalDist (honestTranscriptDist init impl reduction stmtIn witIn)) :
    perfectHVZK init impl rel reduction (witnessSelectorSimulator init impl reduction w₀) :=
  fun stmtIn witIn hMem => hwi stmtIn witIn hMem

/-- **Witness-independence ⟹ HVZK (existential).** A reduction whose honest transcript
distribution is witness-independent on `rel` (witnessed by a selector `w₀`) is honest-verifier
zero-knowledge. -/
theorem isHVZK_of_witnessIndependent
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn)
    (hwi : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl reduction stmtIn (w₀ stmtIn)) =
        evalDist (honestTranscriptDist init impl reduction stmtIn witIn)) :
    isHVZK init impl rel reduction :=
  ⟨witnessSelectorSimulator init impl reduction w₀,
   perfectHVZK_witnessSelectorSimulator init impl rel reduction w₀ hwi⟩

/-- **Fully witness-oblivious honest distribution ⟹ HVZK.** If, for a fixed statement, the honest
transcript distribution does not depend on the witness at all, then (using any witness selector)
the reduction is HVZK for every relation. This is the cleanest structural sufficient condition:
public-coin reductions whose prover messages are computed from the statement alone are perfectly
simulatable. -/
theorem isHVZK_of_witnessOblivious
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn)
    (hobliv : ∀ stmtIn w w',
      evalDist (honestTranscriptDist init impl reduction stmtIn w) =
        evalDist (honestTranscriptDist init impl reduction stmtIn w')) :
    isHVZK init impl rel reduction :=
  isHVZK_of_witnessIndependent init impl rel reduction w₀
    (fun stmtIn witIn _ => hobliv stmtIn (w₀ stmtIn) witIn)

/-- **Statistical analogue.** Witness-independence within total-variation distance `ε` at the
selected witness gives statistical HVZK with error `ε` via the canonical selector simulator. -/
theorem statisticalHVZK_witnessSelectorSimulator
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn) (ε : ℝ≥0)
    (hwi : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl reduction stmtIn (w₀ stmtIn))
        (honestTranscriptDist init impl reduction stmtIn witIn) ≤ (ε : ℝ)) :
    statisticalHVZK init impl rel reduction
      (witnessSelectorSimulator init impl reduction w₀) ε :=
  fun stmtIn witIn hMem => hwi stmtIn witIn hMem

/-- **Existential statistical form.** A reduction whose honest transcript distribution is
witness-independent up to total-variation distance `ε` on `rel` is statistically HVZK with error
`ε`. -/
theorem isStatHVZK_of_witnessIndependent
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (w₀ : StmtIn → WitIn) (ε : ℝ≥0)
    (hwi : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl reduction stmtIn (w₀ stmtIn))
        (honestTranscriptDist init impl reduction stmtIn witIn) ≤ (ε : ℝ)) :
    isStatHVZK init impl rel reduction ε :=
  ⟨witnessSelectorSimulator init impl reduction w₀,
   statisticalHVZK_witnessSelectorSimulator init impl rel reduction w₀ ε hwi⟩

end Reduction

/- Axiom audit for the witness-independence HVZK kernel. -/
#print axioms Reduction.perfectHVZK_witnessSelectorSimulator
#print axioms Reduction.isHVZK_of_witnessIndependent
#print axioms Reduction.isHVZK_of_witnessOblivious
#print axioms Reduction.statisticalHVZK_witnessSelectorSimulator
#print axioms Reduction.isStatHVZK_of_witnessIndependent
