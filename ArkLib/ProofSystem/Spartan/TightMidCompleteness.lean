/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFirstCompleteness
import ArkLib.ProofSystem.Spartan.TightMidLeaves
import ArkLib.ProofSystem.Spartan.TightSeamBridge
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves

/-!
# Tight mid-chain perfect-completeness leaves (issue #329, B7 / R1)

The completeness mirror of the tight mid-chain rbr-KS leaves (`TightMidLeaves.lean`): the three
carried middle rounds are perfectly complete along the **honest** tight relation chain

* after the carried first sum-check: `firstSumcheckWithTargetRelOutEnriched`
  (R1CS pass-through ∧ the direct terminal identity `e₁ = eval r_x F̂`,
  `TightFirstCompleteness.lean`);
* after `sendEvalClaimWithTarget`: `tightSendEvalClaimRelOut` — the enriched relation read back
  through the claim-oracle split, **plus** the claim-oracle honesty
  (`(fun idx => oracle (.inl idx)) = evalClaimValue`), **plus** the first-terminal binding identity
  `evalClaimBindingRel` (`e₁ = eq̃(τ)(r_x)·(v_A·v_B − v_C)` over the *sent* claims). The honest
  prover sends `evalClaimValue`, so the binding conjunct follows from the `e₁`-direct conjunct
  via the product factorization `firstVirtual_eval_eq_product`;
* after `linearCombinationWithTarget`: the challenge-stripped pushforward
  `tightLinearCombinationRelOut` (pure transport — the phase records the sampled RLC challenge
  and passes statement/oracles through);
* after `prependRLCTargetWithTarget`: `tightRelG` (`T = ∑ r·v^true` ∧ binding), equivalently —
  via the seam set-equality `tightRelG_eq_conjoined_relIn` (`TightSeamBridge.lean`) — the
  conjoined carried-second-sum-check input relation
  `secondSumcheckWithTargetRbrRelIn ∩ binding`, exactly where the enriched carried second
  sum-check completeness (`TightSecondCompleteness.lean`) picks up. The honest adapter emits
  `T = ∑ r·v^sent`, and the carried honesty conjunct turns the sent claims into the true ones.

Each leaf is stated in the `OracleReduction.perfectCompleteness init impl relIn relOut` format
that the composed completeness fold consumes (mirroring `ComposedCompletenessLeaves.lean`), with
seam-matching relations: leaf 1's output is leaf 2's input, leaf 2's output is leaf 3's input,
and leaf 3's output is the `h₇`-side input relation of the conjoined carried second sum-check.
-/

open OracleComp OracleSpec ProtocolSpec OracleInterface Function
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-! ## The honest tight relation chain through the mid rounds -/

/-- **Honest relation after the carried `sendEvalClaim`** (the completeness mirror of
`tightRelE`): the enriched carried-first relation (R1CS pass-through ∧ `e₁ = eval r_x F̂`) read
back through the claim-oracle split, the pointwise scalar-claim honesty (`(fun idx => oracle (.inl idx)) = evalClaimValue`), and
the first-terminal binding identity over the sent claims. -/
def tightSendEvalClaimRelOut :
    Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ())
          ∈ firstSumcheckWithTargetRelOutEnriched (R := R) pp
        ∧ (fun idx => (show R from x.1.2 (.inl idx))) =
          evalClaimValue R pp x.1.1.2 (fun j => x.1.2 (.inr j))
        ∧ x.1 ∈ evalClaimBindingRel (R := R) pp }

/-- The carried `linearCombination` round records the sampled RLC challenge and passes statement
and oracles through unchanged, so its honest output relation from an arbitrary input relation
`rel` is the challenge-stripped pushforward. Clone of `linearCombinationRelOutOf` at the carried
types. -/
def tightLinearCombinationRelOutOf
    (rel : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    Set ((Statement.AfterLinearCombinationWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | ((x.1.1.2, x.1.2), ()) ∈ rel }

/-- **Honest relation after the carried `linearCombination`**: the
`tightSendEvalClaimRelOut` content with the recorded RLC challenge stripped. -/
def tightLinearCombinationRelOut :
    Set ((Statement.AfterLinearCombinationWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  tightLinearCombinationRelOutOf pp (tightSendEvalClaimRelOut pp)

/-! ## Leaf 1: the carried `sendEvalClaim` round -/

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **Completeness leaf 1 (tight chain).** The carried `sendEvalClaim` round is perfectly
complete from the enriched carried-first output relation into `tightSendEvalClaimRelOut`: the
honest prover forwards statement and oracles and sends the bundled claim `evalClaimValue`, so
the enriched conjuncts pass through, the honesty conjunct is definitional, and the binding
conjunct is the `e₁`-direct identity composed with the product factorization
`firstVirtual_eval_eq_product`. Clone of `sendEvalClaim_perfectCompleteness_BF` at the carried
types. -/
theorem sendEvalClaimWithTarget_perfectCompleteness_tight :
    (sendEvalClaimWithTarget (R := R) pp oSpec).perfectCompleteness init impl
      (firstSumcheckWithTargetRelOutEnriched (R := R) pp)
      (tightSendEvalClaimRelOut (R := R) pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn z hz
  have : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, sendEvalClaimWithTarget] at hz
  rw [Reduction.run_of_prover_first] at hz
  simp only [sendEvalClaimWithTargetProver, sendEvalClaimWithTargetVerifier, liftM_pure,
    pure_bind, bind_pure_comp, OracleVerifier.toVerifier] at hz
  simp only [OptionT.run_mk, OptionT.run_pure, simulateQ_pure, pure_bind, map_pure,
    liftM_pure, Option.getM_some, Option.map_some] at hz
  simp_all [tightSendEvalClaimRelOut, sendEvalClaimVerifier, OracleVerifier.materializeOutput,
    OracleVerifier.materializeOutputOracle]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · convert hIn.2.trans (firstVirtual_eval_eq_product (R := R) pp stmt.2 oStmt) using 1
    simp [FullTranscript.messages]
    left
    rfl
  · funext i
    cases i <;> rfl

/-! ## Leaf 2: the carried `linearCombination` round -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- **Completeness leaf 2 (tight chain), parametric form.** The carried `linearCombination`
round is perfectly complete from any input relation `rel` to its challenge-stripped pushforward
`tightLinearCombinationRelOutOf rel`: the phase samples the RLC challenge, records it, and
passes statement/oracles/witness through unchanged. Clone of
`linearCombination_perfectCompleteness_of` at the carried types. -/
theorem linearCombinationWithTarget_perfectCompleteness_of
    (rel : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    (linearCombinationWithTarget (R := R) pp oSpec).perfectCompleteness init impl
      rel (tightLinearCombinationRelOutOf (R := R) pp rel) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hRelIn z hz
  simp only [linearCombinationWithTarget, OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, linearCombinationWithTargetProver,
    linearCombinationWithTargetVerifier, OracleVerifier.toVerifier, Verifier.run] at hz
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    simulateQ_pure, pure_bind, map_pure, liftM_pure,
    Option.elimM, Option.getM_some, Option.map_some] at hz
  simp_all [tightLinearCombinationRelOutOf, linearCombinationVerifier, OracleVerifier.materializeOutput,
    OracleVerifier.materializeOutputOracle, FullTranscript.messages]
  obtain ⟨q, _, rfl⟩ := hz
  exact ⟨_, q, stmt.1, stmt.2.1, stmt.2.2.1, stmt.2.2.2, oStmt, ⟨(), rfl⟩, hRelIn⟩

/-- **Completeness leaf 2 (tight chain), seam-pinned form.** Perfectly complete from
`tightSendEvalClaimRelOut` (leaf 1's output) into `tightLinearCombinationRelOut` (leaf 3's
input). Instance of the parametric form — the seam matches definitionally. -/
theorem linearCombinationWithTarget_perfectCompleteness_tight :
    (linearCombinationWithTarget (R := R) pp oSpec).perfectCompleteness init impl
      (tightSendEvalClaimRelOut (R := R) pp)
      (tightLinearCombinationRelOut (R := R) pp) :=
  linearCombinationWithTarget_perfectCompleteness_of pp oSpec
    (tightSendEvalClaimRelOut (R := R) pp)

end Leaves

/-! ## Leaf 3: the carried honest RLC-target adapter -/

/-- The carried honest RLC-target prover's run is deterministic: default (empty) transcript, the
RLC-prepended statement, oracles carried through, unit witness. Definitional. Clone of
`prependRLCTargetProver_run`. -/
theorem prependRLCTargetWithTargetProver_run
    (stmt : Statement.AfterLinearCombinationWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependRLCTargetWithTargetProver (R := R) pp oSpec).run (stmt, oStmt) () =
      pure ((default : (!p[] : ProtocolSpec 0).FullTranscript),
        ((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt), ()) := rfl

/-- The carried honest RLC-target adapter has a deterministic 0-round run. Clone of
`prependRLCTarget_run` at the carried statement (the simulated-verifier collapse is
`simulateQ_prependRLCTargetWithTargetVerifier`, `TightMidLeaves.lean`). -/
theorem prependRLCTargetWithTarget_run
    (stmt : Statement.AfterLinearCombinationWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependRLCTargetWithTarget (R := R) pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt), ())),
        ((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt)) :
        OptionT (OracleComp _) _) := by
  change ((prependRLCTargetWithTarget (R := R) pp oSpec).toReduction.run
    (stmt, oStmt) ()).run = _
  simp only [prependRLCTargetWithTarget, OracleReduction.toReduction, Reduction.run,
    Verifier.run, OracleVerifier.toVerifier]
  rw [prependRLCTargetWithTargetProver_run]
  simp only [liftM_pure, pure_bind, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, Option.elimM]
  erw [simulateQ_prependRLCTargetWithTargetVerifier]
  simp only [_root_.map_pure, Option.map_some, liftM_pure]
  rfl

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Completeness leaf 3 (tight chain), semantic endpoint.** The carried honest RLC-target
adapter is perfectly complete from `tightLinearCombinationRelOut` into `tightRelG`
(`T = ∑ r·v^true` ∧ binding): it emits `T = ∑ r·v^sent`, and the carried honesty conjunct turns
the sent claims into the true ones; the binding conjunct forwards. Clone of
`prependRLCTarget_perfectCompleteness` at the carried statement. -/
theorem prependRLCTargetWithTarget_perfectCompleteness_tightRelG :
    (prependRLCTargetWithTarget (R := R) pp oSpec).perfectCompleteness init impl
      (tightLinearCombinationRelOut (R := R) pp)
      (tightRelG (R := R) pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn x hx
  rw [prependRLCTargetWithTarget_run, OptionT.run_pure, support_pure,
    Set.mem_singleton_iff] at hx
  subst x
  refine ⟨_, rfl, ?_, rfl⟩
  obtain ⟨_hEnriched, hHonest, hBind⟩ := hIn
  refine ⟨?_, hBind⟩
  show (∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)))
      = ∑ idx, stmt.1 idx * evalClaimValue R pp stmt.2.2 (fun j => oStmt (.inr j)) idx
  have hH : (fun idx => (show R from oStmt (.inl idx)))
      = evalClaimValue R pp stmt.2.2 (fun j => oStmt (.inr j)) := hHonest
  exact Finset.sum_congr rfl fun idx _ => congrArg (stmt.1 idx * ·) (congrFun hH idx)

end Leaves

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Completeness leaf 3 (tight chain), seam-pinned form.** The carried honest RLC-target
adapter is perfectly complete from `tightLinearCombinationRelOut` into the conjoined carried
second sum-check input relation `secondSumcheckWithTargetRbrRelIn ∩ binding` — exactly where the
enriched carried-second completeness (`TightSecondCompleteness.lean`) and the conjoined `h₇`
leaf pick up. Restatement of the semantic endpoint through the seam set-equality
`tightRelG_eq_conjoined_relIn`. -/
theorem prependRLCTargetWithTarget_perfectCompleteness_tight :
    (prependRLCTargetWithTarget (R := R) pp oSpec).perfectCompleteness init impl
      (tightLinearCombinationRelOut (R := R) pp)
      (secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp}) := by
  rw [← tightRelG_eq_conjoined_relIn (R := R) pp oSpec]
  exact prependRLCTargetWithTarget_perfectCompleteness_tightRelG pp oSpec

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.sendEvalClaimWithTarget_perfectCompleteness_tight
#print axioms Spartan.Spec.Bricks.linearCombinationWithTarget_perfectCompleteness_of
#print axioms Spartan.Spec.Bricks.linearCombinationWithTarget_perfectCompleteness_tight
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTargetProver_run
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_run
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_perfectCompleteness_tightRelG
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_perfectCompleteness_tight
