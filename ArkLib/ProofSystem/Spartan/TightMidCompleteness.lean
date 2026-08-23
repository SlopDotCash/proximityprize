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
  (`.inl 0 = evalClaimValue`), **plus** the first-terminal binding identity
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

noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-! ## The honest tight relation chain through the mid rounds -/

/-- **Honest relation after the carried `sendEvalClaim`** (the completeness mirror of
`tightRelE`): the enriched carried-first relation (R1CS pass-through ∧ `e₁ = eval r_x F̂`) read
back through the claim-oracle split, the bundled-claim honesty (`.inl 0 = evalClaimValue`), and
the first-terminal binding identity over the sent claims. -/
def tightSendEvalClaimRelOut :
    Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ())
          ∈ firstSumcheckWithTargetRelOutEnriched (R := R) pp
        ∧ x.1.2 (.inl 0) = evalClaimValue R pp x.1.1.2 (fun j => x.1.2 (.inr j))
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
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ wit hIn
  have _inst : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, sendEvalClaimWithTarget]
  rw [Reduction.run_of_prover_first]
  simp only [sendEvalClaimWithTargetProver, sendEvalClaimWithTargetVerifier, liftM_pure,
    pure_bind, bind_pure_comp, OracleVerifier.toVerifier]
  erw [simulateQ_pure]
  simp only [map_pure, StateT.run'_eq, StateT.run_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- `probFailure = 0`: a `ProbComp` cannot fail and the appended `pure (some ·)` is total.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    cases hx
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- enriched pass-through: the recovered input pair is the input
      convert hIn using 2
    · -- claim-oracle honesty: the `.inl 0` slot is the honest `evalClaimValue`
      rfl
    · -- the binding identity: `e₁`-direct + the product factorization at the honest claims
      exact hIn.2.trans (firstVirtual_eval_eq_product (R := R) pp stmt.2 oStmt)
    · -- prover output statement equals verifier output statement
      refine Prod.ext rfl ?_
      funext i
      rcases i with j | j <;> rfl

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
  simp only [OracleReduction.perfectCompleteness, linearCombinationWithTarget,
    tightLinearCombinationRelOutOf]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hRelIn
  simp only [OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, linearCombinationWithTargetProver,
    linearCombinationWithTargetVerifier, OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc]
  erw [simulateQ_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    Option.getM, Option.bind_some, Option.elimM,
    FullTranscript.challenges, FullTranscript.messages, ChallengeIdx, Challenge]
  erw [simulateQ_query]
  simp only [Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx,
    Message, bind_map_left, StateT.run'_eq, StateT.run_bind, map_bind, OptionT.mk_bind,
    Set.mem_setOf_eq, probEvent_eq_one_iff, probFailure_bind_eq_zero_iff,
    OptionT.probFailure_liftM, HasEvalPMF.probFailure_eq_zero, OptionT.support_liftM,
    Prod.forall, true_and, support_bind, Set.mem_iUnion, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.mk.injEq]
  constructor <;> intro <;> intro <;> intro <;> intro
  all_goals try erw [simulateQ_bind]
  all_goals simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift]
  all_goals simp only [OracleComp.liftComp_pure, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_pure, simulateQ_id', pure_bind, bind_assoc, map_pure, monadLift_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, probFailure_eq_zero,
    support_pure, Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [simulateQ_pure, pure_bind, map_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, StateT.run_pure, probFailure_eq_zero,
    support_pure, support_map, Set.mem_singleton_iff, Set.mem_image,
    OptionT.probFailure_eq, probOutput_pure]
  · erw [simulateQ_bind, simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp [map_pure, OptionT.mk, probFailure_pure]
  · intro trFull lc e1 fsc fc x1 oOut wOut lc2 e12 fsc2 fc2 x2 oOut2 sI hsI rng
    erw [simulateQ_bind] at rng
    simp only [liftComp_eq_liftM, pure_bind, simulateQ_pure, OptionT.lift,
      OptionT.run_mk, map_pure] at rng
    erw [simulateQ_pure] at rng
    simp only [pure_bind, simulateQ_pure, support_pure, StateT.run, StateT.run',
      Set.mem_singleton_iff, Prod.mk.injEq] at rng
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := rng
    refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [Set.mem_setOf_eq] using hRelIn
    · funext i
      rcases i with j | j <;> rfl

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
        ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ()) := rfl

/-- The carried honest RLC-target adapter has a deterministic 0-round run. Clone of
`prependRLCTarget_run` at the carried statement (the simulated-verifier collapse is
`simulateQ_prependRLCTargetWithTargetVerifier`, `TightMidLeaves.lean`). -/
theorem prependRLCTargetWithTarget_run
    (stmt : Statement.AfterLinearCombinationWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependRLCTargetWithTarget (R := R) pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ())),
        ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt)) :
        OptionT (OracleComp _) _) := by
  simp only [prependRLCTargetWithTarget, OracleReduction.toReduction, Reduction.run,
    Verifier.run, OracleVerifier.toVerifier]
  rw [prependRLCTargetWithTargetProver_run]
  simp only [liftM_pure, pure_bind]
  rw [simulateQ_prependRLCTargetWithTargetVerifier]
  simp only [OptionT.run_map, bind_pure_comp, Option.getM]
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
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [prependRLCTargetWithTarget_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ())),
          ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt))) :
          OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ())),
        ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt))) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ())),
          ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt))) :
          OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt), ())),
        ((∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt), oStmt))) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [_root_.map_pure, _root_.support_pure, Set.mem_singleton_iff,
      Option.some.injEq] at hx
    cases hx
    obtain ⟨_hEnriched, hHonest, hBind⟩ := hIn
    refine ⟨⟨?_, hBind⟩, rfl⟩
    -- `T = ∑ r·v^sent = ∑ r·v^true` via the carried honesty conjunct.
    show (∑ idx, stmt.1 idx * oStmt (.inl 0) idx)
        = ∑ idx, stmt.1 idx *
            evalClaimValue R pp stmt.2.2 (fun j => oStmt (.inr j)) idx
    have hH : oStmt (.inl 0)
        = evalClaimValue R pp stmt.2.2 (fun j => oStmt (.inr j)) := hHonest
    rw [hH]

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
