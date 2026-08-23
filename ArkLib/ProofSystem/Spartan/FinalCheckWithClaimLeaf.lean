/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks

/-!
# The `finalCheckWithClaim` rbr knowledge-soundness leaf (#329, hypothesis K4)

The composed Spartan chain currently terminates in the binding-free pair
`finalCheck ▷ prependClaim`: `finalPredicate` is tautological (`combined = combined`) and the
relations `finalCheckWithClaimRelIn/Out` are `Set.univ`, so that terminal leaf carries no
algebraic content. The *real* terminal check is `finalCheckWithClaim`, whose
`finalClaimPredicate` queries the matrix/witness oracles and compares the carried target with
`finalExpectedClaimValue`.

This module proves the knowledge-soundness leaf for `finalCheckWithClaim` at the **semantic**
relation `finalCheckWithClaimValueRelIn` (carried target `=` algebraic expected claim value),
not at `Set.univ`:

* `CheckClaim.eq_of_some_mem_support_toVerifier_run` — **support pass-through**: the compiled
  `CheckClaim` oracle verifier can only output the unchanged statement/oracle-statement pair
  (the predicate's `Prop` value is discarded by `let _ ←`, and failure is the only other
  branch).
* `CheckClaim.probEvent_toVerifier_run_eq_zero` — **the doom-catch**: an input pair failing a
  property `P` is never mapped into `P` by the verifier run (probability `0`, i.e. doom is
  rejected with probability 1 *relative to the semantic relation*).
* `CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport` — perfect (error-`0`) rbr
  knowledge soundness of any `CheckClaim` oracle verifier along a relation transport
  `relOut ⊆ relIn` on the pass-through pair.
* `finalCheckWithClaim_rbrKnowledgeSoundness` (and variants) — the Spartan instantiation at
  `finalCheckWithClaimValueRelIn` / `finalCheckWithClaimSecondSumcheckEvalRelOut`.
* `finalCheckWithClaim_doomCatch` — a statement whose carried target differs from
  `finalExpectedClaimValue` is never output into the semantic relation: no accepting output of
  the run's support satisfies the relation.

**Honesty note.** `CheckClaim.oracleVerifier` *discards* the `Prop` computed by the predicate
(`do let _ ← pred stmt; return stmt`), so the verifier itself never halts on a wrong target;
the binding content of the terminal check lives in the *relation* (which this leaf keeps
semantic, unlike the `Set.univ` front doors). The doom-catch is therefore stated in the same
currency as `KnowledgeStateFunction.toFun_full`: a doomed input has probability `0` of
producing an output in the semantic output relation.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec

namespace CheckClaim

universe u

variable {ι : Type} {oSpec : OracleSpec ι} {Statement : Type}
  {ιₛ : Type} {OStatement : ιₛ → Type} [∀ i, OracleInterface (OStatement i)]
  (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)

/-- `simulateQ` collapses an `OptionT`-level `pure` to an honest `pure (some _)` in the target
monad, for any lawful target. -/
lemma simulateQ_optionT_pure_some {ι' : Type} {spec : OracleSpec ι'}
    {n : Type → Type u} [Monad n] [LawfulMonad n] (impl : QueryImpl spec n)
    {γ : Type} (b : γ) :
    simulateQ impl (pure b : OptionT (OracleComp spec) γ) = (pure (some b) : n (Option γ)) := by
  show simulateQ impl (pure (some b) : OracleComp spec (Option γ)) = _
  exact simulateQ_pure impl (some b)

/-- An `OptionT` bind, re-expressed as the underlying monad bind with an `Option.elim`
continuation. -/
lemma optionT_bind_eq_elim_bind {n : Type → Type u} [Monad n]
    {α β : Type} (x : OptionT n α) (f : α → OptionT n β) :
    (x >>= f : OptionT n β) =
      (x.run >>= fun o => Option.elim o (pure none) (fun a => (f a).run) : n (Option β)) := by
  show OptionT.bind x f = _
  unfold OptionT.bind OptionT.mk
  refine bind_congr fun o => ?_
  cases o <;> rfl

/-- **Support pass-through for the compiled `CheckClaim` oracle verifier.** Whatever the oracle
predicate computes (its `Prop` value is discarded by `let _ ←`), the only possible (non-failing)
output of the compiled verifier run is the unchanged input statement/oracle-statement pair. -/
lemma eq_of_some_mem_support_toVerifier_run {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (stmt : Statement) (oStmt : ∀ i, OStatement i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript)
    (x : Statement × (∀ i, OStatement i))
    (hx : some x ∈ _root_.support ((simulateQ impl
      ((oracleVerifier oSpec Statement OStatement pred).toVerifier.run (stmt, oStmt) tr :
        OracleComp oSpec (Option (Statement × (∀ i, OStatement i))))).run' s)) :
    x = (stmt, oStmt) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier] at hx
  rw [simulateQ_optionT_bind] at hx
  rw [simulateQ_optionT_bind] at hx
  rw [simulateQ_optionT_bind] at hx
  simp only [simulateQ_optionT_pure_some, optionT_bind_eq_elim_bind] at hx
  erw [optionT_bind_eq_elim_bind] at hx
  erw [simulateQ_optionT_pure_some] at hx
  simp only [StateT.run'_eq, StateT.run_bind, map_bind, support_bind, support_map,
    Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨⟨o₁, s₁⟩, ho₁, x₁, hx₁, hfst⟩ := hx
  match o₁ with
  | none =>
      simp only [Option.elim_none, OptionT.run, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hx₁
      subst hx₁
      simp at hfst
  | some a =>
      simp only [OptionT.run, StateT.run_bind, support_bind, Set.mem_iUnion] at ho₁
      obtain ⟨⟨o₂, s₂⟩, ho₂, ho₁⟩ := ho₁
      match o₂ with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at ho₁
          exact absurd ho₁.1 (by simp)
      | some p =>
          simp only [Option.elim_some, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at ho₁
          obtain ⟨ha, hs⟩ := ho₁
          subst ha
          simp only [Option.elim_some, OptionT.run, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hx₁
          subst hx₁
          simp only [Option.some.injEq] at hfst
          subst hfst
          rfl

/-- **Doom is caught by the relation at the terminal check.** If the input statement/oracle pair
fails a property `P`, then the compiled `CheckClaim` oracle verifier run never outputs a pair
satisfying `P`: the verifier is a pass-through, so the input's doom persists with probability 1. -/
theorem probEvent_toVerifier_run_eq_zero {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (P : Statement × (∀ i, OStatement i) → Prop)
    (stmt : Statement) (oStmt : ∀ i, OStatement i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript)
    (hP : ¬ P (stmt, oStmt)) :
    Pr[P | OptionT.mk do
      (simulateQ impl ((oracleVerifier oSpec Statement OStatement pred).toVerifier.run
        (stmt, oStmt) tr)).run' (← init)] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  have hxe := eq_of_some_mem_support_toVerifier_run pred impl s stmt oStmt tr x hx
  subst hxe
  exact hP

/-- Knowledge state function for the compiled `CheckClaim` oracle verifier, along a relation
transport `relOut ⊆ relIn` (on the pass-through pair). -/
def oracleVerifier_knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn relOut : Set ((Statement × (∀ i, OStatement i)) × Unit)}
    (hdoom : ∀ p, (p, ()) ∈ relOut → (p, ()) ∈ relIn) :
    (oracleVerifier oSpec Statement OStatement pred).toVerifier.KnowledgeStateFunction
      init impl relIn relOut (extractor oSpec (Statement × (∀ i, OStatement i))) where
  toFun | ⟨0, _⟩ => fun stmtIn _ _ => (stmtIn, ()) ∈ relIn
  toFun_empty := fun stmtIn witMid => Iff.rfl
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmtIn tr witOut => by
    intro h
    obtain ⟨stmt, oStmt⟩ := stmtIn
    show ((stmt, oStmt), ()) ∈ relIn
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have hxe := eq_of_some_mem_support_toVerifier_run pred impl s stmt oStmt tr x hx
    subst hxe
    cases witOut
    exact hdoom (stmt, oStmt) hrel

/-- **The `CheckClaim` oracle verifier is perfectly rbr knowledge-sound along any relation
transport** `relOut ⊆ relIn` on the pass-through pair, with zero error. In particular this holds
at *semantic* (non-`Set.univ`) relations. -/
theorem oracleVerifier_rbrKnowledgeSoundness_transport {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn relOut : Set ((Statement × (∀ i, OStatement i)) × Unit)}
    (hdoom : ∀ p, (p, ()) ∈ relOut → (p, ()) ∈ relIn) :
    (oracleVerifier oSpec Statement OStatement pred).rbrKnowledgeSoundness init impl
      relIn relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  refine ⟨fun _ => Unit, extractor oSpec (Statement × (∀ i, OStatement i)),
    oracleVerifier_knowledgeStateFunction pred init impl hdoom, ?_⟩
  intro _ _ _ i
  exact Fin.elim0 i.1

end CheckClaim

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] (pp : Spartan.PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)

/-- **Support pass-through for the target-carrying Spartan terminal check.** Any non-failing
output of the compiled `finalCheckWithClaim` verifier run is the unchanged input
`((target, stmt), oStmt)`. -/
theorem finalCheckWithClaim_run_support_passthrough {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (target : R) (stmt : FinalStatement R pp) (oStmt : ∀ i, FinalOracleStatement R pp i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript)
    (x : FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i))
    (hx : some x ∈ _root_.support ((simulateQ impl
      ((finalCheckWithClaim R pp oSpec).verifier.toVerifier.run ((target, stmt), oStmt) tr :
        OracleComp oSpec
          (Option (FinalClaimStatement R pp × (∀ i, FinalOracleStatement R pp i))))).run' s)) :
    x = ((target, stmt), oStmt) :=
  CheckClaim.eq_of_some_mem_support_toVerifier_run (finalClaimPredicate R pp)
    impl s (target, stmt) oStmt tr x hx

/-- **The doom-catch theorem for the real Spartan terminal check.** A statement whose carried
target differs from the algebraic `finalExpectedClaimValue` is never output into the semantic
terminal relation by `finalCheckWithClaim`'s verifier: the probability that the run produces an
output satisfying `finalCheckWithClaimValueRelIn` is `0` (no accepting-into-the-relation output
exists in the run's support). -/
theorem finalCheckWithClaim_doomCatch {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (target : R) (stmt : FinalStatement R pp) (oStmt : ∀ i, FinalOracleStatement R pp i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript)
    (hdoom : target ≠ finalExpectedClaimValue R pp stmt oStmt) :
    Pr[fun out => (out, ()) ∈ finalCheckWithClaimValueRelIn R pp | OptionT.mk do
      (simulateQ impl ((finalCheckWithClaim R pp oSpec).verifier.toVerifier.run
        ((target, stmt), oStmt) tr)).run' (← init)] = 0 :=
  CheckClaim.probEvent_toVerifier_run_eq_zero (finalClaimPredicate R pp) init impl
    (fun out => (out, ()) ∈ finalCheckWithClaimValueRelIn R pp)
    (target, stmt) oStmt tr hdoom

/-- Doom-catch in the second-sum-check endpoint currency: a carried target differing from the
second-sum-check virtual-polynomial endpoint is never output into
`finalCheckWithClaimSecondSumcheckEvalRelOut`. -/
theorem finalCheckWithClaim_doomCatch_secondSumcheckEval {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (target : R) (stmt : FinalStatement R pp) (oStmt : ∀ i, FinalOracleStatement R pp i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript)
    (hdoom : target ≠
      MvPolynomial.eval stmt.1 (secondSumCheckVirtualPolynomial R pp stmt.2 oStmt)) :
    Pr[fun out => (out, ()) ∈ finalCheckWithClaimSecondSumcheckEvalRelOut R pp | OptionT.mk do
      (simulateQ impl ((finalCheckWithClaim R pp oSpec).verifier.toVerifier.run
        ((target, stmt), oStmt) tr)).run' (← init)] = 0 :=
  CheckClaim.probEvent_toVerifier_run_eq_zero (finalClaimPredicate R pp) init impl
    (fun out => (out, ()) ∈ finalCheckWithClaimSecondSumcheckEvalRelOut R pp)
    (target, stmt) oStmt tr hdoom

/-- **The `finalCheckWithClaim` rbr knowledge-soundness leaf along any relation transport**
`relOut ⊆ relIn` on the pass-through pair (zero-round, zero error). -/
theorem finalCheckWithClaim_rbrKnowledgeSoundness_transport {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {relIn relOut : Set ((FinalClaimStatement R pp ×
      (∀ i, FinalOracleStatement R pp i)) × Unit)}
    (hdoom : ∀ p, (p, ()) ∈ relOut → (p, ()) ∈ relIn) :
    (finalCheckWithClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relIn relOut 0 :=
  CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport (finalClaimPredicate R pp)
    init impl hdoom

/-- **The K4 leaf: `finalCheckWithClaim` is perfectly rbr knowledge-sound at the semantic
terminal relation** `finalCheckWithClaimValueRelIn` (carried target `=` algebraic expected claim
value) — **not** at the tautological `Set.univ` front doors. Zero rounds, zero error. -/
theorem finalCheckWithClaim_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (finalCheckWithClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (finalCheckWithClaimValueRelIn R pp) (finalCheckWithClaimValueRelIn R pp) 0 :=
  finalCheckWithClaim_rbrKnowledgeSoundness_transport pp oSpec init impl (fun _ h => h)

/-- The K4 leaf at the second-sum-check endpoint relation
`finalCheckWithClaimSecondSumcheckEvalRelOut` (the composition-facing surface for the K5
reassembly). -/
theorem finalCheckWithClaim_rbrKnowledgeSoundness_secondSumcheckEval [DecidableEq R] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (finalCheckWithClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (finalCheckWithClaimSecondSumcheckEvalRelOut R pp)
      (finalCheckWithClaimSecondSumcheckEvalRelOut R pp) 0 := by
  rw [finalCheckWithClaimSecondSumcheckEvalRelOut_eq_valueRelIn]
  exact finalCheckWithClaim_rbrKnowledgeSoundness pp oSpec init impl

end Spartan.Spec.Bricks

#print axioms CheckClaim.eq_of_some_mem_support_toVerifier_run
#print axioms CheckClaim.probEvent_toVerifier_run_eq_zero
#print axioms CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_run_support_passthrough
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_doomCatch
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_doomCatch_secondSumcheckEval
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_rbrKnowledgeSoundness_transport
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_rbrKnowledgeSoundness
#print axioms Spartan.Spec.Bricks.finalCheckWithClaim_rbrKnowledgeSoundness_secondSumcheckEval
