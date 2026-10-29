/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessUncondCorrect
import ArkLib.ProofSystem.Spartan.SumcheckPhaseRbr

/-! # Oracle-pinned multi-round sum-check perfect completeness (issue #329, task K)

The completeness keystone for the tight composed Spartan apex: the `P`-indexed family of
**pinned** sum-check round relations

  `relationRoundPinned P i := relationRound i ∩ { x | x.1.2 = fun _ => P }`

(the plain sum-check round relation *conjoined with* the identity of the polynomial oracle), and
the perfect completeness of both the per-round and the fully composed sum-check oracle reduction
along this family.  This is exactly the missing oracle pass-through fact blocking the
completeness side of `composedPIOPTightFull_Rc` (`FirstSumcheckWithTarget.lean`): the
completeness-side compatible context is over the *prover's* output, and the plain
`relationRound` endpoints cannot see that the polynomial oracle is forwarded unchanged.

The mathematical content is structural, not probabilistic: the honest per-round prover *forwards*
its polynomial oracle (`receiveChallenge` outputs `fun _ => (poly, hp)` destructured from its
input state), and every round's oracle verifier routes its single output oracle from its single
input oracle under canonical output materialization.  So on **every** point of the run support — for
any query answers, hence under any simulation — the output oracle equals the input oracle, and the
pinned conjunct rides along the existing (unconditional) completeness for free.

Main results:

* `Reduction.perfectCompleteness_strengthen_support`: generic — perfect completeness survives
  adding any output-relation conjunct that holds on the run support (and shrinking the input
  relation).
* `Reduction.mem_support_verifier_run_of_mem_support_run`: generic — a successful
  `Reduction.run` outcome's verifier output is in the verifier's own run support on the produced
  transcript (the *decomposition* converse of `mem_support_run_of_prover_verifier`).
* `Sumcheck.Spec.SingleRound.mem_support_oracleVerifier_run_oStmt`: per-round oracle
  pass-through (single-round analogue of the composed
  `Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt` of `SumcheckPhaseRbr.lean`).
* `Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness_pinned`: per-round enriched
  completeness `relationRoundPinned P i.castSucc → relationRoundPinned P i.succ` (conditional
  only on the same lens coherence `[coh]` as the plain per-round completeness).
* `Sumcheck.Spec.oracleReduction_perfectCompleteness_pinned` /
  `…_pinned_unconditional`: the composed pinned completeness `relationRoundPinned P 0 →
  relationRoundPinned P (Fin.last n)` for every `P`, assembled through the relation-generic
  n-ary keystone `OracleReduction.seqCompose_perfectCompleteness_threaded` (instantiated at
  `rel := relationRoundPinned P`), with the coherence residual discharged by the proven
  `SingleRound.coh_proven_inst` in the unconditional form. -/

open OracleComp OracleSpec ProtocolSpec MvPolynomial Polynomial
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- **Run-support decomposition (verifier side).** Any *successful* outcome
`some ((td, prv), vOut)` in the support of `Reduction.run` has its verifier output `vOut` in the
support of the verifier's own run on the input statement and the produced transcript `td`.

This is the decomposition converse of `Reduction.mem_support_run_of_prover_verifier`
(`AppendCompletenessHelper.lean`); it lets support-level facts about the verifier (e.g. the
oracle pass-through `mem_support_oracleVerifier_run_oStmt`) be consumed on reduction-run support
points. -/
theorem mem_support_verifier_run_of_mem_support_run
    (red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    {td : FullTranscript pSpec} {prv : StmtOut × WitOut} {vOut : StmtOut}
    (hy : some ((td, prv), vOut) ∈ support (OptionT.run (red.run stmt wit))) :
    some vOut ∈ support (OptionT.run (red.verifier.run stmt td)) := by
  rw [Reduction.run_run_eq_bind, mem_support_bind_iff] at hy
  obtain ⟨pr, _, hrest⟩ := hy
  rw [mem_support_bind_iff] at hrest
  obtain ⟨vOpt, hv, hout⟩ := hrest
  cases vOpt with
  | none => simp at hout
  | some v =>
    simp only [Option.map_some, support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    simpa only [OracleComp.support_liftComp] using hv

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Support-conjunct strengthening of perfect completeness.** If a reduction is perfectly
complete for `relIn → relOut`, then it is perfectly complete for any smaller input relation
`relIn' ⊆ relIn` and any output relation `relOut'` that the completeness event *together with*
run-support membership implies.  (Used with `relOut' = relOut ∩ B` for a support-invariant `B`,
e.g. the polynomial-oracle pass-through pin.)

The probability content is one `probEvent_mono` over the completeness experiment; run-support
membership of the experiment outcome is transported to the **un-simulated** `Reduction.run`
support via `support_simulateQ_run'_subset` (simulation can only shrink support). -/
theorem perfectCompleteness_strengthen_support
    [∀ i, SampleableType (pSpec.Challenge i)]
    {red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (h : red.perfectCompleteness init impl relIn relOut)
    (hIn : relIn' ⊆ relIn)
    (hPin : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn' →
      ∀ out : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut,
        some out ∈ support (OptionT.run (red.run stmtIn witIn)) →
        (out.2, out.1.2.2) ∈ relOut → out.1.2.1 = out.2 → (out.2, out.1.2.2) ∈ relOut') :
    red.perfectCompleteness init impl relIn' relOut' := by
  intro stmtIn witIn hmem
  refine le_trans (h stmtIn witIn (hIn hmem)) (prEvent_mono_of_support _ _ _ ?_)
  rintro ⟨⟨tr, prvStmtOut, witOut⟩, stmtOut⟩ hx ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨s, _, hx⟩ := hx
  exact hPin stmtIn witIn hmem _
    (_root_.support_simulateQ_run'_subset _ _ s hx) h1 h2

end Reduction

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι}

/-- **The `P`-pinned sum-check round relation** (issue #329): the plain `relationRound`
conjoined with the identity of the (single) polynomial oracle.  The honest sum-check prover
forwards its polynomial oracle unchanged and every round's oracle verifier routes its output
oracle from its input oracle, so completeness holds round-to-round along this family for every
fixed `P` — which is what lets a lens-side consumer pin the inner polynomial to the projected
virtual polynomial. -/
def relationRoundPinned (R : Type) [CommSemiring R] (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
    (P : R⦃≤ deg⦄[X Fin n]) (i : Fin (n + 1)) :
    Set (((StatementRound R n i) × (∀ j, OracleStatement R n deg j)) × Unit) :=
  relationRound R n deg D i ∩ { x | x.1.2 = fun _ => P }

omit [DecidableEq R] [SampleableType R] in
lemma mem_relationRoundPinned_iff {P : R⦃≤ deg⦄[X Fin n]} {i : Fin (n + 1)}
    {x : ((StatementRound R n i) × (∀ j, OracleStatement R n deg j)) × Unit} :
    x ∈ relationRoundPinned R n deg D P i ↔
      x ∈ relationRound R n deg D i ∧ x.1.2 = fun _ => P :=
  Iff.rfl

namespace SingleRound

/-- The canonical round materializes the unchanged input polynomial oracle, including its
virtual output representation. -/
theorem oracleVerifier_materializeOutput_eq_input (i : Fin n)
    (chals : (pSpec R deg).Challenges) (oStmt : ∀ j, OracleStatement R n deg j)
    (messages : (pSpec R deg).Messages) :
    (oracleVerifier R n deg D oSpec i).materializeOutput chals oStmt messages = oStmt := rfl

/-- Every reachable compiled round output carries the unchanged input polynomial oracle. -/
theorem mem_support_oracleVerifier_run_oStmt {i : Fin n}
    {stmt : StatementRound R n i.castSucc} {oStmt : ∀ j, OracleStatement R n deg j}
    {tr : FullTranscript (pSpec R deg)}
    {out : StatementRound R n i.succ × ∀ j, OracleStatement R n deg j}
    (h : out ∈ support ((oracleVerifier R n deg D oSpec i).toVerifier.run (stmt, oStmt) tr)) :
    out.2 = oStmt := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image] at h
  obtain ⟨result, _, hresult⟩ := h
  cases result with
  | none => simp at hresult
  | some stmtOut =>
    simp only [Option.map_some, Option.some.injEq] at hresult
    have hOracle := congrArg Prod.snd hresult
    rw [oracleVerifier_materializeOutput_eq_input] at hOracle
    exact hOracle.symm

/-- **Per-round run-level oracle pass-through.** Any successful outcome of the `i`-th-round
sum-check oracle reduction's run has verifier-output oracle equal to the input oracle. -/
theorem mem_support_run_oStmt {i : Fin n}
    {stmt : StatementRound R n i.castSucc} {oStmt : ∀ j, OracleStatement R n deg j}
    {witIn : Unit}
    {td : FullTranscript (pSpec R deg)}
    {prv : (StatementRound R n i.succ × ∀ j, OracleStatement R n deg j) × Unit}
    {vOut : StatementRound R n i.succ × ∀ j, OracleStatement R n deg j}
    (h : some ((td, prv), vOut) ∈ support
      (OptionT.run ((oracleReduction R n deg D oSpec i).toReduction.run (stmt, oStmt) witIn))) :
    vOut.2 = oStmt :=
  mem_support_oracleVerifier_run_oStmt
    ((OptionT.mem_support_iff _ _).mpr
      (Reduction.mem_support_verifier_run_of_mem_support_run _ (stmt, oStmt) witIn h))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **Per-round oracle perfect completeness, pinned (issue #329).**

The `i`-th-round sum-check oracle reduction is perfectly complete from
`relationRoundPinned P i.castSucc` to `relationRoundPinned P i.succ`, for every fixed polynomial
`P`.  The plain part is the existing `SingleRound.oracleReduction_perfectCompleteness` (with the
same single coherence residual `[coh]`); the pinned conjunct holds on the *entire* run support
because the verifier routes its output oracle from its input oracle
(`mem_support_run_oStmt`). -/
theorem oracleReduction_perfectCompleteness_pinned [Fintype R] [Inhabited R]
    [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    (P : R⦃≤ deg⦄[X Fin n]) (i : Fin n)
    [coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier] :
    (oracleReduction R n deg D oSpec i).perfectCompleteness init impl
      (relationRoundPinned R n deg D P i.castSucc) (relationRoundPinned R n deg D P i.succ) := by
  refine Reduction.perfectCompleteness_strengthen_support
    (oracleReduction_perfectCompleteness_of_liftContextCoherent
      (init := init) (impl := impl) (_coh := coh) i)
    Set.inter_subset_left ?_
  rintro ⟨stmt, oStmt⟩ witIn ⟨_, hpin⟩ ⟨⟨td, prv⟩, vOut⟩ hsupp h1 _
  refine ⟨h1, ?_⟩
  have hpass : vOut.2 = oStmt := mem_support_run_oStmt hsupp
  show vOut.2 = fun _ => P
  rw [hpass]
  exact hpin

end SingleRound

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

section Composed

variable [Fintype R] [Inhabited R] [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]

-- As in `OracleCompletenessThreaded.lean`: the `@`-applied keystone elaborates a large dependent
-- `seqCompose` `toReduction` bridge, so we raise the heartbeat limit.
set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **Composed multi-round sum-check perfect completeness, pinned (issue #329, task K).**

For every fixed polynomial `P`, the full sum-check oracle reduction is perfectly complete from
`relationRoundPinned P 0` to `relationRoundPinned P (Fin.last n)`: the terminal relation *pins
the carried polynomial oracle* in addition to the terminal sum-check claim.  Assembled through
the relation-generic n-ary keystone `OracleReduction.seqCompose_perfectCompleteness_threaded`
instantiated at `rel := relationRoundPinned P`, from the per-round pinned completeness
`SingleRound.oracleReduction_perfectCompleteness_pinned` — exactly the assembly of the plain
`oracleReduction_perfectCompleteness` (`OracleCompletenessThreaded.lean`) along the enriched
relation family. -/
theorem oracleReduction_perfectCompleteness_pinned
    (P : R⦃≤ deg⦄[X Fin n])
    [coh : ∀ i, OracleVerifier.LiftContextCoherent (SingleRound.sumcheckOracleLens R n deg D oSpec i)
      (SingleRound.Simple.oracleReduction R deg D oSpec).verifier]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRoundPinned R n deg D P 0) (relationRoundPinned R n deg D P (Fin.last n)) := by
  exact OracleReduction.seqCompose_pc_oracle_msg'
    (init := init) (impl := impl)
    (StatementRound R n) (fun _ => OracleStatement R n deg) (fun _ => Unit)
    (SingleRound.oracleReduction R n deg D oSpec)
    (fun i => relationRoundPinned R n deg D P i)
    (fun _ => inferInstance) (fun _ => SingleRound.chalFintype)
    (fun _ => SingleRound.chalInhab)
    (fun _ => ⟨by omega, SingleRound.pSpec_dir_zero⟩)
    hInit hImplSupp
    (fun i => SingleRound.oracleReduction_perfectCompleteness_pinned (coh := coh i) P i)

set_option linter.unusedFintypeInType false in
/-- **Composed pinned completeness, UNCONDITIONAL.** The per-round lens coherence residual is
discharged by the proven `CubeFiber` coherence (`SingleRound.coh_proven_inst`), exactly as in
the plain `oracleReduction_perfectCompleteness_unconditional`
(`OracleCompletenessUncondCorrect.lean`).  Only the standard honest data facts
`hInit`/`hImplSupp` remain. -/
theorem oracleReduction_perfectCompleteness_pinned_unconditional
    (P : R⦃≤ deg⦄[X Fin n])
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRoundPinned R n deg D P 0) (relationRoundPinned R n deg D P (Fin.last n)) :=
  oracleReduction_perfectCompleteness_pinned
    (coh := fun i => SingleRound.coh_proven_inst i) P hInit hImplSupp

end Composed

end Sumcheck.Spec

#print axioms Reduction.mem_support_verifier_run_of_mem_support_run
#print axioms Reduction.perfectCompleteness_strengthen_support
#print axioms Sumcheck.Spec.SingleRound.mem_support_oracleVerifier_run_oStmt
#print axioms Sumcheck.Spec.SingleRound.mem_support_run_oStmt
#print axioms Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness_pinned
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness_pinned
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness_pinned_unconditional

#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_materializeOutput_eq_input
