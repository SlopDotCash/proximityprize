/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ProofSystem.Spartan.TightSecondCompleteness
import ArkLib.ProofSystem.Spartan.TightConjoinedSecondLeaf
import ArkLib.ToVCVio.Lemmas
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Tight terminal completeness: `finalCheckTight` + the binding strengthening (#329, B7, task R2)

The two completeness pieces closing the tail of the tight chain:

1. **The pred-generic oracle-`CheckClaim` completeness** (`CheckClaim` namespace): for *any*
   oracle predicate, the compiled `CheckClaim` oracle reduction is perfectly complete as a
   relation pass-through.  The oracle `CheckClaim` verifier *discards* its predicate's `Prop`
   (`do let _ ← pred stmt; return stmt`), the only `OptionT` failure entry points
   (`guard`/`failure`) are absent, and both prover and verifier forward the input
   statement/oracle pair unchanged — so the honest run never fails and outputs the input pair,
   whatever (symbolically many) oracle queries the predicate makes.  Unlike the binding-free
   `finalCheck` leaf (`FinalCheckLeafComplete.lean`), the run does **not** collapse to a literal
   `pure`; the collapse is to "(simulated, discarded) predicate, then `pure (some pair)`"
   (`toReduction_run_run_eq`).

2. **The Spartan instantiations**:
   * `finalCheckTight_perfectCompleteness` — the tight terminal check carries
     `(e₂-direct ∧ binding)` into `tightFinalRelOut` (the two relations agree conjunct-by-
     conjunct at the pass-through pair);
   * `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` — the carried second
     sum-check's enriched completeness (`TightSecondCompleteness.lean`) strengthened by the
     first-terminal binding pass-through, via
     `Reduction.perfectCompleteness_strengthen_support` (`PinnedCompleteness.lean`): the lifted
     verifier is failing-deterministic with verdict `(v? (proj s) tr).map (lift s)`
     (`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`, the
     `TightConjoinedSecondLeaf.lean` `hPres` pattern), and the lift forwards the passenger
     statement and oracles, so `bindingAtSecondIn` rides through to `bindingAtSecondOut` on the
     whole run support.

The output relation of (2) is definitionally the input relation of (1), so together they hand
the completeness fold the last two legs of the honest tight chain.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec
open scoped NNReal

universe u v

namespace CheckClaim

variable {ι : Type} {oSpec : OracleSpec ι} {Statement : Type}
  {ιₛ : Type} {OStatement : ιₛ → Type} [∀ i, OracleInterface (OStatement i)]
  (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)

omit [∀ i, OracleInterface (OStatement i)] in
/-- The oracle `CheckClaim` prover is a deterministic pass-through: empty transcript, unchanged
statement/oracle pair, unit witness. -/
lemma oracleProver_run (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    (oracleProver oSpec Statement OStatement).run (stmt, oStmt) () =
      pure ((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()) := rfl

/-! ## Generic support transport lemmas

These are applied (not rewritten), so they unify up to definitional unfolding of
`OptionT.run`/`OptionT.mk` and the monad-lift instance chains. -/

/-- Outputs of a simulated computation (into another `OracleComp`) are outputs of the original
computation. `OracleComp`-target analogue of `support_simulateQ_run'_subset`. -/
private lemma support_simulateQ_subset' {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {α : Type} (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y with
  | pure x => simpa [simulateQ_pure] using hy
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, support_bind, Set.mem_iUnion] at hy ⊢
      aesop

/-- A simulated `some`-wrapped computation only outputs `some`. -/
private lemma head_some {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {γ : Type} (Y : OracleComp spec γ)
    {o : Option γ}
    (h : o ∈ support (simulateQ impl (Y >>= fun x => pure (some x)))) :
    ∃ y, o = some y := by
  have h' := support_simulateQ_subset' impl _ h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h'
  obtain ⟨y, -, rfl⟩ := h'
  exact ⟨y, rfl⟩

/-- A simulated `pure (some b)` only outputs `some b`. -/
private lemma mem_support_pure_optionT {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {γ : Type} (b : γ) {o : Option γ}
    (h : o ∈ support (simulateQ impl (pure (some b) : OracleComp spec (Option γ)))) :
    o = some b := by
  rw [simulateQ_pure] at h
  simpa using h

/-- Membership in the support of a `pure` pins the value. Applied (defeq-unified) against
computations that reduce to `pure` definitionally (e.g. `Fin.induction` at round `0`). -/
private lemma mem_support_pure_eq {ι₁ : Type u} {spec : OracleSpec ι₁}
    {α : Type} {b c : α} (h : c ∈ support (pure b : OracleComp spec α)) : c = b := by
  simpa using h

/-- `OptionT`-level probability-one bridge with sampled initial state: if every output of the
underlying computation is a `some` satisfying `P`, the simulated experiment satisfies `P` with
probability one. Init-sampling version of `OptionT.probEvent_eq_one_of_simulateQ_support`. -/
private lemma probEvent_eq_one_of_support_init
    {ι₁ σ α : Type} {spec : OracleSpec ι₁}
    (impl : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    (oa : OracleComp spec (Option α)) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk (do (simulateQ impl oa).run' (← init))] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (do (simulateQ impl oa).run' (← init) : ProbComp _)] = 0 :=
      HasEvalPMF.probFailure_eq_zero _
    rw [hfail, _root_.zero_add]
    refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
    simp only [support_bind, Set.mem_iUnion] at hnone
    obtain ⟨s, -, hnone⟩ := hnone
    have hmem := _root_.support_simulateQ_run'_subset impl oa s hnone
    obtain ⟨a, ha, -⟩ := h none hmem
    cases ha
  · intro y hy
    rw [OptionT.mem_support_iff] at hy
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hy
    obtain ⟨s, -, hy⟩ := hy
    obtain ⟨a, ha, hP⟩ := h (some y) (_root_.support_simulateQ_run'_subset impl oa s hy)
    cases ha
    exact hP

/-- **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the
run only ever outputs `some (stmt, oStmt)` — there is no failure entry point, and the
predicate's (simulated, `some`-wrapped) value is discarded. -/
private theorem support_toVerifier_run (stmt : Statement) (oStmt : ∀ i, OStatement i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    ∀ x ∈ support (((oracleVerifier oSpec Statement OStatement pred).toVerifier.run
        (stmt, oStmt) tr).run), x = some (stmt, oStmt) := by
  intro x hx
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier] at hx
  rw [OptionT.run_bind] at hx
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift] at hx
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure,
    Option.elimM, support_bind, Set.mem_iUnion] at hx
  rw [simulateQ_optionT_bind] at hx
  simp only [OptionT.run_bind, Option.elimM, support_bind, Set.mem_iUnion] at hx
  obtain ⟨i, ⟨i1, hi1, hi⟩, hxm⟩ := hx
  obtain ⟨y, rfl⟩ := head_some _ _ hi1
  rw [Option.elim_some] at hi
  have hstmt := mem_support_pure_optionT _ _ hi
  subst hstmt
  rw [Option.elim_some] at hxm
  rw [OptionT.run_pure] at hxm
  simp only [support_pure, Set.mem_singleton_iff] at hxm
  subst hxm
  rfl

/-- **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**:
the run only ever outputs the default transcript together with the unchanged
statement/oracle-statement pair (from both prover and verifier). -/
private theorem support_oracleReduction_run (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    ∀ x ∈ support ((((oracleReduction oSpec Statement OStatement pred).toReduction.run
        (stmt, oStmt) ()).run)),
      x = some ((default, (stmt, oStmt), ()), (stmt, oStmt)) := by
  intro x hx
  simp only [oracleReduction, OracleReduction.toReduction, oracleProver, Reduction.run,
    Prover.run, Prover.runToRound] at hx
  rw [OptionT.run_bind] at hx
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift] at hx
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure,
    Option.elimM, support_bind, Set.mem_iUnion, OptionT.run_bind] at hx
  obtain ⟨i, ⟨i1, ⟨i0, hi0, ⟨i2, hi2, hi1⟩⟩, hii⟩, hxm⟩ := hx
  have hi0' := mem_support_pure_eq hi0
  subst hi0'
  rw [OracleComp.liftComp_pure] at hi2
  have hi2' := mem_support_pure_eq hi2
  subst hi2'
  have hi1' := mem_support_pure_eq hi1
  subst hi1'
  have hii' := mem_support_pure_eq hii
  subst hii'
  rw [Option.elim_some] at hxm
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hxm
  obtain ⟨o, ⟨v, hv, rfl⟩, hxm⟩ := hxm
  have hv' := support_toVerifier_run pred stmt oStmt _ v (support_simulateQ_subset' _ _ hv)
  subst hv'
  rw [Option.elim_some] at hxm
  simp only [Option.getM, OptionT.run_pure, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hxm
  obtain ⟨o, rfl, hxm⟩ := hxm
  rw [Option.elim_some] at hxm
  exact mem_support_pure_eq hxm

/-- **The oracle `CheckClaim` reduction is perfectly complete as a relation pass-through**, for
*any* oracle predicate: the verifier never fails (the predicate's `Prop` is discarded, no
`guard` exists, and `OracleComp` is total), and both prover and verifier forward the
statement/oracle pair unchanged. -/
theorem oracleReduction_perfectCompleteness_passthrough {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn relOut : Set ((Statement × (∀ i, OStatement i)) × Unit)}
    (_hInit : NeverFail init)
    (h : ∀ p, (p, ()) ∈ relIn → (p, ()) ∈ relOut) :
    (oracleReduction oSpec Statement OStatement pred).perfectCompleteness init impl
      relIn relOut := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  rw [ge_iff_le, one_le_probEvent_iff]
  refine probEvent_eq_one_of_support_init _ _ _ _ ?_
  intro y hy
  have hval := support_oracleReduction_run pred stmt oStmt y hy
  subst hval
  exact ⟨_, rfl, h _ hIn, rfl⟩

end CheckClaim


namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Completeness leaf for the tight terminal check** (#329, B7): `finalCheckTight` carries the
conjoined `(e₂-direct ∧ binding)` relation — the output of the binding-strengthened carried
second sum-check — into `tightFinalRelOut`.  The implication is conjunct-by-conjunct at the
pass-through pair: `e₂-direct` *is* `tightFinalRelOut`'s first conjunct and the binding is its
second. -/
theorem finalCheckTight_perfectCompleteness (hInit : NeverFail init) :
    (finalCheckTight (R := R) pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) :=
  CheckClaim.oracleReduction_perfectCompleteness_passthrough (tightFinalPredicate pp)
    hInit (fun _ hp => ⟨hp.1, hp.2⟩)

set_option linter.unusedFintypeInType false in
/-- **The binding strengthening of the carried second sum-check completeness** (#329, B7): the
enriched completeness (`secondSumcheckWithTarget_perfectCompleteness_enriched`) conjoined with
the first-terminal binding identity as a pass-through invariant, at the same honest hypotheses.

The pass-through fact is supported on the *whole run support*: the lifted verifier is
failing-deterministic with verdict `(v? (proj s) tr).map (lift s)`
(`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`), and the lift
forwards the passenger statement and the oracles untouched. -/
theorem secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp})
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp}) := by
  have h := secondSumcheckWithTarget_perfectCompleteness_enriched (R := R) pp oSpec
    (init := init) (impl := impl) hInit hImplSupp
  unfold OracleReduction.perfectCompleteness at h ⊢
  refine Reduction.perfectCompleteness_strengthen_support h Set.inter_subset_left ?_
  rintro stmtIn witIn ⟨_, hBind⟩ ⟨⟨td, prv⟩, vOut⟩ hsupp hRel _
  refine ⟨hRel, ?_⟩
  -- Run-support decomposition: the verifier output is in the verifier's own run support.
  have hv : some vOut ∈ support (OptionT.run
      ((secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.run
        stmtIn td)) :=
    Reduction.mem_support_verifier_run_of_mem_support_run _ stmtIn witIn hsupp
  -- Failing-determinism: the lifted verifier's verdict is `(v? (proj s) tr).map (lift s)`.
  obtain ⟨v?, hvdet⟩ := sumcheckFull_toVerifier_isFailingDet
    (R := R) (oSpec := oSpec) 2 (boolEmbedding R) pp.ℓ_n
  have hcomm := (secondSumcheckCoherentWithTarget (R := R) pp oSpec).toVerifier_comm
  have hVeq : (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun s tr => OptionT.mk (pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj s) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift s)))⟩ := by
    refine hcomm.trans ?_
    exact Verifier.liftContext_failingDet
      (secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens _ v? hvdet
  rw [hVeq] at hv
  simp only [Verifier.run, OptionT.run_mk, support_pure, Set.mem_singleton_iff] at hv
  -- Extract the inner output and the lift shape; the lift forwards the passenger data.
  rcases hverd : (v? ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      stmtIn) td) with _ | so
  · rw [hverd] at hv
    simp at hv
  · rw [hverd] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    obtain ⟨⟨T, stmt⟩, oStmt⟩ := stmtIn
    obtain ⟨⟨t', r_y⟩, innerO⟩ := so
    rw [hv]
    exact hBind

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms CheckClaim.oracleProver_run
#print axioms CheckClaim.oracleReduction_perfectCompleteness_passthrough
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
