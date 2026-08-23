/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.RunUnroll
import ArkLib.ToVCVio.Simulation
open OracleComp OracleSpec ProtocolSpec OptionTStateT

/-!
# The basic Fiat-Shamir transformed run IS the honest execution (syntactically)

`fiatShamir_run_eq_honestExecution_holds` discharges the named run-equality residual: the
basic Fiat-Shamir transformed reduction's run equals the lifted explicit honest execution on
the nose. The proof unrolls the one-message run shell, then crosses the OptionT
lift-coherence wall (the two-step associativity-routed lift chosen by `run` vs the direct
lift): every coherence square is closed by `OracleComp.inductionOn` with per-`Sum`-branch
defeq (`rcases t <;> bind_congr`) — the instance paths differ syntactically but agree on
each routed query. The `simulateQ`-of-query-routing collapses (`hsim`/`hsimGen`), the
OptionT-level path bridge (`hLHS`), and a four-path coherence square on the verifier leg are
all proven inline by the same recipe.

This feeds `fiatShamir_runCollapseResidual_holds` (below) and through it the entire basic-FS
completeness consumer chain (`fiatShamir_completeness_of_runEq` etc., `Basic.lean`).
-/

namespace Reduction
variable {n : ℕ} {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {pSpec : ProtocolSpec n} [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, VCVCompatible (pSpec.Challenge i)]

attribute [local instance] fiatShamirChallengeOracleInterface

/-- Cross-instance lift coherence: lifting a query's own-spec computation into a sum spec
agrees with the direct query lift. -/
private lemma liftM_liftM_query {ι₁ ι₂ : Type} {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂}
    (t : s₁.Domain) :
    (liftM (liftM (OracleSpec.query t) : OracleComp s₁ _) : OracleComp (s₁ + s₂) _)
      = liftM (OracleSpec.query t) := by
  show liftComp ((OracleSpec.query t : OracleQuery s₁ _) : OracleComp s₁ _) (s₁ + s₂)
    = liftM (OracleSpec.query t)
  rw [liftComp_query]
  simp [OracleQuery.cont_query, OracleQuery.input_query, id_map]

set_option maxHeartbeats 6000000 in
theorem fiatShamir_run_eq_honestExecution_holds
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    fiatShamir_run_eq_honestExecution R stmtIn witIn := by
  unfold fiatShamir_run_eq_honestExecution
  rw [fiatShamir_run_eq_oneMessage]
  unfold fiatShamirHonestExecution
  simp only [Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir, Verifier.run,
    fiatShamir_sendMessage_eq_raw, Verifier.fiatShamir_verify_eq,
    liftM_bind, liftM_pure, bind_assoc, pure_bind, OptionT.run_bind]
  simp only [OptionT.liftM_run_getM_bind, lift_run_elim, Option.elimM, liftM_bind,
    liftM_pure, bind_assoc, pure_bind, map_bind, bind_map_left]
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_liftM_run,
    OracleComp.liftM_OptionT_eq, OptionT.run_pure, map_eq_bind_pure_comp,
    liftM_bind, liftM_pure, bind_assoc, pure_bind]
  have hsim : ∀ {α : Type} (X : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α),
      simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ) _)) X
        = liftM X := by
    intro α X
    induction X using OracleComp.inductionOn with
    | pure a => exact (liftM_pure _).symm
    | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, liftM_bind]
      rcases t with t₁ | t₂
      · exact bind_congr fun a => ih a
      · exact bind_congr fun a => ih a
  have hsimGen : ∀ (impl : QueryImpl oSpec
        (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
      (himpl : ∀ t, impl t = liftM (OracleSpec.query t))
      {α : Type} (X : OracleComp oSpec α),
      simulateQ impl X = liftM X := by
    intro impl himpl α X
    induction X using OracleComp.inductionOn with
    | pure a => exact (liftM_pure _).symm
    | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, himpl]
      first
      | exact bind_congr fun a => ih a
      | (rw [show (liftM (liftM (OracleSpec.query t) : OracleComp oSpec _) :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) _)
            = liftM (OracleSpec.query t) from rfl]
         exact bind_congr fun a => ih a)
  have hll : ∀ {α : Type} (X : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α),
      (liftM (liftM X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
        = liftM X := fun X => rfl
  have hLHS : ∀ {α : Type} (X : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α),
      (@liftM (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
        (OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
        (instMonadLiftTOfMonadLift
          (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
          (OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))))
        α X)
      = (liftM X : OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
    intro α X
    apply OptionT.ext
    induction X using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t oa ih =>
      rcases t with t₁ | t₂ <;>
        (simp only [liftM_bind]; exact bind_congr fun a => ih a)
  simp only [hsim, hll, hLHS, Function.comp, liftM_pure, pure_bind, Option.elimM,
    OptionT.run_pure, OptionT.run_bind, bind_assoc]
  apply bind_congr; intro d
  rcases d with _ | d
  · rfl
  apply bind_congr; intro e
  rcases e with _ | e
  · rfl
  apply bind_congr; intro f
  rcases f with _ | f
  · rfl
  simp only [Option.elim]
  refine Eq.trans
    (congrArg₂ (· >>= ·) (congrArg (fun Y => OptionT.run (liftM Y))
      (hsimGen _ (fun t => by with_unfolding_all rfl) _)) rfl) ?_
  beta_reduce
  congr 1
  · induction (R.verifier.verify stmtIn f).run using OracleComp.inductionOn with
    | pure a =>
      first
      | rfl
      | with_unfolding_all rfl
    | query_bind t oa ih =>
      simp only [liftM_bind]
      first
      | exact bind_congr fun a => ih a
      | (congr 1
         · with_unfolding_all rfl
         all_goals funext a
         all_goals exact ih a)
  all_goals funext g
  rcases g with _ | g
  · rfl
  rcases g with _ | s <;> rfl

/-- **The basic Fiat-Shamir challenge-collapse residual is DISCHARGED**: the syntactic
run-equality above feeds the named constructor. -/
theorem fiatShamir_runCollapseResidual_holds
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    fiatShamir_runCollapseResidual impl R stmtIn witIn :=
  fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
    (fiatShamir_run_eq_honestExecution_holds R stmtIn witIn)

end Reduction

-- Axiom audit: must report only [propext, Classical.choice, Quot.sound] (no sorryAx).
#print axioms Reduction.fiatShamir_run_eq_honestExecution_holds
#print axioms Reduction.fiatShamir_runCollapseResidual_holds
