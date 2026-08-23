/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.RunUnroll
open OracleComp OracleSpec ProtocolSpec OptionTStateT
/-!
# The DSFS transformed run IS the honest execution (syntactically)

`duplexSpongeFiatShamir_run_eq_honestExecution_holds`: the unsalted duplex-sponge Fiat-Shamir
transformed reduction's run equals the lifted explicit honest execution on the nose,
discharging the named run-equality residual and through it
`duplexSpongeFiatShamir_runCollapseResidual` (the DSFS completeness chain's gate).

The proof composes this campaign's full coherence arsenal (see
`docs/wiki/optiont-lift-coherence-walls.md` and `Security/LiftCoherence.lean`): the
one-message shell unroll, the `getM`/`elim` collapses, `OptionT.ext` + run-level
normalization, the `dsfs_hLHS`/`dsfs_hLHS₂` path bridges as `congr`-head closers, whole-goal
induction on the verifier computation for the (Option-depth-misaligned) verify leg, and a
single depth-equalizing pin whose spelling REQUIRES the transform's `ProtocolSpec (0 + 1)`
length form (literal `1` mints structurally different `Fin.vcons` families — the final
lesson of the campaign).
-/

namespace Reduction
variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

local instance dsfsChallengeOracleInterface :
    ∀ i : (⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
      ProtocolSpec 1).ChallengeIdx,
      OracleInterface ((⟨!v[Direction.P_to_V],
        !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
        ProtocolSpec 1).Challenge i) :=
  challengeOracleInterface

/-- Run-characterization of the composite lift (left-inclusion). -/
theorem optionT_liftM_run_add_left' {ι₁ ι₂ : Type}
    {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {α : Type} (X : OracleComp s₁ α) :
    ((liftM X : OptionT (OracleComp (s₁ + s₂)) α)).run
    = simulateQ (fun t => ((liftM ((OracleSpec.query t : OracleQuery s₁ _)) :
        OracleQuery (s₁ + s₂) _) : OracleComp (s₁ + s₂) _))
        (X >>= fun x => pure (some x)) := rfl

theorem optionT_liftM_run_assoc_path' {ι₁ ι₂ ι₃ : Type}
    {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {s₃ : OracleSpec ι₃}
    {α : Type} (X : OracleComp (s₁ + s₂) α) :
    ((@liftM (OracleComp (s₁ + s₂)) (OptionT (OracleComp (s₁ + s₂ + s₃)))
      (instMonadLiftTOfMonadLift (OracleComp (s₁ + s₂))
        (OptionT (OracleComp (s₁ + (s₂ + s₃))))
        (OptionT (OracleComp (s₁ + s₂ + s₃))))
      α X)).run
    = simulateQ (fun t => ((liftM ((OracleSpec.query t :
        OracleQuery (s₁ + (s₂ + s₃)) _)) : OracleQuery (s₁ + s₂ + s₃) _) :
        OracleComp (s₁ + s₂ + s₃) _))
        (simulateQ (fun t => ((liftM ((OracleSpec.query t :
          OracleQuery (s₁ + s₂) _)) : OracleQuery (s₁ + (s₂ + s₃)) _) :
          OracleComp (s₁ + (s₂ + s₃)) _))
          (X >>= fun x => pure (some x))) := rfl

/-- Bridge: annotated (assoc-routed) vs direct lift of a single right-side query. -/
theorem dsfs_lift_query_bridge_inr (t₂ : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    (@liftM (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)))
      (instMonadLiftTOfMonadLift
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
      _ ((liftM ((OracleSpec.query (Sum.inr t₂) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _))) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
    = (liftM (liftM ((OracleSpec.query (Sum.inr t₂) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) _) := by
  apply OptionT.ext
  show (simulateQ (fun t => (liftM ((OracleSpec.query (Sum.inl t) :
      OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ) _)) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ) _))
      (some <$> (liftM (OracleSpec.query (Sum.inr t₂)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _)))
    = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  first
  | simp only [simulateQ_spec_query]
  | rw [show (simulateQ (fun t => (liftM ((OracleSpec.query (Sum.inl t) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ) _))
      (liftM ((OracleSpec.query (Sum.inr t₂) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
      = (liftM ((OracleSpec.query (Sum.inl (Sum.inr t₂)) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ) _) from by with_unfolding_all rfl]
  simp only [Function.comp, simulateQ_pure]
  refine Eq.trans (b := simulateQ (fun t => ((liftM ((OracleSpec.query t :
      OracleQuery (oSpec + (duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)) _)) :
      OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ) _) :
      OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ) _))
      (simulateQ (fun t => ((liftM ((OracleSpec.query t :
          OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
          OracleQuery (oSpec + (duplexSpongeChallengeOracle StmtIn U +
            [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
              ProtocolSpec 1).Challenge]ₒ)) _) :
          OracleComp (oSpec + (duplexSpongeChallengeOracle StmtIn U +
            [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
              ProtocolSpec 1).Challenge]ₒ)) _))
        ((liftM ((OracleSpec.query (Sum.inr t₂) :
          OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
          OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _) >>=
          fun x => pure (some x)))) ?_ (by rfl)
  rw [OracleComp.simulateQ_simulateQ]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, simulateQ_query,
    OracleQuery.liftM_add_left_query, OracleQuery.liftM_add_right_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, id_eq,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  have hroute : (liftM ((OracleSpec.query (Sum.inr t₂) :
      OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
      OracleQuery (oSpec + (duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)) _)
      = OracleSpec.query (Sum.inr (Sum.inl t₂)) := by
    rcases t₂ with s | (c | c) <;>
      first
      | rfl
      | with_unfolding_all rfl
  rw [hroute]
  simp only [OracleQuery.liftM_add_assoc_def, OracleQuery.liftM_add_assoc_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_eq, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp]
  first
  | rfl
  | with_unfolding_all rfl
  | trace_state


/-- Bridge: annotated vs direct lift of a single left-side query. -/
theorem dsfs_lift_query_bridge_inl (t₁ : oSpec.Domain) :
    (@liftM (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)))
      (instMonadLiftTOfMonadLift
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (OptionT (OracleComp (oSpec + (duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
      _ ((liftM ((OracleSpec.query (Sum.inl t₁) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _))) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
    = (liftM (liftM ((OracleSpec.query (Sum.inl t₁) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) _) := by
  first
  | rfl
  | with_unfolding_all rfl
  | trace_state


set_option maxHeartbeats 1000000 in
/-- The annotated (assoc-routed) lift equals the direct lift, for every computation: the
DS-hLHS. Induction with the two per-query bridges. -/
theorem dsfs_hLHS {α : Type}
    (X : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) :
    (@liftM (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)))
      (instMonadLiftTOfMonadLift
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (OptionT (OracleComp (oSpec + (duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
      α X)
    = (liftM X : OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) α) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    first
    | rfl
    | with_unfolding_all rfl
  | query_bind t oa ih =>
    simp only [liftM_bind]

#print axioms Reduction.dsfs_hLHS


/-- Bridge: annotated vs direct lift of a single left-side query. -/
theorem dsfs_lift_query_bridge_inl₂ (t₁ : oSpec.Domain) :
    (@liftM (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)))
      (instMonadLiftTOfMonadLift
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
      _ ((liftM ((OracleSpec.query (Sum.inl t₁) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _))) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
    = (liftM (liftM ((OracleSpec.query (Sum.inl t₁) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) _) := by
  first
  | rfl
  | with_unfolding_all rfl
  | trace_state



set_option maxHeartbeats 1000000 in
/-- Annotated lift through `OptionT (OracleComp base)` (the third path) = direct lift. -/
theorem dsfs_hLHS₂ {α : Type}
    (X : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) :
    (@liftM (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)))
      (instMonadLiftTOfMonadLift
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)))
        (OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ))))
      α X)
    = (liftM X : OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) α) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    first
    | rfl
    | with_unfolding_all rfl
  | query_bind t oa ih =>
    simp only [liftM_bind]
    rcases t with t₁ | t₂ <;>
      first
      | exact bind_congr fun a => ih a
      | (refine Eq.trans (congrArg₂ (· >>= ·) (dsfs_lift_query_bridge_inl₂ _) rfl) ?_
         all_goals first
           | (beta_reduce; exact bind_congr fun a => ih a)
           | exact bind_congr fun a => ih a
           | rfl)
      | (refine Eq.trans (congrArg₂ (· >>= ·) (dsfs_lift_query_bridge_inr _) rfl) ?_
         all_goals first
           | (beta_reduce; exact bind_congr fun a => ih a)
           | exact bind_congr fun a => ih a
           | rfl)
      | rfl

#print axioms Reduction.dsfs_hLHS₂


attribute [local instance] dsfsProverOnly dsfsSaltedProverOnly

set_option maxHeartbeats 2000000 in
theorem duplexSpongeFiatShamir_run_eq_honestExecution_holds
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    duplexSpongeFiatShamir_run_eq_honestExecution (U := U) R stmtIn witIn := by
  unfold duplexSpongeFiatShamir_run_eq_honestExecution
  rw [Reduction.run_of_prover_first stmtIn witIn (R.duplexSpongeFiatShamir (U := U))]
  unfold duplexSpongeFiatShamirHonestExecution duplexSpongeFiatShamirHonestRun
  simp only [Reduction.duplexSpongeFiatShamir, Prover.duplexSpongeFiatShamir,
    Verifier.duplexSpongeFiatShamir, Verifier.run, Verifier.duplexSpongeFiatShamir_verify_eq,
    liftM_bind, liftM_pure, bind_assoc, pure_bind, OptionT.run_bind]
  simp only [OptionT.liftM_run_getM_bind, lift_run_elim, Option.elimM, liftM_bind,
    liftM_pure, bind_assoc, pure_bind, map_bind, bind_map_left]
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_liftM_run,
    OracleComp.liftM_OptionT_eq, OptionT.run_pure, map_eq_bind_pure_comp,
    liftM_bind, liftM_pure, bind_assoc, pure_bind]
  have hsimGen : ∀ (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)))
      (himpl : ∀ t, impl t = liftM (OracleSpec.query t))
      {α : Type} (X : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α),
      simulateQ impl X = X := by
    intro impl himpl α X
    induction X using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, himpl]
      rcases t with t₁ | t₂ <;> exact bind_congr fun a => ih a
  have hll : ∀ {α : Type} (X : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α),
      (liftM (liftM X :
          OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) α) :
        OptionT (OracleComp ((oSpec + duplexSpongeChallengeOracle StmtIn U) +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec 1).Challenge]ₒ)) α)
        = liftM X := fun X => rfl
  have hLHS := fun {α : Type} (X : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α) => dsfs_hLHS (pSpec := pSpec) (oSpec := oSpec) X
  simp only [hll, hLHS, Function.comp, liftM_pure, pure_bind, Option.elimM,
    OptionT.run_pure, OptionT.run_bind, bind_assoc]
  iterate 3
    (congr 1
     all_goals first
       | rfl
       | exact congrArg OptionT.run (dsfs_hLHS₂ _)
       | exact congrArg OptionT.run (dsfs_hLHS₂ _).symm
       | skip
     all_goals try funext d
     all_goals try (rcases d with _ | d; · rfl))
  simp only [Option.elim]
  congr 1
  all_goals first
    | rfl
    | exact congrArg OptionT.run (dsfs_hLHS₂ _)
    | exact congrArg OptionT.run (dsfs_hLHS₂ _).symm
    | skip
  all_goals try funext g
  all_goals try (rcases g with _ | g; · rfl)
  dsimp only []
  induction (R.verifier.verify stmtIn g.2).run using OracleComp.inductionOn with
  | pure a =>
    rcases a with _ | a <;>
      first
      | rfl
      | with_unfolding_all rfl
      | (dsimp only []; rfl)
  | query_bind t oa ih =>
    simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, simulateQ_spec_query,
      simulateQ_query, simulateQ_pure, simulateQ_map,
      OracleQuery.liftM_add_left_query, OracleQuery.liftM_add_right_query,
      OracleQuery.liftM_add_assoc_def, OracleQuery.liftM_add_assoc_query,
      OracleQuery.liftM_right_add_right_add_def, OracleQuery.liftM_right_add_right_add_query,
      OracleQuery.input_query, OracleQuery.cont_query, id_eq, id_map, liftM_bind, liftM_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, Option.getM, Option.elim,
      OracleComp.simulateQ_simulateQ, liftM_OptionT_eq]
    first
    | rfl
    | exact bind_congr fun a => ih a
    | (refine Eq.trans (congrArg₂ (· >>= ·)
        (show (simulateQ (fun t' => (liftM (OracleSpec.query t') :
            OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
              [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec (0 + 1)).Challenge]ₒ) _))
            ((liftM ((liftM ((OracleSpec.query t : OracleQuery oSpec _)) :
              OracleComp oSpec _)) :
              OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _)).run)
          = ((liftM ((OracleSpec.query (Sum.inl (Sum.inl t)) :
              OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U +
                [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec (0 + 1)).Challenge]ₒ) _)) :
              OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
                [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec (0 + 1)).Challenge]ₒ) _) >>=
              fun x => pure (some x))
          from by with_unfolding_all rfl) rfl) ?_
       beta_reduce
       refine Eq.trans (bind_assoc _ _ _) ?_
       try simp only [pure_bind]
       first
       | exact bind_congr fun a => ih a
       | (apply bind_congr; intro a
          rcases a with _ | a
          · first | rfl | with_unfolding_all rfl
          · first
            | exact ih a
            | (simp only [Option.elim]; exact ih a)
            | (dsimp only []; exact ih a)))

set_option maxHeartbeats 4000000 in
/-- **The unsalted DSFS challenge-collapse residual is DISCHARGED**: rewrite by the
run-equality, then whole-goal induction on the honest execution — the pure case is
definitional, and the query case distributes the lifted bind via the pinned run-level
`elim` exposure and collapses the per-query routed head by case analysis through the
sponge oracle's internal domain sum. -/
theorem duplexSpongeFiatShamir_runCollapseResidual_holds
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    duplexSpongeFiatShamir_runCollapseResidual (U := U) impl R stmtIn witIn := by
  unfold duplexSpongeFiatShamir_runCollapseResidual
  rw [duplexSpongeFiatShamir_run_eq_honestExecution_holds R stmtIn witIn]
  induction (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn)
      using OracleComp.inductionOn with
  | pure a =>
    rcases a with _ | a <;>
      first
      | rfl
      | with_unfolding_all rfl
      | (dsimp only []; rfl)
  | query_bind t oa ih =>
    -- run-level: both sides' OptionT-binds expose as elimM over the lifted query
    have hrunL : ((liftM ((liftM (OracleSpec.query t) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _) >>= oa) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec (0 + 1)).Challenge]ₒ)) _)).run
        = (((liftM ((liftM (OracleSpec.query t) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _)) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
              [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
                ProtocolSpec (0 + 1)).Challenge]ₒ)) _)).run >>= fun o =>
            o.elim (pure none) fun a => ((liftM ((show OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
                ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut) from oa a)) :
              OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
                [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
                  ProtocolSpec (0 + 1)).Challenge]ₒ))
              ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut))).run) := by
      first
      | rfl
      | with_unfolding_all rfl
    refine Eq.trans (congrArg (simulateQ (impl.addLift challengeQueryImpl)) hrunL) ?_
    refine Eq.trans ?_ (congrArg (simulateQ impl) (show (OptionT.run ((liftM (OracleSpec.query t) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _) >>= oa))
        = ((liftM (OracleSpec.query t) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _)).run >>=
          fun o => o.elim (pure none) fun a =>
            ((show OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
              ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut) from oa a)).run
      from rfl)).symm
    simp only [simulateQ_bind]
    refine Eq.trans (congrArg₂ (· >>= ·)
      (show (simulateQ (impl.addLift challengeQueryImpl)
          ((liftM ((liftM (OracleSpec.query t) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _)) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
        [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
          ProtocolSpec (0 + 1)).Challenge]ₒ)) _)).run)
        = simulateQ impl ((liftM (OracleSpec.query t) :
            OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)) _)).run
        from by
          rcases t with t₁ | t₂
          · first | rfl | with_unfolding_all rfl
          · rcases t₂ with s | (c | c) <;> first | rfl | with_unfolding_all rfl) rfl) ?_
    apply bind_congr; intro o
    rcases o with _ | a
    · first | rfl | with_unfolding_all rfl | (dsimp only []; rfl)
    · first
      | exact ih a
      | (dsimp only []; exact ih a)



end Reduction

#print axioms Reduction.duplexSpongeFiatShamir_run_eq_honestExecution_holds
#print axioms Reduction.duplexSpongeFiatShamir_runCollapseResidual_holds
