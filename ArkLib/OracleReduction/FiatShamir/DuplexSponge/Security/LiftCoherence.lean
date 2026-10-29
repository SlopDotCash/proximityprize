/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness
import ArkLib.ToVCVio.Simulation
open OracleComp OracleSpec ProtocolSpec
/-!
# DSFS OptionT lift-coherence bridges

The proven coherence layer for the duplex-sponge Fiat-Shamir run-unrolling (the
`duplexSpongeFiatShamir{,Salted}_runCollapseResidual` campaign): run-characterizations of the
composite `OptionT` lifts (pure `rfl` once the instance paths are spelled), the per-query
annotated-vs-direct bridges (the right-side one crosses the instance diamond through
`duplexSpongeChallengeOracle`'s internal domain sum by case analysis), and the central
`dsfs_hLHS`: the associativity-routed two-step lift equals the direct lift on every
computation. The decisive lesson (see `docs/wiki/optiont-lift-coherence-walls.md`): the
mid-spec of the annotated path is the assoc-NESTED sum `oSpec + (dsCh + [Chal]ₒ)` — with the
annotation spelled correctly, the induction's query case is a one-line `simp`.
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
      _ ((liftM ((OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U) (Sum.inr t₂) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _))) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _))
    = (liftM (liftM ((OracleSpec.query (spec := oSpec + duplexSpongeChallengeOracle StmtIn U) (Sum.inr t₂) :
        OracleQuery (oSpec + duplexSpongeChallengeOracle StmtIn U) _)) :
        OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) _) :
        OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U +
          [(⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ :
            ProtocolSpec 1).Challenge]ₒ)) _) := by
  rcases t₂ with _ | (_ | _) <;> with_unfolding_all rfl

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


end Reduction

-- Axiom audits: all must be sorry-free.
#print axioms Reduction.dsfs_hLHS
#print axioms Reduction.dsfs_lift_query_bridge_inr
#print axioms Reduction.dsfs_lift_query_bridge_inl
#print axioms Reduction.dsfs_lift_query_bridge_inl₂
#print axioms Reduction.dsfs_hLHS₂
