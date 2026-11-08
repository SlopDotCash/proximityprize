/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Extensions.OracleReduction.LiftContext.Reduction
import ArkLib.OracleReduction.LiftContext.OracleReduction
import Batteries.Tactic.OpenPrivate

open private OracleVerifier.simulateQueryAlongHEq from ArkLib.OracleReduction.Basic

/-!
# Oracle-statement-preserving context lifting

The statement-only lift retains the canonical output representation, whether embedded or virtual.
Output reselection routes selected queries through the canonical simulation and materializes the
same selected values. It requires agreement of the output oracle interfaces along the supplied
type equalities; this structural coherence was implicit in the retired embedding-only model.
-/

open OracleSpec OracleComp ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

/-- The oracle-statement-preserving lift of an oracle verifier: transform only
the non-oracle statement (via a `Statement.Lens`), keeping the oracle statements
fixed. The output-oracle embedding and type-equalities are inherited unchanged
from the inner verifier. Fully implementable, in contrast to the fully general
`OracleVerifier.liftContext`. -/
def liftContextStmt
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec) :
    OracleVerifier oSpec OuterStmtIn OStmtIn OuterStmtOut OStmtOut pSpec where
  verify := fun outerStmtIn challenges =>
    (fun innerStmtOut => lens.lift outerStmtIn innerStmtOut) <$>
      V.verify (lens.proj outerStmtIn) challenges
  outputOracle := V.outputOracle

@[simp]
lemma liftContextStmt_outputOracle
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec) :
    (V.liftContextStmt lens).outputOracle = V.outputOracle := rfl

@[simp]
lemma liftContextStmt_verify
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut OStmtOut pSpec)
    (outerStmtIn : OuterStmtIn) (challenges : pSpec.Challenges) :
    (V.liftContextStmt lens).verify outerStmtIn challenges
      = (fun s => lens.lift outerStmtIn s) <$> V.verify (lens.proj outerStmtIn) challenges :=
  rfl

-- (An auxiliary / commutation lemma holds but
-- requires the OptionT/simulateQ map-distribution machinery; omitted here as
-- the security properties are inherited via the existing
-- ported lemmas in .)

end OracleVerifier

namespace OracleVerifier

variable {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
  [∀ i, OracleInterface (InnerOStmtOut i)]

/-- The output-oracle-reselecting lift of an oracle verifier: in addition to a
non-oracle statement lens, the outer output oracle statements are a reindexing
(`oₒ`, injective) of the inner ones, with matching types (`hOO`). The input
oracle statements are shared. This strictly generalises `liftContextStmt`
(which is the `oₒ = id` case) and covers the realistic protocol-composition
scenario where a lift never adds input oracles but may drop/reselect outputs.
Fully implementable: `embed` composes `oₒ` with the inner embedding, `hEq`
chains the type equalities. -/
def liftContextReselect
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ)
    (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (hInterface : ∀ i, HEq (inferInstance : OracleInterface (OStmtOut i))
      (inferInstance : OracleInterface (InnerOStmtOut (oₒ i))))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec) :
    OracleVerifier oSpec OuterStmtIn OStmtIn OuterStmtOut OStmtOut pSpec where
  verify := fun outerStmtIn challenges =>
    (fun innerStmtOut => lens.lift outerStmtIn innerStmtOut) <$>
      V.verify (lens.proj outerStmtIn) challenges
  outputOracle := .inr {
    materializeOutput := fun challenges inputs messages i =>
      cast (hOO i).symm (V.materializeOutput challenges inputs messages (oₒ i))
    simulateOutputQuery := fun challenges q =>
      OracleVerifier.queryAlongHEq (inferInstance : OracleInterface (OStmtOut q.1))
        (inferInstance : OracleInterface (InnerOStmtOut (oₒ q.1))) (hOO q.1) (hInterface q.1)
        (fun query => V.simulateOutputQuery challenges ⟨oₒ q.1, query⟩) q.2
    simulateOutputQuery_eq := fun challenges inputs messages q => by
      apply OracleVerifier.simulateQueryAlongHEq
      · exact cast_heq _ _
      · intro query
        exact V.simulateOutputQuery_eq challenges inputs messages ⟨oₒ q.1, query⟩ }

@[simp]
lemma liftContextReselect_materializeOutput
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ) (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (hInterface : ∀ i, HEq (inferInstance : OracleInterface (OStmtOut i))
      (inferInstance : OracleInterface (InnerOStmtOut (oₒ i))))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (challenges : pSpec.Challenges) (inputs : ∀ i, OStmtIn i) (messages : pSpec.Messages)
    (i : ιₛₒ) :
    (V.liftContextReselect lens oₒ hOO hInterface).materializeOutput challenges inputs messages i =
      cast (hOO i).symm (V.materializeOutput challenges inputs messages (oₒ i)) := rfl

@[simp]
lemma liftContextReselect_verify
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (oₒ : ιₛₒ ↪ Inner_ιₛₒ) (hOO : ∀ i, OStmtOut i = InnerOStmtOut (oₒ i))
    (hInterface : ∀ i, HEq (inferInstance : OracleInterface (OStmtOut i))
      (inferInstance : OracleInterface (InnerOStmtOut (oₒ i))))
    (V : OracleVerifier oSpec InnerStmtIn OStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (outerStmtIn : OuterStmtIn) (challenges : pSpec.Challenges) :
    (V.liftContextReselect lens oₒ hOO hInterface).verify outerStmtIn challenges
      = (fun s => lens.lift outerStmtIn s) <$> V.verify (lens.proj outerStmtIn) challenges :=
  rfl

end OracleVerifier

namespace ProximityPrize.Compatibility

variable {StmtIn StmtOut : Type} {ιIn ιOut : Type}
  {OIn : ιIn → Type} {OOut : ιOut → Type}
  [∀ i, OracleInterface (OIn i)] [∀ i, OracleInterface (OOut i)]

/-- Identity statement/oracle transport in the canonical native lens interface. -/
def identityExecutableLens : OracleStatement.ExecutableLens
    StmtIn StmtOut StmtIn StmtOut OIn OOut OIn OOut where
  projStmt := id
  materializeInput := fun _ => id
  simulateInput := fun _ q => OracleSpec.query (spec := [OIn]ₒ) q
  simulateInput_eq := by intro _ _ _; rfl
  liftStmt := fun _ => id
  materializeOutput := fun _ => id
  simulateOutput := fun q => OracleSpec.query (spec := [OIn]ₒ + [OOut]ₒ) (.inr q)
  simulateOutput_eq := by intro _ _ _; rfl

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)]

/-- Identity lifting preserves either native output representation, including virtual outputs. -/
def identityLiftContextOutput
    (V : OracleVerifier oSpec StmtIn OIn StmtOut OOut pSpec) :
    OracleVerifier.LiftContextOutput identityExecutableLens V where
  outputOracle := V.outputOracle
  materialize_eq := by intro _ _ _ _; rfl

end ProximityPrize.Compatibility
