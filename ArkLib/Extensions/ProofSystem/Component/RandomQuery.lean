/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Component.RandomQuery
import ArkLib.OracleReduction.DecisionTail
import ArkLib.OracleReduction.Security.OracleZeroKnowledge

/-!
# Historical two-oracle view of RandomQuery

The canonical reduction carries a public statement through the random query. Historical
virtual-polynomial lenses project the statement to `Unit`, compare the two virtual input
oracles, and expect just the query as the output statement. Specialize the canonical prover
and verifier to those inputs and project away the carried `Unit`.

The verifier samples and sends the query. The output relation requires the oracle
answers to agree at that query. `RandomQueryAndReduceClaim` remains a commented sketch.
-/

open OracleSpec OracleComp OracleInterface ProtocolSpec
open scoped NNReal

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [O : OracleInterface OStatement]

namespace RandomQuery.Historical

abbrev StmtIn := Unit
abbrev StmtOut := Query OStatement

abbrev OStmtIn : Fin 2 → Type := fun _ => OStatement
abbrev OStmtOut := OStmtIn OStatement

abbrev WitIn := Unit
abbrev WitOut := Unit

/-- The two virtual oracle values are equal. -/
@[reducible, simp]
def relIn : Set ((StmtIn × (∀ i, OStmtIn OStatement i)) × WitIn) :=
  RandomQuery.relIn Unit (OStmtIn OStatement) OStatement
    (fun _ oracles => oracles 0) (fun _ oracles => oracles 1)

/-- The two virtual oracle values give the same answer at the query. -/
@[reducible, simp]
def relOut : Set ((StmtOut OStatement × (∀ i, OStmtOut OStatement i)) × WitOut) :=
  {p | (((p.1.1, ()), p.1.2), p.2) ∈
    RandomQuery.relOut Unit (OStmtIn OStatement) OStatement
      (fun _ oracles => oracles 0) (fun _ oracles => oracles 1)}

abbrev pSpec := RandomQuery.pSpec (Query OStatement)

/-- Repackage the canonical prover's output in the historical query-only statement type. -/
def oracleProver :
    OracleProver oSpec StmtIn (OStmtIn OStatement) WitIn
      (StmtOut OStatement) (OStmtOut OStatement) WitOut (pSpec OStatement) :=
  (RandomQuery.oracleProver oSpec Unit (OStmtIn OStatement) (Query OStatement)).mapOutput
    (fun output => (output.1.1, output.2)) id

instance : (oracleProver oSpec OStatement).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- Project the query from the canonical verifier's verdict, preserving its oracle routing. -/
def oracleVerifier :
    OracleVerifier oSpec StmtIn (OStmtIn OStatement)
      (StmtOut OStatement) (OStmtOut OStatement) (pSpec OStatement) :=
  let V := RandomQuery.oracleVerifier oSpec Unit (OStmtIn OStatement) (Query OStatement)
  { verify := fun stmt challenges => Prod.fst <$> V.verify stmt challenges
    outputOracle := V.outputOracle }

@[simp]
theorem oracleVerifier_verify (stmt : StmtIn) (challenges : (pSpec OStatement).Challenges) :
    (oracleVerifier oSpec OStatement).verify stmt challenges =
      pure (challenges ⟨0, rfl⟩) := rfl

@[simp]
theorem oracleVerifier_materializeOutput (challenges : (pSpec OStatement).Challenges)
    (oracles : ∀ i, OStmtIn OStatement i) (messages : (pSpec OStatement).Messages) :
    (oracleVerifier oSpec OStatement).materializeOutput challenges oracles messages = oracles :=
  RandomQuery.oracleVerifier_materializeOutput oSpec Unit (OStmtIn OStatement)
    (Query OStatement) challenges oracles messages

/-- The historical reduction forwards the sampled query and keeps both input oracles. -/
def oracleReduction :
    OracleReduction oSpec StmtIn (OStmtIn OStatement) WitIn
      (StmtOut OStatement) (OStmtOut OStatement) WitOut (pSpec OStatement) :=
  ⟨oracleProver oSpec OStatement, oracleVerifier oSpec OStatement⟩

instance [Fintype (Query OStatement)] : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  change Fintype (Query OStatement)
  infer_instance

end RandomQuery.Historical

namespace RandomQuery

variable [SampleableType (Query OStatement)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

private local instance : MeasurableSpace (FullTranscript (Historical.pSpec OStatement)) := ⊤

/-- The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun
the honest transcript distribution using the public oracle input and the unique `Unit` witness. -/
def transcriptSimulator :
    @OracleReduction.TranscriptSimulator ι oSpec Unit (Fin 2) (Historical.OStmtIn OStatement) 1
      (Historical.pSpec OStatement) :=
  fun stmtIn =>
    Reduction.honestTranscriptDist init impl
      (Historical.oracleReduction oSpec OStatement).toReduction stmtIn ()

/-- The honest transcript distribution for `RandomQuery` is definitionally the simulator
distribution. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmtIn : Historical.StmtIn × (∀ i, Historical.OStmtIn OStatement i)) :
    evalDist (Reduction.honestTranscriptDist init impl
        (Historical.oracleReduction oSpec OStatement).toReduction stmtIn ()) =
      evalDist (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl) stmtIn) := rfl

/-- `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the
single verifier challenge is sampled by the same honest challenge implementation in the simulator. -/
theorem oracleReduction_perfectHVZK :
    OracleReduction.perfectHVZK init impl (Historical.relIn OStatement)
      (Historical.oracleReduction oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) := by
  intro stmtIn () _
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (OStatement := OStatement) (init := init) (impl := impl) stmtIn).symm

/-- Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget. -/
theorem oracleReduction_statisticalHVZK (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl (Historical.relIn OStatement)
      (Historical.oracleReduction oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) ε :=
  (oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).statisticalHVZK ε

/-- `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction. -/
theorem oracleReduction_isHVZK :
    OracleReduction.isHVZK init impl (Historical.relIn OStatement)
      (Historical.oracleReduction oSpec OStatement) :=
  ⟨transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl),
    oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl)⟩

/-- `RandomQuery` has statistical HVZK at every error budget as an oracle reduction. -/
theorem oracleReduction_isStatHVZK (ε : NNReal) :
    OracleReduction.isStatHVZK init impl (Historical.relIn OStatement)
      (Historical.oracleReduction oSpec OStatement) ε :=
  (oracleReduction_isHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).isStatHVZK ε

#print axioms RandomQuery.transcriptSimulator
#print axioms RandomQuery.honestTranscriptDist_oracleReduction_evalDist
#print axioms RandomQuery.oracleReduction_perfectHVZK
#print axioms RandomQuery.oracleReduction_statisticalHVZK
#print axioms RandomQuery.oracleReduction_isHVZK
#print axioms RandomQuery.oracleReduction_isStatHVZK

end RandomQuery
