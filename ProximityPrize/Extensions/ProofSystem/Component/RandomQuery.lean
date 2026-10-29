/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Component.RandomQuery

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ProximityPrize.Extensions.OracleReduction.LiftContext.OracleReduction
import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append

/-!
# Simple Oracle Reduction: Random Query

This describes a one-round oracle reduction to randomly test whether two oracles (of the same type,
with same oracle interface) are equal.

In more details: there is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
of the same type. The relation is `a = b`.
   - The verifier samples random `q : OracleInterface.Query` for that type and sends it to the
     prover.
   - The verifier does not do any checks.
   - The output relation is that `a` and `b` are equal at that query.
   - We also support a variant where it's `a.query q = r` where `r` is the response, discarding `b`.
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec
open scoped NNReal

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [O : OracleInterface OStatement]
  [inst : SampleableType (Query OStatement)]

namespace RandomQuery

local instance : MeasurableSpace (FullTranscript (pSpec OStatement)) := ⊤

instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
  | ⟨0, _⟩ => inst

instance : VerifierOnly (pSpec OStatement) where
  verifier_first' := by simp

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun
the honest transcript distribution using the public oracle input and the unique `Unit` witness. -/
def transcriptSimulator :
    @OracleReduction.TranscriptSimulator ι oSpec Unit (Fin 2) (OStmtIn OStatement) 1
      (pSpec OStatement) :=
  fun stmtIn =>
    Reduction.honestTranscriptDist init impl
      (oracleReduction oSpec OStatement).toReduction stmtIn ()

/-- The honest transcript distribution for `RandomQuery` is definitionally the simulator
distribution. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmtIn : StmtIn × (∀ i, OStmtIn OStatement i)) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReduction oSpec OStatement).toReduction stmtIn ()) =
      evalDist (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl) stmtIn) := rfl

/-- `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the
single verifier challenge is sampled by the same honest challenge implementation in the simulator. -/
theorem oracleReduction_perfectHVZK :
    OracleReduction.perfectHVZK init impl (relIn OStatement)
      (oracleReduction oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) := by
  intro stmtIn () _
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (OStatement := OStatement) (init := init) (impl := impl) stmtIn).symm

/-- Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget. -/
theorem oracleReduction_statisticalHVZK (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl (relIn OStatement)
      (oracleReduction oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) ε :=
  (oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).statisticalHVZK ε

/-- `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction. -/
theorem oracleReduction_isHVZK :
    OracleReduction.isHVZK init impl (relIn OStatement) (oracleReduction oSpec OStatement) :=
  ⟨transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl),
    oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl)⟩

/-- `RandomQuery` has statistical HVZK at every error budget as an oracle reduction. -/
theorem oracleReduction_isStatHVZK (ε : NNReal) :
    OracleReduction.isStatHVZK init impl (relIn OStatement)
      (oracleReduction oSpec OStatement) ε :=
  (oracleReduction_isHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).isStatHVZK ε

#print axioms RandomQuery.transcriptSimulator
#print axioms RandomQuery.honestTranscriptDist_oracleReduction_evalDist
#print axioms RandomQuery.oracleReduction_perfectHVZK
#print axioms RandomQuery.oracleReduction_statisticalHVZK
#print axioms RandomQuery.oracleReduction_isHVZK
#print axioms RandomQuery.oracleReduction_isStatHVZK

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   answer (oracles 0) q = answer (oracles 1) q

variable [Fintype (Query OStatement)] [∀ q, DecidableEq (O.toOC.spec q)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

end RandomQuery

-- namespace RandomQueryAndReduceClaim

-- /-!
--   Random query where we throw away the second oracle, and replace with the response:
--   - The input relation is `{ ⟨⟨_, 𝒪⟩, _⟩ | 𝒪 0 = 𝒪 1 }`.
--   - The output relation is `{ ⟨⟨q, r⟩, 𝒪⟩, _⟩ | oracle (𝒪 0) q = r }`.
--   - The (oracle) verifier sends a single random query `q` to the prover, queries the oracle
--     `𝒪 1` at
--     `q` to get response `r`, returns `(q, r)` as the output statement, and drop `𝒪 1` from the
--     output oracle statement.

--   This is just the concatenation of `RandomQuery` and `ReduceClaim`.
-- -/

-- @[reducible, simp] def StmtIn := Unit
-- @[reducible, simp] def StmtOut := Query OStatement × Response OStatement

-- @[reducible, simp] def OStmtIn := fun _ : Fin 2 => OStatement
-- @[reducible, simp] def OStmtOut := fun _ : Fin 1 => OStatement

-- @[reducible, simp] def WitIn := Unit
-- @[reducible, simp] def WitOut := Unit

-- @[reducible, simp]
-- def relIn : (StmtIn × ∀ i, OStmtIn OStatement i) → WitIn → Prop := fun ⟨(), oracles⟩ () =>
--   oracles 0 = oracles 1

-- /--
-- The final relation states that the first oracle `oStmt ()` agrees with the response `r` at the
-- query `q`.
-- -/
-- @[reducible, simp]
-- def relOut : (StmtOut OStatement × ∀ i, OStmtOut OStatement i) → WitOut → Prop :=
--   fun ⟨⟨q, r⟩, oStmt⟩ () => answer (oStmt 0) q = r

-- -- @[reducible]
-- -- def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

-- -- instance : ∀ i, OracleInterface ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
-- -- @[reducible, simp] instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
-- --   | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

-- -- instance : OracleContext.Lens
-- --     RandomQuery.StmtIn (RandomQuery.StmtOut OStatement)
-- --     StmtIn (StmtOut OStatement)
-- --     (RandomQuery.OStmtIn OStatement) (RandomQuery.OStmtOut OStatement)
-- --     (OStmtIn OStatement) (OStmtOut OStatement)
-- --     RandomQuery.WitIn RandomQuery.WitOut
-- --     WitIn WitOut where
-- --   projStmt := fun () => ()
-- --   liftStmt := fun () => ()
-- --   projOStmt := fun i => fun () => ()
-- --   simOStmt := fun i => fun () => ()
-- --   liftOStmt := fun i => fun () => ()
-- --   projWit := fun () => ()
-- --   liftWit := fun () => ()

-- end RandomQueryAndReduceClaim
