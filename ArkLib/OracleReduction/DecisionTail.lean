/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Basic

/-!
# The decision tail (#301)

General combinators turning an `OracleReduction` into an `OracleProof` (`Bool` output
statement, no output oracles) by post-composing a decision predicate on the output statement.
-/

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut StmtOut' WitOut' : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Map the output statement and witness of a prover. -/
def mapOutput (f : StmtOut → StmtOut') (g : WitOut → WitOut')
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prover oSpec StmtIn WitIn StmtOut' WitOut' pSpec where
  PrvState := P.PrvState
  input := P.input
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := fun st => do
    let ⟨s, w⟩ ← P.output st
    return ⟨f s, g w⟩

end Prover

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]

/-- **The decision tail**: turn an oracle reduction into an oracle proof by post-composing a
Boolean decision on the output statement; the output oracles and witness are discarded
(`Empty`-indexed output oracles, `Unit` witness). The prover and verifier apply the same
decision to their respective output statements, so output agreement is inherited. -/
def toProof (d : StmtOut → Bool)
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    OracleProof oSpec StmtIn OStmtIn WitIn pSpec where
  prover := Prover.mapOutput
    (fun s : StmtOut × ∀ i, OStmtOut i =>
      ((d s.1, fun e : Empty => nomatch e) : Bool × ∀ _ : Empty, Unit))
    (fun _ => ()) R.prover
  verifier :=
    { verify := fun stmt chals => do
        let s ← R.verifier.verify stmt chals
        return d s
      embed := ⟨Empty.elim, fun e => e.elim⟩
      hEq := fun e => e.elim }

end OracleReduction


#print axioms Prover.mapOutput
#print axioms OracleReduction.toProof
