/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VectorChain
import ArkLib.OracleReduction.DecisionTail

/-!
# The packaged STIR chain proof object (#301)
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The packaged STIR chain proof object** over the compound vector-wire spec: the full
vectorised chain with a decision tail. The decision is the always-accept placeholder at this
stage (mirroring the WHIR `Protocol.lean` staging); upgrading it to the genuine final checks
(consistency of the in-the-clear final word with the folded chain at sampled points) is the
checked-verifier step, exactly as WHIR's `CheckedVerifier.lean` did for `whirVerify`. -/
noncomputable def stirChainProof (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleProof []ₒ Unit (OStmt ι F) Unit
      ((stirInitVSpec.toProtocolSpec F) ++ₚ
        (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
          ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
            ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))) :=
  (stirFullVectorReduction φ deg M).toProof (fun _ => true)

end Round3

end StirIOP


#print axioms StirIOP.Round3.stirChainProof
