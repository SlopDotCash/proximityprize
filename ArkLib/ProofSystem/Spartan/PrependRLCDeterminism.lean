/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeFailingDet

/-!
# `hV₆`: the honest RLC-target adapter's verifier compiles purely (issue #114)

The pure-determinism witness for the `prependRLCTarget ▷ …` seam of the composed rbr-KS fold:
the 0-round adapter's compiled verifier is a `pure` function of the input statement/oracles —
`toVerifier_eq_pure_of_collapse` on the proven `simulateQ_prependRLCTargetVerifier` collapse.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [SampleableType R] in
/-- **`hV₆` witness: the honest RLC-target adapter's compiled verifier is pure.** -/
theorem prependRLCTarget_toVerifier_pure :
    (prependRLCTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p _tr => pure ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2)⟩ := by
  have h := OracleVerifier.toVerifier_eq_pure_of_collapse
    (prependRLCTarget (R := R) pp oSpec).verifier
    (fun p _tr => (∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1))
    (fun stmt oStmt tr => by
      exact_mod_cast simulateQ_prependRLCTargetVerifier (R := R) pp oSpec stmt oStmt
        tr.messages tr.challenges)
  rw [h]
  congr 1

/-- The witness in `IsFailingDet` form (for fold slots taking the existential shape). -/
theorem prependRLCTarget_toVerifier_isFailingDet :
    (prependRLCTarget (R := R) pp oSpec).verifier.toVerifier.IsFailingDet :=
  Verifier.IsFailingDet.of_pure _ (prependRLCTarget_toVerifier_pure pp oSpec)

end Spartan.Spec.Bricks

#print axioms Spartan.Spec.Bricks.prependRLCTarget_toVerifier_pure
#print axioms Spartan.Spec.Bricks.prependRLCTarget_toVerifier_isFailingDet
