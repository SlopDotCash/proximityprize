import ArkLib.ProofSystem.BCS.TransparentEndToEnd
import ArkLib.ProofSystem.BCS.ErrorAccounting
import ArkLib.OracleReduction.BCS.AppendSoundnessMsg
import ArkLib.OracleReduction.BCS.CompletenessPreservation
import ArkLib.Commitments.Functional.Transparent

-- Front D audit (#62): axiom-cleanliness of every headline BCS theorem.

-- End-to-end headline (a): perfect completeness of the compiled transparent BCS protocol.
#print axioms BCSTransparentEndToEnd.transparentBCS_perfectCompleteness
-- End-to-end headline (b): soundness of the compiled transparent BCS protocol.
#print axioms BCSTransparentEndToEnd.transparentBCS_soundness
-- Per-phase content.
#print axioms BCSTransparentEndToEnd.openingRed_perfectCompleteness
#print axioms BCSTransparentEndToEnd.openingRed_soundness
#print axioms BCSTransparentEndToEnd.interactionRed_perfectCompleteness
#print axioms BCSTransparentEndToEnd.interactionRed_soundness
-- Compiler-level keystones.
#print axioms OracleReduction.BCSTransform_perfectCompleteness
#print axioms OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg
#print axioms Verifier.append_soundness_msg'
#print axioms Verifier.append_soundness_msg_residual
