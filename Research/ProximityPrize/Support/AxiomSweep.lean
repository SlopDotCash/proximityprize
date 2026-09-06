-- Flagship axiom sweep — every declaration must show only [propext, Classical.choice, Quot.sound]
import Research.ProximityPrize.Lattice2
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.ToMathlib.CS25JointFar
import ArkLib.ToMathlib.L13Milestone
import ArkLib.ToMathlib.L46DiffStackRS
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToMathlib.KoalaBearCode
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.ToMathlib.ToyStep4
import ArkLib.ToMathlib.SubspacePolyLinearized
import Research.ProximityPrize.Hab25Core

-- Grand Challenge lattice encodings
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec
#print axioms ProximityGap.GrandChallengesLattice.listThreshold_spec
-- GK16 T2.18-FRS (full external-paper port)
#print axioms CodingTheory.frs_is_subspaceDesign_gk16
-- CS25 Thm 2 / ABF26 T5.3 (full external-paper port)
#print axioms CodingTheory.CS25.DeepHole.rs_epsCA_implies_lambda_extended_cs25_complete
-- L13 keystone milestone (BCIKS20 §5, residual-free β)
#print axioms ArkLib.L13Milestone.correlatedAgreement_affine_curves_strongBeta_of_betaRecFin
-- ABF26 L4.6 for Reed–Solomon
#print axioms ProximityGap.L46GS.epsMCA_eq_epsCA_below_udr_rs
-- L4.6 unconditional sharp form
#print axioms ProximityGap.epsMCA_le_max_epsCA_card_div_udr
-- L6.12 list-decoding soundness lower bound
#print axioms ToyProblem.simplified_iop_soundness_listDecoding_lb
-- BKR06 linearized-support chain
#print axioms BKR06.subspacePoly_isQLinearized
