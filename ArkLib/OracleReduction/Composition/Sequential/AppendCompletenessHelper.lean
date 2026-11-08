import ArkLib.OracleReduction.Composition.Sequential.AppendRun
import ArkLib.OracleReduction.Completeness

/-! Reconstruction helper for append-completeness (#113): component prover+verifier supports
compose into a `Reduction.run` support point. The reusable core of the append-completeness
keystone (used twice after `Verifier.append_run` splits the seam). -/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- A `Reduction.run` outcome is in the support whenever its prover-transcript piece is in the
prover's support and its verifier output is in the verifier's support on that transcript. -/
theorem mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : FullTranscript pSpec) (prv : StmtOut × WitOut) (vout : StmtOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : some vout ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    some ((tr, prv), vout) ∈ support (OptionT.run (R.run stmt wit)) := by
  rw [Reduction.run_run_eq_bind, mem_support_bind_iff]
  refine ⟨(tr, prv), hP, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨some vout, ?_, ?_⟩
  · simpa only [OracleComp.support_liftComp] using hV
  · simp only [Option.map_some, support_pure, Set.mem_singleton_iff]


end Reduction

#print axioms Reduction.mem_support_run_of_prover_verifier
