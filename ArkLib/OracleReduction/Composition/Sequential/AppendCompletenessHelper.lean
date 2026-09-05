import ArkLib.OracleReduction.Composition.Sequential.AppendRun
import ArkLib.OracleReduction.Completeness

/-! Reconstruction helper for append-completeness (#113): component prover+verifier supports
compose into a `Reduction.run` support point. The reusable core of the append-completeness
keystone (used twice after `Verifier.append_run` splits the seam). -/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
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
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · show some (tr, prv) ∈ support (some <$> R.prover.run stmt wit)
    simp only [support_map, Set.mem_image, Option.some.injEq]; exact ⟨_, hP, rfl⟩
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some (some vout), ?_, ?_⟩
    · rw [OptionT.run_liftM_run, support_map,
        support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)]
      simp only [Set.mem_image, Option.some.injEq]
      exact ⟨some vout, hV, rfl⟩
    · simp only [Option.elim_some, Option.getM_some, OptionT.run_pure, OptionT.run_bind,
        pure_bind, support_pure, Set.mem_singleton_iff]

end Reduction
