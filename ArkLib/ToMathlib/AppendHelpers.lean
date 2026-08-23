/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Execution

/-!
# Support Preservation under Oracle Reduction and Context Lifting

This module establishes the core algebraic and support-level transport lemmas required for
the sequential composition and context lifting of oracle reductions, specifically supporting
`OracleReduction/Composition/Sequential/Append.lean` and
`OracleReduction/LiftContext/Reduction.lean`.

By isolating the support-transport reasoning from the larger security reductions, we maintain
modularity and avoid re-deriving the invariance of monadic supports under spec extensions.
-/

open OracleSpec OracleComp ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι}

namespace OracleComp

-- `support_liftComp` is now provided upstream by VCVio (`OracleComp.support_liftComp`).

end OracleComp

namespace Reduction

variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Verifier reachability under reduction runs.
Let `reduction` be a reduction protocol. For any statement-witness pair in the support of the
full reduction execution `reduction.run stmt wit`, the verifier's final output statement is a
reachable outcome of the verifier's execution when run on the statement and the transcript.

This provides the transcript witness for `Verifier.compatStatement`: the witness transcript is
the `proverResult.1` component of the run result. The verifier sub-computation is lifted as
`liftM (verifier.run stmt td).run`; because `OracleComp.liftComp` preserves supports, the
reachability
relation transports back to the un-lifted execution. -/
theorem verifier_output_mem_run_support
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {stmt : StmtIn} {wit : WitIn}
    {x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut}
    (hx : some x ∈ support (reduction.run stmt wit).run) :
    x.2 ∈ support (reduction.verifier.run stmt x.1.1) := by
  rw [Reduction.run] at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨proverResultOpt, _hprover, hx⟩ := hx
  cases proverResultOpt with
  | none => simp at hx
  | some proverResult =>
      simp only [Option.elim_some, OptionT.run_bind, Option.elimM] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨stmtOutOpt, hstmtOut, hx⟩ := hx
      -- `stmtOutOpt` is of type `Option (Option StmtOut)`, representing the outer monadic bind
      -- and the verifier's optional output. Both must be `some` for `x` to be reachable.
      cases stmtOutOpt with
      | none => simp at hx
      | some vOutOpt =>
          cases vOutOpt with
          | none => simp [Option.getM] at hx
          | some vOut =>
              simp only [Option.elim_some, Option.getM_some, OptionT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
              have hx2 : x.2 = vOut := congrArg Prod.snd hx
              have hx11 : x.1.1 = proverResult.1 := congrArg (Prod.fst ∘ Prod.fst) hx
              rw [hx2, hx11]
              -- Transport the reachability of `some vOut` from the lifted verifier run to the
              -- original.
              -- `hstmtOut` asserts `some (some vOut) ∈ support (liftM (V.run …).run).run`. Since
              -- the lift
              -- is `OptionT.lift ∘ liftComp`, we decompose the lift as `some <$> liftComp
              -- (V.run).run`.
              rw [OptionT.mem_support_iff]
              have hLift := hstmtOut
              have hrun : (liftM (reduction.verifier.run stmt proverResult.1).run :
                    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)).run
                  = some <$> OracleComp.liftComp (reduction.verifier.run stmt proverResult.1).run
                      (oSpec + [pSpec.Challenge]ₒ) := by
                rw [liftComp_eq_liftM]
                simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
                  OptionT.lift, OptionT.mk, OptionT.run, map_eq_pure_bind, simulateQ_bind,
                  simulateQ_pure, OracleComp.liftComp]
              rw [hrun, support_map, OracleComp.support_liftComp, Set.mem_image] at hLift
              obtain ⟨w, hw, hwEq⟩ := hLift
              rw [Option.some.injEq] at hwEq
              rwa [← hwEq]

end Reduction
