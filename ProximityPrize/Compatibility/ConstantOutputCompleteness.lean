/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Execution
import ArkLib.OracleReduction.Security.Basic

/-!
# Completeness of reductions with constant honest outputs

The native support proof is shared by always-accepting downstream protocol shells. It preserves
all prover queries and verifies that every reachable optional result is present and correct.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

/-- Constant, agreeing honest prover and verifier outputs give perfect completeness whenever
that output satisfies the output relation. No restriction is imposed on the prover's rounds. -/
theorem perfectCompleteness_of_constant_output
    {κ : Type} {spec : OracleSpec κ} {A B C D : Type} {n : ℕ} {p : ProtocolSpec n}
    [∀ i, SampleableType (p.Challenge i)]
    (R : Reduction spec A B C D p) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp)) (relIn : Set (A × B))
    (relOut : Set (C × D)) (c : C) (d : D)
    (houtput : ∀ state, R.prover.output state = pure (c, d))
    (hverify : ∀ stmt tr, R.verifier.run stmt tr = pure c)
    (hrel : (c, d) ∈ relOut) :
    R.perfectCompleteness init impl relIn relOut := by
  apply perfectCompleteness_of_run_support init impl
  intro stmt wit _ value hvalue
  rw [run_run_eq_bind] at hvalue
  simp only [Prover.run, LawfulApplicative.map_pure, houtput, liftM_pure, pure_bind, bind_pure_comp, bind_map_left, hverify,
    OptionT.run_pure, liftComp_pure, Option.map_some] at hvalue
  obtain ⟨ctx, hctx, hv⟩ := OracleComp.mem_support_map_peel _ _ hvalue
  obtain ⟨ctx₀, _, hctxEq⟩ := OracleComp.mem_support_map_peel _ _ hctx
  subst ctx
  subst value
  exact ⟨_, rfl, hrel, rfl⟩

end Reduction

#print axioms Reduction.perfectCompleteness_of_constant_output
