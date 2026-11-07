/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriCompletePerRound
import ArkLib.ProofSystem.Fri.Spec.HonestFinalFolding

/-!
# Final FRI fold perfect completeness

The retained `finalFoldRoundPerfectCompletenessResidual_holds` contract delegates execution to
canonical `finalFoldProver_run` and `toVerifier_run`. The folded witness satisfies the final degree
guard. The verifier materializes the polynomial actually transmitted by the prover, so the final
output relation is the relative distance of that polynomial from itself, bounded by every
nonnegative `δ`. The original source and native API migration are recorded in
`scripts/integration/fri-final-completeness-migration.json`.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

omit [Fintype F] [SampleableType F] in
/-- A `CPolynomial` in `degreeLT D` (for positive `D`) has `natDegree < D`. Bridges the FRI
final-round witness bound to the verifier's degree `guard`. -/
lemma natDegree_lt_of_mem_degreeLT {p : CompPoly.CPolynomial F} {D : ℕ} (hD : 0 < D)
    (hp : p ∈ CompPoly.CPolynomial.degreeLT (R := F) D) : p.natDegree < D := by
  rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT] at hp
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  rcases eq_or_ne p.toPoly 0 with h0 | h0
  · simpa [h0] using hD
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hp)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Brick A/B — final folding round perfect completeness (residual DISCHARGED).** -/
theorem finalFoldRoundPerfectCompletenessResidual_holds
    (hInit : NeverFail init)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) :
    finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit cond δ := by
  unfold finalFoldRoundPerfectCompletenessResidual OracleReduction.perfectCompleteness
  apply Reduction.perfectCompleteness_of_run_support init impl
  rintro ⟨c, o⟩ p hIn value hvalue
  rw [Reduction.run_run_eq_bind] at hvalue
  change value ∈ support (do
    let pr ← (FinalFoldPhase.finalFoldProver s d).run (c, o) p
    let out ← liftComp ((FinalFoldPhase.finalFoldVerifier s d).toVerifier.run
      (c, o) pr.1).run _
    pure (out.map (fun v => (pr, v)))) at hvalue
  rw [FinalFoldPhase.finalFoldProver_run] at hvalue
  simp only [bind_assoc, pure_bind] at hvalue
  obtain ⟨a, _, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  let p' : Witness F s d (Fin.last (k + 1)) :=
    ⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold p.val
      (2 ^ (s (Fin.last k)).val) a, witness_lift (i := Fin.last k) p.property⟩
  let tr : (FinalFoldPhase.pSpec F).FullTranscript := FullTranscript.mk2 a p'.val
  have hg : p'.val.natDegree < d.val := by
    simpa using witness_natDegree_lt s d _ p'
  have hverify := FinalFoldPhase.toVerifier_run s d c o tr
  have htr1 : tr 1 = p'.val := rfl
  have htr0 : tr 0 = a := rfl
  rw [htr1, htr0, ite_eq_left hg] at hverify
  change value ∈ support (do
    let out ← liftComp ((FinalFoldPhase.finalFoldVerifier s d).toVerifier.run
      (c, o) tr).run _
    pure (out.map (fun v =>
      ((tr, (Fin.append c (fun _ : Fin 1 => a),
        (FinalFoldPhase.finalFoldVerifier s d).materializeOutput tr.challenges o tr.messages), p'), v)))) at hvalue
  rw [hverify] at hvalue
  simp only [liftComp_pure, pure_bind, Option.map_some] at hvalue
  have heq := OracleComp.eq_of_mem_support_pure _ hvalue
  refine ⟨_, heq, ?_, rfl⟩
  simp only [FinalFoldPhase.outputRelation, Set.mem_ofPred_eq]
  rw [FinalFoldPhase.finalPolynomial_materialize]
  simp only [tr, FullTranscript.mk2, Code.relHammingDist, hammingDist_self,
    Nat.cast_zero, zero_div, NNRat.cast_zero]
  exact bot_le

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Fri.Spec.Completeness.finalFoldRoundPerfectCompletenessResidual_holds
