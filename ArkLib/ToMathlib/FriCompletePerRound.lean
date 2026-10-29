/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriComplete
import ArkLib.ProofSystem.Whir.FoldRound
import ArkLib.ProofSystem.Fri.Spec.HonestFolding

/-!
# FRI: per-round perfect completeness — discharging the Brick A/B residuals (issue #117)

This module **discharges** the named per-round FRI perfect-completeness residuals from
`ArkLib.ToMathlib.FriComplete`:

* `foldRoundPerfectCompletenessResidual_holds` : the honest non-final folding round
  `FoldPhase.foldOracleReduction` is perfectly complete w.r.t. the FRI per-round
  input/output relations, given `hInit : NeverFail init`.

The proof uses the canonical `FoldPhase.foldProver_run` and native
`Reduction.run_run_eq_bind` factorization. Every reachable verifier result is `some`, and its
materialized output oracle is exactly the honest folded polynomial evaluation. That evaluation
has zero distance from the output witness, which proves the current canonical output relation.
The completed historical public theorem and its initialization hypothesis are retained.

-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ### Reed–Solomon membership and distance helpers -/

/-- The evaluation of a `CompPoly` polynomial of (computable) degree `< D` on any embedded domain
is a Reed–Solomon codeword of degree bound `D`. -/
lemma eval_mem_code {ι : Type} [Fintype ι] {D : ℕ} (dom : ι ↪ F)
    (p : CompPoly.CPolynomial F) (hp : p ∈ CompPoly.CPolynomial.degreeLT (R := F) D) :
    (fun idx => p.eval (dom idx)) ∈ (_root_.ReedSolomon.code dom D : Set (ι → F)) := by
  refine Submodule.mem_map.mpr ⟨p.toPoly, CompPoly.CPolynomial.degreeLT_toPoly.mp hp, ?_⟩
  funext idx
  exact (CompPoly.CPolynomial.eval_toPoly (dom idx) p).symm

/-- A vector in the code has relative distance `0 ≤ δ` from it (power-of-two index version,
as used by the FRI evaluation domains). -/
lemma relDistFromCode_le_of_mem {m : ℕ} {f : Fin (2 ^ m) → F}
    {C : Set (Fin (2 ^ m) → F)} (hf : f ∈ C) (δ : ℝ≥0) :
    δᵣ(f, C) ≤ (δ : ENNReal) := by
  haveI : Nonempty (Fin (2 ^ m)) := Fin.pos_iff_nonempty.mp (Nat.two_pow_pos _)
  refine le_trans (Code.relDistFromCode_le_relDist_to_mem f f hf) ?_
  refine le_trans (le_of_eq ?_) (by positivity)
  rw [Code.relHammingDist, hammingDist_self]
  simp only [Nat.cast_zero, zero_div]
  rw [← ENNReal.coe_nnratCast]
  simp only [NNRat.cast_zero, ENNReal.coe_zero]

/-! ### Brick A/B — non-final folding round: residual discharged -/

set_option maxHeartbeats 4000000 in
/-- **Brick A/B — non-final folding round perfect completeness (residual DISCHARGED).** -/
theorem foldRoundPerfectCompletenessResidual_holds
    (hInit : NeverFail init) (i : Fin k)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) :
    foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i cond δ := by
  unfold foldRoundPerfectCompletenessResidual OracleReduction.perfectCompleteness
  apply Reduction.perfectCompleteness_of_run_support init impl
  rintro ⟨c, o⟩ p hIn value hvalue
  rw [Reduction.run_run_eq_bind] at hvalue
  change value ∈ support (do
    let pr ← (FoldPhase.foldProver s d i).run (c, o) p
    let out ← liftComp ((FoldPhase.foldVerifier s (ω := ω) i).toVerifier.run
      (c, o) pr.1).run _
    pure (out.map (fun v => (pr, v)))) at hvalue
  rw [FoldPhase.foldProver_run] at hvalue
  simp only [bind_assoc, pure_bind] at hvalue
  obtain ⟨a, _, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  let p' : Witness F s d i.succ.castSucc :=
    ⟨CompPoly.CPolynomial.FoldingPolynomial.cpolyFold p.val (2 ^ (s i.castSucc).val) a,
      witness_lift (i := i.castSucc) p.property⟩
  have hverify : (FoldPhase.foldVerifier s (ω := ω) i).toVerifier.run (c, o)
      (FullTranscript.mk2 a (fun x => p'.val.eval x.val)) =
      pure (Fin.append c (fun _ : Fin 1 => a), FoldPhase.appendFoldOracle s i o p'.val) := by
    apply OptionT.ext
    change Option.map _ <$> simulateQ _ (pure _) = _
    simp only [simulateQ_pure, _root_.map_pure, Option.map_some]
    congr 3
    · rw [Fin.vappend_eq_append]
    · funext j
      apply eq_of_heq
      dsimp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
        FoldPhase.foldVerifier, DFunLike.coe]
      split <;> rename_i j' he
      · have hj : j'.val = j.val := by
          split_ifs at he with h
          exact congrArg Fin.val (Sum.inl.inj he).symm
        have hlt : j.val < i.val + 1 := by
          have hjlt := j'.isLt
          simpa only [Fin.val_castSucc, hj] using hjlt
        simp only [FoldPhase.appendFoldOracle, dite_eq_left hlt, eqRec_heq_iff]
        exact congr_arg_heq o (Fin.ext hj)
      · have hj : j.val = i.val + 1 := by
          split_ifs at he with h
          exact h
        have hj' : j' = ⟨1, by simp⟩ := by
          simpa only [dite_eq_left hj, Sum.inr.injEq] using he.symm
        subst j'
        have hjlast : j = Fin.last (i.val + 1) := Fin.ext hj
        subst j
        simp only [FoldPhase.appendFoldOracle, hj, lt_self_iff_false, ↓reduceDIte,
          eqRec_heq_iff, FullTranscript.mk2, FullTranscript.messages]
        rfl
  change value ∈ support (do
    let out ← liftComp ((FoldPhase.foldVerifier s (ω := ω) i).toVerifier.run (c, o)
      (FullTranscript.mk2 a (fun x => p'.val.eval x.val))).run _
    pure (out.map (fun v =>
      ((FullTranscript.mk2 a (fun x => p'.val.eval x.val),
        (Fin.append c (fun _ : Fin 1 => a), FoldPhase.appendFoldOracle s i o p'.val), p'), v)))) at hvalue
  rw [hverify] at hvalue
  simp only [OptionT.run_pure, liftComp_pure, pure_bind, Option.map_some] at hvalue
  have hv := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  refine ⟨_, rfl, ?_, rfl⟩
  change Code.relHammingDist (FoldPhase.appendFoldOracle s i o p'.val (Fin.last (i.val + 1)))
    (fun x => p'.val.eval x.val) ≤ δ
  rw [FoldPhase.appendFoldOracle_last]
  simp only [Code.relHammingDist, hammingDist_self, Nat.cast_zero, zero_div]
  simpa only [NNRat.cast_zero] using (show (0 : ℝ≥0) ≤ δ from zero_le)

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Fri.Spec.Completeness.foldRoundPerfectCompletenessResidual_holds
