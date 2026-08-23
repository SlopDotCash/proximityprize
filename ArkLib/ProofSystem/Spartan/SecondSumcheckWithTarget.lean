/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.MidChainWithTarget
import ArkLib.ProofSystem.Spartan.SecondSumcheckFaithful

/-!
# Target-preserving second sum-check lift, over the carried statement (issue #329, X-lane)

The carried analogue of `SecondSumcheckReduction`/`FirstSumcheckWithTarget` for the second
sum-check: the input statement is `(T, (r, (e₁, (r_x, τ, 𝕩))))` — the prepended RLC target over
the `e₁`-carrying `Statement.AfterLinearCombinationWithTarget` — and the output **keeps** the
inner terminal target `e₂`: `((e₂, r_y), (r, (e₁, (r_x, τ, 𝕩))))`.

Everything reuses the plain second sum-check development through the `e₁`-dropping projection
`dropFirstTarget`: the virtual polynomial, the oracle reconstruction
(`secondSumcheckEvalFromOracles`), and its faithfulness (`secondSumcheckEvalFromOracles_simOracle2`)
are consumed as-is — the carried `e₁` is a pure passenger for this phase.

Provides, mirroring `FirstSumcheckWithTarget`:
* the lenses and the lifted reduction `secondSumcheckReductionWithTarget`;
* `AppendCoherent` + `LiftContextCoherent`;
* the rbr-KS relations (`secondSumcheckWithTargetRbrRelIn`/`RelOut`), the target-pinning
  collapse, and the KS transfer at per-round error `2/|R|`
  (`secondSumcheckWithTarget_rbrKnowledgeSoundness_honest_full`).
-/

open OracleComp OracleSpec ProtocolSpec Function MvPolynomial OracleVerifier.LiftContext
open scoped NNReal

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The Spartan statement after the carried second sum-check, **with the terminal target kept**:
`((e₂, r_y), (r, (e₁, (r_x, τ, 𝕩))))`. -/
@[simp]
abbrev Statement.AfterSecondSumcheckWithTarget : Type :=
  (R × SecondSumcheckChallenge R pp) × Statement.AfterLinearCombinationWithTarget R pp

variable {R}

/-- Drop the carried first-terminal slot: project the `e₁`-carrying post-RLC statement back to
the plain `Statement.AfterLinearCombination`, for reuse of the plain second sum-check algebra. -/
@[simp]
abbrev dropFirstTarget (s : Statement.AfterLinearCombinationWithTarget R pp) :
    Statement.AfterLinearCombination R pp :=
  (s.1, s.2.2)

/-- The **target-preserving** value-level oracle-statement lens for the carried second
sum-check. -/
noncomputable def secondSumcheckStmtLensWithTarget :
    OracleStatement.Lens
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) where
  toFunA := fun ⟨⟨t, stmt⟩, oStmt⟩ =>
    ⟨⟨t, Fin.elim0⟩,
     fun _ => ⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt,
               secondSCVP_mem_restrictDegree pp (dropFirstTarget pp stmt) oStmt⟩⟩
  toFunB := fun ⟨⟨_t, stmt⟩, oStmt⟩ ⟨⟨t', r_y⟩, _innerO⟩ => ⟨((t', r_y), stmt), oStmt⟩

/-- The **target-preserving** oracle-routing lens for the carried second sum-check: identical
routing to `secondSumcheckOracleLens` (same `simOStmt` reconstruction through
`dropFirstTarget`, same input-oracle embedding); the lift keeps the terminal target. -/
noncomputable def secondSumcheckOracleLensWithTarget :
    OracleStatement.OracleLens oSpec
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2)
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) where
  toLens := secondSumcheckStmtLensWithTarget pp
  projStmt := fun ⟨t, _stmt⟩ => ⟨t, Fin.elim0⟩
  liftStmt := fun ⟨_t, stmt⟩ ⟨t', r_y⟩ => ((t', r_y), stmt)
  simOStmt := fun q => match q with
    | ⟨_, point⟩ => ReaderT.mk fun ⟨_t, stmt⟩ =>
        secondSumcheckEvalFromOracles pp oSpec (dropFirstTarget pp stmt) point
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl

/-- The **target-preserving** value-level oracle context lens for the carried second
sum-check. -/
noncomputable def secondSumcheckContextLensWithTarget :
    OracleContext.Lens
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n))
      (OracleStatement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2) (Sumcheck.Spec.OracleStatement R pp.ℓ_n 2)
      Unit Unit Unit Unit where
  stmt := secondSumcheckStmtLensWithTarget pp
  wit := ⟨fun _ => (), fun _ _ => ()⟩

/-- **The target-preserving Spartan second sum-check oracle reduction**: the lift of the proven
full sum-check oracle reduction onto Spartan's second virtual polynomial, keeping the terminal
target `e₂` in the lifted output statement. -/
noncomputable def secondSumcheckReductionWithTarget :
    OracleReduction oSpec
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n) :=
  (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).liftContext
    (secondSumcheckContextLensWithTarget pp) (secondSumcheckOracleLensWithTarget pp oSpec)

instance instSecondSumcheckWithTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier where
  hCohInl i k h := by
    simp only [secondSumcheckReductionWithTarget, OracleVerifier.liftContext,
      Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [secondSumcheckReductionWithTarget, OracleVerifier.liftContext,
      Function.Embedding.inl_apply] at h
    cases h

/-- **`LiftContextCoherent` instance for the target-preserving second sum-check lens** —
the faithfulness content (`secondSumcheckEvalFromOracles_simOracle2`) is shared with the plain
lens through `dropFirstTarget`; only the output lift differs, and it is coherent by
construction. -/
@[reducible] noncomputable def secondSumcheckCoherentWithTarget :
    OracleVerifier.LiftContextCoherent (secondSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier :=
  liftContextCoherent_of (secondSumcheckOracleLensWithTarget pp oSpec) _
    (fun _ _ => rfl)
    (by
      intro os oos transcript q
      obtain ⟨t, stmt⟩ := os
      obtain ⟨idx, point⟩ := q
      refine (secondSumcheckEvalFromOracles_simOracle2 pp oSpec oos transcript.messages
        (dropFirstTarget pp stmt) point).trans ?_
      simp only [secondSumcheckOracleLensWithTarget, secondSumcheckStmtLensWithTarget,
        OracleStatement.Lens.proj, OracleInterface.simOracle2, QueryImpl.addLift,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
        OracleInterface.simOracle0, OracleInterface.answer]
      rfl)
    (by
      intro os oos transcript so
      obtain ⟨t, stmt⟩ := os
      simp [secondSumcheckOracleLensWithTarget, secondSumcheckStmtLensWithTarget,
        OracleStatement.Lens.lift, OracleStatement.Lens.proj])

/-! ## The rbr knowledge-soundness surface -/

/-- Honest local input relation for the target-preserving second sum-check RBR-KS leaf: the
inner round-0 sum-check claim (`T` = cube sum of the second virtual polynomial), pulled back
through the carried lens. -/
abbrev secondSumcheckWithTargetRbrRelIn :
    Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  Extractor.Lens.Honest.pullbackRelIn (secondSumcheckOracleLensWithTarget pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))

/-- Honest local output relation for the target-preserving second sum-check RBR-KS leaf: the
inner terminal claim transported back through the carried lens. Because the lift **keeps** the
terminal target `e₂`, this relation genuinely pins it (`secondSumcheckWithTargetRbrRelOut_pins_target`). -/
abbrev secondSumcheckWithTargetRbrRelOut :
    Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  Extractor.Lens.Honest.transportedRelOut (secondSumcheckOracleLensWithTarget pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
    ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
      |>.compatStatement (secondSumcheckOracleLensWithTarget pp oSpec).toLens)

/-- **The kept target is pinned.** Membership in the target-preserving transported output
relation pins the carried target `y.1.1.1.1` (= `e₂`): every compatible inner terminal
statement lifting to it has that target and satisfies the terminal sum-check relation. -/
theorem secondSumcheckWithTargetRbrRelOut_pins_target
    (y : (Statement.AfterSecondSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)
    (hy : y ∈ secondSumcheckWithTargetRbrRelOut pp oSpec)
    (sIn : (R × Statement.AfterLinearCombinationWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i))
    (sOut : Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n) ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i))
    (hCompat : (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n
        oSpec).verifier.toVerifier.compatStatement
        (secondSumcheckOracleLensWithTarget pp oSpec).toLens sIn sOut)
    (hLift : (secondSumcheckOracleLensWithTarget pp oSpec).toLens.lift sIn sOut = y.1) :
    sOut.1.target = y.1.1.1.1 ∧
      (sOut, ()) ∈ Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R)
        (Fin.last pp.ℓ_n) := by
  refine ⟨?_, hy sIn sOut hCompat hLift⟩
  obtain ⟨⟨t, stmt⟩, oStmt⟩ := sIn
  obtain ⟨⟨t_out, r_y⟩, oStmt'⟩ := sOut
  rw [← hLift]
  rfl

section KS

local instance secondSumcheckWithTarget_instInhabitedStatementRound {n : ℕ} {i : Fin (n + 1)} :
    Inhabited (Sumcheck.Spec.StatementRound R n i) :=
  ⟨⟨0, fun _ => 0⟩⟩

noncomputable local instance secondSumcheckWithTarget_instInhabitedOracleStatement
    {n deg : ℕ} {i : Unit} :
    Inhabited (Sumcheck.Spec.OracleStatement R n deg i) :=
  ⟨⟨0, by simp⟩⟩

/-- **The target-preserving second sum-check RBR-KS transfer** over the honest transported
relation contract, reduced to the inner generic multi-round sum-check RBR-KS theorem. -/
theorem secondSumcheckWithTarget_rbrKnowledgeSoundness_honest
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rbrKnowledgeError : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier
        |>.rbrKnowledgeSoundness init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
        rbrKnowledgeError) :
    (secondSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (secondSumcheckWithTargetRbrRelIn pp oSpec)
      (secondSumcheckWithTargetRbrRelOut pp oSpec)
      rbrKnowledgeError := by
  haveI := secondSumcheckCoherentWithTarget (R := R) pp oSpec
  letI : Extractor.Lens.IsKnowledgeSound
      (secondSumcheckWithTargetRbrRelIn pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckWithTargetRbrRelOut pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
        |>.compatStatement (secondSumcheckOracleLensWithTarget pp oSpec).toLens)
      (fun _ _ => True)
      ⟨(secondSumcheckOracleLensWithTarget pp oSpec).toLens, Witness.InvLens.trivial⟩ :=
    Extractor.Lens.Honest.honestLensKS (secondSumcheckOracleLensWithTarget pp oSpec).toLens
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
        |>.compatStatement (secondSumcheckOracleLensWithTarget pp oSpec).toLens)
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (V := (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier)
    (stmtLens := secondSumcheckOracleLensWithTarget pp oSpec)
    (witLens := Witness.InvLens.trivial)
    h_inner

set_option linter.unusedFintypeInType false in
/-- **The target-preserving second sum-check RBR-KS leaf** at per-round error `2/|R|`. -/
theorem secondSumcheckWithTarget_rbrKnowledgeSoundness_honest_full [Inhabited R]
    {σ : Type} [Subsingleton σ] {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
      (fun _ => (2 : ℝ≥0) / (Fintype.card R)) :=
  secondSumcheckWithTarget_rbrKnowledgeSoundness_honest (R := R) pp oSpec
    (fun _ => (2 : ℝ≥0) / (Fintype.card R))
    (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      (R := R) (deg := 2) (D := boolEmbedding R) (n := pp.ℓ_n)
      (oSpec := oSpec) (init := init) (impl := impl) hInit hInitNF)

end KS

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.secondSumcheckReductionWithTarget
#print axioms Spartan.Spec.secondSumcheckWithTargetRbrRelOut_pins_target
#print axioms Spartan.Spec.secondSumcheckWithTarget_rbrKnowledgeSoundness_honest
#print axioms Spartan.Spec.secondSumcheckWithTarget_rbrKnowledgeSoundness_honest_full
