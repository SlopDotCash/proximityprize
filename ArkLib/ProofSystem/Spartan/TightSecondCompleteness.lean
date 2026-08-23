/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.PinnedCompleteness
import ArkLib.ProofSystem.Spartan.SecondSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.TightFinalLeaf

/-!
# Enriched carried-second-sum-check completeness (issue #329, B7 transfer, second half)

Mirror of `TightFirstCompleteness.lean` at the carried second sum-check: the honest output
relation pins the carried terminal `e₂ = eval r_y ℳ` — exactly the first conjunct of
`tightFinalRelOut` — via the per-`P` fiber trick over the second virtual polynomial
(`secondSumCheckVirtualPolynomial` through the `dropFirstTarget` projection).

The honest input relation here also records that the prepended target is the cube sum
(the inner round-0 claim), i.e. the `T = ∑ r·v^true` content of `tightRelG` — pulled back
through the carried lens as the pinned round-0 relation on the fiber.
-/

open OracleComp OracleSpec ProtocolSpec MvPolynomial
open scoped NNReal

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Inhabited R] (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The second-sum-check virtual polynomial of a carried post-RLC input, as the inner oracle
statement (the value `secondSumcheckOracleLensWithTarget`'s projection supplies). -/
noncomputable def secondSumcheckVirtualOracle
    (x : (R × Statement.AfterLinearCombinationWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    R⦃≤ 2⦄[X Fin pp.ℓ_n] :=
  ⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp x.1.2) x.2,
   secondSCVP_mem_restrictDegree pp (dropFirstTarget pp x.1.2) x.2⟩

/-- The honest carried-second input relation: the inner round-0 claim (the prepended target is
the cube sum of the second virtual polynomial — the `tightRelG` content, in pulled-back form),
restricted to the fiber of a fixed virtual polynomial `P`. -/
def secondSumcheckWithTargetRelInAt (P : R⦃≤ 2⦄[X Fin pp.ℓ_n]) :
    Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec ∩
  { x | secondSumcheckVirtualOracle pp x.1 = P }

/-- **The enriched carried-second output relation**: the direct terminal identity
`e₂ = eval r_y ℳ` — the first conjunct of `tightFinalRelOut`. -/
def secondSumcheckWithTargetRelOutEnriched :
    Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | x.1.1.1.1 = MvPolynomial.eval x.1.1.1.2
      (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp x.1.1.2) x.1.2) }

set_option linter.unusedSectionVars false in
/-- **The per-fiber lens-completeness instance** at the carried second sum-check. -/
@[reducible] def secondSumcheckWithTargetLensCompleteAt (P : R⦃≤ 2⦄[X Fin pp.ℓ_n]) :
    (secondSumcheckContextLensWithTarget pp).toContext.IsComplete
      (secondSumcheckWithTargetRelInAt pp oSpec P)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_n 2 (boolEmbedding R) P (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckWithTargetRelOutEnriched pp)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_n 2 (boolEmbedding R) P (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.compatContext
        (secondSumcheckContextLensWithTarget pp).toContext) where
  proj_complete := by
    rintro ⟨⟨T, stmt⟩, oStmt⟩ ⟨⟩ ⟨hRelIn, hP⟩
    refine ⟨hRelIn, ?_⟩
    show (fun _ => secondSumcheckVirtualOracle pp ((T, stmt), oStmt)) = fun _ => P
    rw [hP]
  lift_complete := by
    rintro ⟨⟨T, stmt⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_y⟩, innerO⟩ ⟨⟩ _hCompat ⟨hRelIn, hP⟩ ⟨hRel, hPin⟩
    have hpoly : innerO = fun _ => P := hPin
    have hterm : MvPolynomial.eval r_y (innerO ()).val = t_out :=
      (Bricks.relationRound_last_iff_deg (R := R) t_out r_y innerO).mp hRel
    show t_out = MvPolynomial.eval r_y
      (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt)
    rw [← hterm, hpoly]
    have : ((P : R⦃≤ 2⦄[X Fin pp.ℓ_n]) : MvPolynomial (Fin pp.ℓ_n) R)
        = secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt := by
      rw [← hP]
      rfl
    rw [this]

section Theorem

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **Enriched carried-second-sum-check perfect completeness (issue #329, B7).** The honest
output pins the carried terminal: `e₂ = eval r_y ℳ` — the first conjunct of
`tightFinalRelOut`. Unconditional modulo the standard honest execution-model facts. -/
theorem secondSumcheckWithTarget_perfectCompleteness_enriched
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (secondSumcheckWithTargetRelOutEnriched (R := R) pp) := by
  intro stmtIn witIn hmem
  set P : R⦃≤ 2⦄[X Fin pp.ℓ_n] := secondSumcheckVirtualOracle pp stmtIn with hPdef
  letI : (secondSumcheckContextLensWithTarget pp).toContext.IsComplete
      (secondSumcheckWithTargetRelInAt pp oSpec P)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_n 2 (boolEmbedding R) P (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckWithTargetRelOutEnriched pp)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_n 2 (boolEmbedding R) P (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R)
          pp.ℓ_n oSpec).toReduction.compatContext
        (secondSumcheckContextLensWithTarget pp).toContext) :=
    secondSumcheckWithTargetLensCompleteAt pp oSpec P
  haveI := secondSumcheckCoherentWithTarget (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (lens := secondSumcheckContextLensWithTarget pp)
    (stmtLens := secondSumcheckOracleLensWithTarget pp oSpec)
    (outerRelIn := secondSumcheckWithTargetRelInAt pp oSpec P)
    (outerRelOut := secondSumcheckWithTargetRelOutEnriched pp)
    rfl
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_pinned_unconditional P hInit hImplSupp)
    stmtIn witIn ⟨hmem, rfl⟩

end Theorem

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.secondSumcheckWithTargetLensCompleteAt
#print axioms Spartan.Spec.secondSumcheckWithTarget_perfectCompleteness_enriched
