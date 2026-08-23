/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.HonestKnowledgeLens
import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckFaithful
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle

/-!
# Spartan sum-check RBR-KS leaves over the honest transported relations (#114)

The R1CS-carrying first/second sum-check relations used for perfect completeness are not honest
local knowledge-soundness contracts: the local sum-check claim at one sampled point does not imply
R1CS satisfiability.  The correct phase-local RBR-KS leaves are the canonical pullback input
relation and transported output relation of the sum-check oracle lens.  This module packages those
relations and proves the two Spartan lift steps from the inner generic sum-check RBR-KS theorem.
-/

open MvPolynomial OracleComp ProtocolSpec Sumcheck
open scoped NNReal

namespace Spartan.Spec

noncomputable section

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Sum-check round statements are inhabited by the zero target with zero challenges. -/
local instance sumcheckKnowledgeLeaves_instInhabitedStatementRound {n : ℕ} {i : Fin (n + 1)} :
    Inhabited (Sumcheck.Spec.StatementRound R n i) :=
  ⟨⟨0, fun _ => 0⟩⟩

/-- Sum-check oracle statements are inhabited by the zero polynomial. -/
noncomputable local instance sumcheckKnowledgeLeaves_instInhabitedOracleStatement
    {n deg : ℕ} {i : Unit} :
    Inhabited (Sumcheck.Spec.OracleStatement R n deg i) :=
  ⟨⟨0, by simp⟩⟩

/-- Honest local input relation for the Spartan first sum-check RBR-KS leaf: the inner round-0
sum-check claim, pulled back through `firstSumcheckOracleLens`. -/
abbrev firstSumcheckRbrRelIn :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  Extractor.Lens.Honest.pullbackRelIn (firstSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))

/-- Honest local output relation for the Spartan first sum-check RBR-KS leaf: the inner terminal
sum-check claim transported back through `firstSumcheckOracleLens`. -/
abbrev firstSumcheckRbrRelOut :
    Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  Extractor.Lens.Honest.transportedRelOut (firstSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
      |>.compatStatement (firstSumcheckOracleLens pp oSpec).toLens)

/-- Honest local input relation for the Spartan second sum-check RBR-KS leaf: the inner round-0
sum-check claim, pulled back through `secondSumcheckOracleLens`. -/
abbrev secondSumcheckRbrRelIn :
    Set (((R × Statement.AfterLinearCombination R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  Extractor.Lens.Honest.pullbackRelIn (secondSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))

/-- Honest local output relation for the Spartan second sum-check RBR-KS leaf: the inner terminal
sum-check claim transported back through `secondSumcheckOracleLens`. -/
abbrev secondSumcheckRbrRelOut :
    Set ((Statement.AfterSecondSumcheck R pp ×
        (∀ i, OracleStatement.AfterSecondSumcheck R pp i)) × Unit) :=
  Extractor.Lens.Honest.transportedRelOut (secondSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
    ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
      |>.compatStatement (secondSumcheckOracleLens pp oSpec).toLens)

set_option linter.unusedFintypeInType false in
/-- The first Spartan sum-check RBR-KS leaf over the honest transported relation contract, reduced
to the inner generic multi-round sum-check RBR-KS theorem. -/
theorem firstSumcheck_rbrKnowledgeSoundness_honest
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rbrKnowledgeError : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
        |>.rbrKnowledgeSoundness init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
        rbrKnowledgeError) :
    (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckRbrRelIn pp oSpec)
      (firstSumcheckRbrRelOut pp oSpec)
      rbrKnowledgeError := by
  haveI := firstSumcheckCoherent (R := R) pp oSpec
  letI : Extractor.Lens.IsKnowledgeSound
      (firstSumcheckRbrRelIn pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckRbrRelOut pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
        |>.compatStatement (firstSumcheckOracleLens pp oSpec).toLens)
      (fun _ _ => True)
      ⟨(firstSumcheckOracleLens pp oSpec).toLens, Witness.InvLens.trivial⟩ :=
    Extractor.Lens.Honest.honestLensKS (firstSumcheckOracleLens pp oSpec).toLens
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
        |>.compatStatement (firstSumcheckOracleLens pp oSpec).toLens)
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (V := (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier)
    (stmtLens := firstSumcheckOracleLens pp oSpec)
    (witLens := Witness.InvLens.trivial)
    h_inner

set_option linter.unusedFintypeInType false in
/-- The first Spartan sum-check RBR-KS leaf over the honest transported relation contract, with
the generic multi-round sum-check oracle RBR-KS theorem plugged in. -/
theorem firstSumcheck_rbrKnowledgeSoundness_honest_full [Inhabited R]
    {σ : Type} [Subsingleton σ] {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (firstSumcheckReduction (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckRbrRelIn (R := R) pp oSpec)
      (firstSumcheckRbrRelOut (R := R) pp oSpec)
      (fun _ => (3 : ℝ≥0) / (Fintype.card R)) :=
  firstSumcheck_rbrKnowledgeSoundness_honest (R := R) pp oSpec
    (fun _ => (3 : ℝ≥0) / (Fintype.card R))
    (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      (R := R) (deg := 3) (D := boolEmbedding R) (n := pp.ℓ_m)
      (oSpec := oSpec) (init := init) (impl := impl) hInit hInitNF)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- The second Spartan sum-check RBR-KS leaf over the honest transported relation contract, reduced
to the inner generic multi-round sum-check RBR-KS theorem. -/
theorem secondSumcheck_rbrKnowledgeSoundness_honest
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rbrKnowledgeError : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier
        |>.rbrKnowledgeSoundness init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
        rbrKnowledgeError) :
    (secondSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (secondSumcheckRbrRelIn pp oSpec)
      (secondSumcheckRbrRelOut pp oSpec)
      rbrKnowledgeError := by
  haveI := secondSumcheckCoherent (R := R) pp oSpec
  letI : Extractor.Lens.IsKnowledgeSound
      (secondSumcheckRbrRelIn pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckRbrRelOut pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
        |>.compatStatement (secondSumcheckOracleLens pp oSpec).toLens)
      (fun _ _ => True)
      ⟨(secondSumcheckOracleLens pp oSpec).toLens, Witness.InvLens.trivial⟩ :=
    Extractor.Lens.Honest.honestLensKS (secondSumcheckOracleLens pp oSpec).toLens
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.toVerifier
        |>.compatStatement (secondSumcheckOracleLens pp oSpec).toLens)
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (V := (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier)
    (stmtLens := secondSumcheckOracleLens pp oSpec)
    (witLens := Witness.InvLens.trivial)
    h_inner

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- The second Spartan sum-check RBR-KS leaf over the honest transported relation contract, with
the generic multi-round sum-check oracle RBR-KS theorem plugged in. -/
theorem secondSumcheck_rbrKnowledgeSoundness_honest_full [Inhabited R]
    {σ : Type} [Subsingleton σ] {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (secondSumcheckReduction (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (secondSumcheckRbrRelIn (R := R) pp oSpec)
      (secondSumcheckRbrRelOut (R := R) pp oSpec)
      (fun _ => (2 : ℝ≥0) / (Fintype.card R)) :=
  secondSumcheck_rbrKnowledgeSoundness_honest (R := R) pp oSpec
    (fun _ => (2 : ℝ≥0) / (Fintype.card R))
    (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      (R := R) (deg := 2) (D := boolEmbedding R) (n := pp.ℓ_n)
      (oSpec := oSpec) (init := init) (impl := impl) hInit hInitNF)

#print axioms firstSumcheck_rbrKnowledgeSoundness_honest
#print axioms firstSumcheck_rbrKnowledgeSoundness_honest_full
#print axioms secondSumcheck_rbrKnowledgeSoundness_honest
#print axioms secondSumcheck_rbrKnowledgeSoundness_honest_full

end

end Spartan.Spec
