/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightConjoinedSecondLeaf
import ArkLib.ProofSystem.Spartan.SecondSumcheckRelIn

/-!
# The `h₆ → h₇` seam bridge of the tight chain (issue #329, X-lane)

The tight adapter leaf (`prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf`) ends at the
*semantic* relation `tightRelG` (`T = ∑ r·v^true` ∧ binding), while the conjoined carried second
sum-check leaf (`h₇`) starts at the *pullback* relation
`secondSumcheckWithTargetRbrRelIn ∩ binding` (`T` = cube-sum of the carried virtual polynomial
∧ binding). These are **the same set**: the cube-sum of the second virtual polynomial *is* the
RLC of the true evaluation claims (`secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue`
+ the cube-reindex bridge, packaged as `secondSC_relationRound_zero`).

* `secondSC_relationRound_zero_iff` — the round-0 sum-check relation at an arbitrary target `T`
  holds iff `T` equals the true RLC (the iff form of the completeness-side bridge);
* `tightRelG_eq_conjoined_relIn` — the seam set-equality;
* `prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf'` — the `h₆` leaf restated to end
  exactly at `h₇`'s input relation.
-/

open OracleComp OracleSpec ProtocolSpec Function MvPolynomial
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

omit [Inhabited R] [SampleableType R] in
/-- **The iff form of the round-0 bridge**: the second sum-check round-0 relation at target `T`
holds iff `T` is the RLC of the *true* evaluation claims. -/
theorem secondSC_relationRound_zero_iff
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (M : R⦃≤ 2⦄[X Fin pp.ℓ_n])
    (hM : M.val = secondSumCheckVirtualPolynomial R pp stmt oStmt) (T : R) :
    (((⟨T, Fin.elim0⟩ : Sumcheck.Spec.StatementRound R pp.ℓ_n 0),
        fun _ => M), ()) ∈ Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) 0
      ↔ T = ∑ idx, stmt.1 idx * evalClaimValue R pp stmt.2 (fun i => oStmt (.inr i)) idx := by
  have h := secondSC_relationRound_zero pp stmt oStmt M hM
  simp only [Sumcheck.Spec.relationRound, Set.mem_setOf_eq] at h ⊢
  exact ⟨fun h2 => h2.symm.trans h, fun h2 => h.trans h2.symm⟩

omit [Inhabited R] in
/-- **The `h₆ → h₇` seam set-equality**: the semantic adapter output relation `tightRelG` is the
conjoined carried second sum-check input relation. -/
theorem tightRelG_eq_conjoined_relIn :
    tightRelG (R := R) pp
      = (secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec
          ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp}) := by
  ext x
  obtain ⟨⟨⟨T, stmt⟩, oStmt⟩, ⟨⟩⟩ := x
  show (T = _ ∧ _) ↔ _
  constructor
  · rintro ⟨hT, hbind⟩
    refine ⟨?_, hbind⟩
    exact (secondSC_relationRound_zero_iff pp (dropFirstTarget pp stmt)
      (fun i => oStmt i)
      ⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt,
        secondSCVP_mem_restrictDegree pp (dropFirstTarget pp stmt) oStmt⟩ rfl T).mpr hT
  · rintro ⟨hpull, hbind⟩
    refine ⟨?_, hbind⟩
    have := (secondSC_relationRound_zero_iff pp (dropFirstTarget pp stmt)
      (fun i => oStmt i)
      ⟨secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt) oStmt,
        secondSCVP_mem_restrictDegree pp (dropFirstTarget pp stmt) oStmt⟩ rfl T).mp hpull
    exact this

section Leaf

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₆`, restated at the `h₇` seam**: the carried honest RLC-target adapter is perfectly
rbr knowledge-sound from `tightRelF` to the conjoined carried second sum-check input relation. -/
theorem prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf' :
    (prependRLCTargetWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (tightRelF (R := R) pp)
      (secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp}) 0 := by
  rw [← tightRelG_eq_conjoined_relIn (R := R) pp oSpec]
  exact prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf pp oSpec

end Leaf

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.secondSC_relationRound_zero_iff
#print axioms Spartan.Spec.Bricks.tightRelG_eq_conjoined_relIn
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf'
