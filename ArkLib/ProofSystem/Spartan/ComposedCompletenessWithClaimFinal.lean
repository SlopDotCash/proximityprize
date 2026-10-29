/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ProximityPrize.Extensions.ProofSystem.Component.ReduceClaim
import ArkLib.ProofSystem.Spartan.TightCompletenessProven
import ArkLib.ProofSystem.Spartan.TightTerminalToValueRel

/-!
# Spartan composed PIOP perfect completeness with claim — final assembly (issue #114)

This file discharges the **target-carrying** composed completeness obligation
`composedCompletenessWithClaimStatement` at the composition
`(composedPIOP_Rc …).append (prependClaim …)`.

**Why this `Rc` and not `composedPIOPWithClaim_Rc`:** the residual is parameterized over the
composed reduction (any `Rc : OracleReduction … pSpecC` qualifies). The in-tree
`composedPIOPWithClaim_Rc` nests `prependClaim` at the *innermost* position
(`… (finalCheck.append prependClaim)`), while the proven base apex
`composedCompletenessStatement_proven` is about the 8-fold `composedPIOP_Rc`. Reduction
`append` is **not definitionally associative** (the protocol-spec `Fin.vappend` nests
differently), so the outer-append composition here is a *different* (equally valid) witness:
the empty-seam keystone applies directly to it, with no re-derivation of the seven inner
seams. A proof for the right-nested `composedPIOPWithClaim_Rc` variant would require
re-running the full seam chain with `finalCheck.append prependClaim` as the deepest block —
deliberately not duplicated here.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512
set_option linter.unusedSectionVars false

variable {R : Type 0} [CommRing R] [IsDomain R] [DecidableEq R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

noncomputable instance instComposedPSpecOuterClaimMessage :
    ∀ i, OracleInterface (((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := composedPSpec (R := R) pp)
    (pSpec₂ := (!p[] : ProtocolSpec 0))

noncomputable instance instComposedPSpecOuterClaimChallenge :
    ∀ i, SampleableType (((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := composedPSpec (R := R) pp)
    (pSpec₂ := (!p[] : ProtocolSpec 0))

noncomputable instance instComposedPSpecOuterClaimChallengeFintype :
    ∀ i, Fintype (((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).Challenge i) :=
  by
    have : ∀ j, Fintype ((composedPSpec (R := R) pp).Challenge j) := c0F (R := R) pp
    exact ProtocolSpec.appendChallenge_fintype (composedPSpec (R := R) pp)
      (!p[] : ProtocolSpec 0)

noncomputable instance instComposedPSpecOuterClaimChallengeInhabited :
    ∀ i, Inhabited (((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).Challenge i) :=
  by
    have : ∀ j, Inhabited ((composedPSpec (R := R) pp).Challenge j) := c0I (R := R) pp
    exact ProtocolSpec.appendChallenge_inhabited (composedPSpec (R := R) pp)
      (!p[] : ProtocolSpec 0)

/-- **Target-carrying composed Spartan PIOP perfect completeness, fully discharged
(issue #114)**, at the outer-append composition `(composedPIOP_Rc …).append (prependClaim …)`:
the proven 8-fold completeness apex followed by the proven 0-round claim-slot adapter, glued
by the empty-seam keystone, with the output relation relaxed to the residual's
`finalCheckWithClaimRelOut` (= `Set.univ`). Only the standard honest-implementation side
conditions remain as inputs. -/
theorem composedCompletenessWithClaimStatement_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0) :
    composedCompletenessWithClaimStatement R pp oSpec
      ((composedPIOP_Rc (R := R) pp oSpec).append (prependClaim (R := R) pp oSpec)) init impl := by
  have h_base := composedCompletenessStatement_proven (R := R) pp oSpec hm hn hInit hImplSupp
    himplSP himplNF
  have h_claim := prependClaim_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl) (finalCheckRelOut R pp)
  unfold composedCompletenessWithClaimStatement
  -- the per-index and bundled challenge-oracle instances for the empty-seam keystone
  have : ∀ j, Fintype ((composedPSpec (R := R) pp).Challenge j) := c0F pp
  have : ∀ j, Inhabited ((composedPSpec (R := R) pp).Challenge j) := c0I pp
  have := ProtocolSpec.challengeOracle_fintype (composedPSpec (R := R) pp)
  have := ProtocolSpec.challengeOracle_inhabited (composedPSpec (R := R) pp)
  have := ProtocolSpec.challengeOracle_fintype
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  have := ProtocolSpec.challengeOracle_inhabited
      ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  have := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  have := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  have h := OracleReduction.append_perfectCompleteness_keystone_empty_114
    (composedPIOP_Rc (R := R) pp oSpec) (prependClaim (R := R) pp oSpec)
    h_base h_claim hInit hImplSupp
  exact Reduction.completeness_relOut_mono init impl
    (Set.subset_univ _) h

/-- Project the tight terminal statement `((e₂, r_y), (r, (e₁, ...)))` to the public
`FinalClaimStatement` surface by keeping the terminal target `e₂` and dropping the first-sum-check
passenger target `e₁`. -/
def tightFinalToClaimStmt (stmt : Statement.AfterSecondSumcheckWithTarget R pp) :
    FinalClaimStatement R pp :=
  (stmt.1.1, (stmt.1.2, dropFirstTarget pp stmt.2))

/-- Zero-round projection from the tight composed terminal endpoint to the target-carrying final
claim endpoint. The oracle family is unchanged; only the statement is re-associated and the
tight `e₂` target becomes the carried final claim target. -/
noncomputable def tightFinalToClaim :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (FinalClaimStatement R pp) (FinalOracleStatement R pp) Unit
      !p[] :=
  ReduceClaim.oracleReduction oSpec (tightFinalToClaimStmt (R := R) pp)
    (fun _ _ => ()) (Function.Embedding.refl _) (by intro i; rfl)
    (by intro i; exact HEq.rfl)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- The tight terminal relation maps into the semantic final-claim value relation: its first
conjunct pins the carried terminal target to the second-sum-check endpoint, and the endpoint bridge
identifies that value with `finalExpectedClaimValue`. -/
theorem tightFinalToClaim_perfectCompleteness :
    (tightFinalToClaim (R := R) pp oSpec).perfectCompleteness init impl
      (tightFinalRelOut (R := R) pp) (finalCheckWithClaimValueRelIn R pp) := by
  refine ReduceClaim.oracleReduction_completeness
    (oSpec := oSpec)
    (mapStmt := tightFinalToClaimStmt (R := R) pp)
    (mapWit := fun _ _ => ())
    (embedIdx := Function.Embedding.refl _)
    (hEq := by intro i; rfl)
    (hInterface := by intro i; exact HEq.rfl)
    (relIn := tightFinalRelOut (R := R) pp)
    (relOut := finalCheckWithClaimValueRelIn R pp)
    (init := init) (impl := impl) ?_
  intro stmt oStmt wit h
  cases wit
  let x : (Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit :=
    ((stmt, oStmt), ())
  have hmap : ReduceClaim.mapOStmt
      (OStmtIn := OracleStatement.AfterLinearCombination R pp)
      (OStmtOut := FinalOracleStatement R pp)
      (Function.Embedding.refl _) (by intro i; rfl) oStmt = oStmt := by
    funext i
    rfl
  rw [hmap]
  simpa only [x, tightFinalToClaimStmt, tightTerminalToFinalClaim] using
    valueRel_of_tightFinalRelOut (R := R) pp x h

/-- **Semantic target-carrying composed completeness, discharged (issue #352).** The witness is
the proven tight full Spartan composition followed by the zero-round projection
`tightFinalToClaim`, so the final carried target is the tight second-sum-check endpoint rather than
the old `prependClaim` adapter's hardwired `0`. -/
theorem composedCompletenessWithClaimValueRelStatement_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0) :
    composedCompletenessWithClaimValueRelStatement R pp oSpec
      ((composedPIOPTightPure_Rc (R := R) pp oSpec).append
        (tightFinalToClaim (R := R) pp oSpec)) init impl := by
  have h_base := composedTightPure_perfectCompleteness (R := R) pp oSpec hm hn hInit hImplSupp
    himplSP himplNF
  have h_claim := tightFinalToClaim_perfectCompleteness (R := R) pp oSpec
    (init := init) (impl := impl)
  unfold composedCompletenessWithClaimValueRelStatement
  -- the per-index and bundled challenge-oracle instances for the empty-seam keystone
  have : ∀ j, Fintype ((composedPSpec (R := R) pp).Challenge j) := c0F pp
  have : ∀ j, Inhabited ((composedPSpec (R := R) pp).Challenge j) := c0I pp
  have := ProtocolSpec.challengeOracle_fintype (composedPSpec (R := R) pp)
  have := ProtocolSpec.challengeOracle_inhabited (composedPSpec (R := R) pp)
  have := ProtocolSpec.challengeOracle_fintype
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  have := ProtocolSpec.challengeOracle_inhabited
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0))
  have := ProtocolSpec.challengeOracle_fintype (!p[] : ProtocolSpec 0)
  have := ProtocolSpec.challengeOracle_inhabited (!p[] : ProtocolSpec 0)
  exact OracleReduction.append_perfectCompleteness_keystone_empty_114
    (composedPIOPTightPure_Rc (R := R) pp oSpec)
    (tightFinalToClaim (R := R) pp oSpec)
    h_base h_claim hInit hImplSupp

/-- Endpoint-form companion of `composedCompletenessWithClaimValueRelStatement_proven`. -/
theorem composedCompletenessWithClaimSecondSumcheckEvalStatement_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0) :
    composedCompletenessWithClaimSecondSumcheckEvalStatement R pp oSpec
      ((composedPIOPTightPure_Rc (R := R) pp oSpec).append
        (tightFinalToClaim (R := R) pp oSpec)) init impl :=
  composedCompletenessWithClaimSecondSumcheckEvalStatement_of_valueRel
    R pp oSpec
    ((composedPIOPTightPure_Rc (R := R) pp oSpec).append
      (tightFinalToClaim (R := R) pp oSpec))
    init impl
    (composedCompletenessWithClaimValueRelStatement_proven (R := R) pp oSpec
      hm hn hInit hImplSupp himplSP himplNF)

end Spartan.Spec.Bricks

-- Axiom check
#print axioms Spartan.Spec.Bricks.composedCompletenessWithClaimStatement_proven
#print axioms Spartan.Spec.Bricks.tightFinalToClaim_perfectCompleteness
#print axioms Spartan.Spec.Bricks.composedCompletenessWithClaimValueRelStatement_proven
#print axioms Spartan.Spec.Bricks.composedCompletenessWithClaimSecondSumcheckEvalStatement_proven
