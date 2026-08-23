/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightSeamBridge
import ArkLib.ProofSystem.Spartan.FinalCheckWithClaimLeaf

/-!
# The tight terminal leaf `h₈` (issue #329, X-lane)

The zero-round terminal check of the tight chain, over the doubly-carried statement
`((e₂, r_y), (r, (e₁, (r_x, τ, 𝕩))))`: a `CheckClaim` whose **semantic output relation**
(`tightFinalRelOut`) demands *both* terminal identities:

* the second-terminal identity `e₂ = eval r_y ℳ` (the carried second sum-check target equals
  the second virtual polynomial's evaluation — quantifier-free, checkable by the next stage
  from the final statement and oracles), and
* the first-terminal binding identity `e₁ = eq̃(τ)(r_x)·(v_A·v_B − v_C)`.

Following the honest `FinalCheckWithClaimLeaf` pattern: the oracle `CheckClaim` discards the
predicate's `Prop`, so the binding content lives in the relation; rbr knowledge soundness is the
pred-generic transport (`CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport`) along

  `tightFinalRelOut ⊆ (transported₂ ∩ binding)` ,

whose content — **the direct second-terminal identity implies the transported relation** — is the
∀-side collapse: the lift pins the inner terminal statement, the oracle-pinning keystone
(`mem_support_oracleVerifier_run_oStmt`) pins the inner oracle to the honest second virtual
polynomial, and the terminal relation collapses to the direct evaluation identity
(`relationRound_last_iff_deg`, the degree-generic form of `relationRound_last_iff`).

This closes the leaf chain `h₁ … h₈` of the tight composition.
-/

open OracleComp OracleSpec ProtocolSpec Function Finset
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

-- `relationRound_last_iff_deg` now lives in `TightMidLeaves.lean` (DRY-audit item 7); it
-- resolves here through the import chain unchanged.

/-- **The tight final output relation** — the acceptance currency of the tight chain, checkable
by the next stage from the final statement and oracles (no quantifiers): the second-terminal
identity `e₂ = eval r_y ℳ` *and* the first-terminal binding identity. -/
@[reducible]
def tightFinalRelOut :
    Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | x.1.1.1.1 = MvPolynomial.eval x.1.1.1.2
        (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp x.1.1.2) x.1.2)
      ∧ (x.1.1.2.2, x.1.2) ∈ evalClaimBindingRel (R := R) pp }

/-- The tight terminal predicate (documentation-level: the oracle `CheckClaim` discards the
`Prop`; the semantic content lives in `tightFinalRelOut`). It mirrors `finalClaimPredicate`
through the target-dropping projections. -/
noncomputable def tightFinalPredicate :
    ReaderT (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleComp [OracleStatement.AfterLinearCombination R pp]ₒ) Prop :=
  fun stmt => do
    let expected ← finalExpectedClaimFromOracles R pp (stmt.1.2, dropFirstTarget pp stmt.2)
    pure (stmt.1.1 = expected)

/-- **The tight terminal check**: a zero-round `CheckClaim` at the doubly-carried statement. -/
noncomputable def finalCheckTight :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] :=
  CheckClaim.oracleReduction oSpec
    (Statement.AfterSecondSumcheckWithTarget R pp)
    (OracleStatement.AfterLinearCombination R pp)
    (tightFinalPredicate pp)

/-! ## The doom transport: direct ⟹ transported -/

/-- **The ∀-side collapse at the second terminal**: the direct identity `e₂ = eval r_y ℳ`
implies membership in the carried transported output relation — every compatible inner output
lifting to it carries the honest polynomial (oracle pinning) and the pinned terminal target, so
the terminal relation is exactly the direct identity. -/
theorem transported₂_of_direct
    (p : Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hE2 : p.1.1.1 = MvPolynomial.eval p.1.1.2
        (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp p.1.2) p.2)) :
    (p, ()) ∈ secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec := by
  rintro ⟨⟨T', stmt'⟩, oStmt'⟩ ⟨⟨t', r_y'⟩, innerO⟩ hCompat hLift
  -- The lift pins the passenger and the inner terminal statement.
  have h1 : ((t', r_y'), stmt') = p.1 := congrArg Prod.fst hLift
  have h2 : oStmt' = p.2 := congrArg Prod.snd hLift
  have he : t' = p.1.1.1 := congrArg (fun q => q.1.1) h1
  have hr : r_y' = p.1.1.2 := congrArg (fun q => q.1.2) h1
  have hst : stmt' = p.1.2 := congrArg (fun q => q.2) h1
  -- The oracle-pinning keystone: the compatible inner oracle is the honest virtual polynomial.
  have hpin : innerO = ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      ((T', stmt'), oStmt')).2 := by
    obtain ⟨tr, htr⟩ := hCompat
    exact Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt htr
  rw [hpin]
  refine (relationRound_last_iff_deg t' r_y' _).mpr ?_
  show MvPolynomial.eval r_y'
      (secondSumCheckVirtualPolynomial R pp (dropFirstTarget pp stmt') oStmt') = t'
  rw [hr, hst, h2, he]
  exact hE2.symm

section Leaf

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₈` (tight chain): the tight terminal check is perfectly rbr knowledge-sound** from
the conjoined carried second sum-check output relation to the tight final relation, error `0`.
The transport `tightFinalRelOut ⊆ transported₂ ∩ binding` is `transported₂_of_direct` plus the
binding pass-through. -/
theorem finalCheckTight_rbrKnowledgeSoundness :
    (finalCheckTight (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      ((secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) 0 :=
  CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport
    (tightFinalPredicate pp) init impl
    (fun p hOut => ⟨transported₂_of_direct pp oSpec p hOut.1, hOut.2⟩)

end Leaf

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.relationRound_last_iff_deg
#print axioms Spartan.Spec.Bricks.transported₂_of_direct
#print axioms Spartan.Spec.Bricks.finalCheckTight_rbrKnowledgeSoundness
