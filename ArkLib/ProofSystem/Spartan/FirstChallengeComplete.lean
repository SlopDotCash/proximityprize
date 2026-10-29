/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.SpartanFirstChallenge
import ArkLib.ProofSystem.Spartan.FirstChallengeCoherent
import ArkLib.ProofSystem.Spartan.ZeroCheckComplete
import ProximityPrize.Extensions.ProofSystem.Component.RandomQuery

/-!
# The Spartan `firstChallenge` phase is (unconditionally) perfectly complete (issue #114)

Spartan's `firstChallenge` phase (`oracleReduction.firstChallenge`) is the `liftContext` of the
generic `RandomQuery` oracle reduction onto the virtual zero-check polynomial `𝒢` (compared against
the zero polynomial). This module assembles the **completeness transfer** for that lift.

Unlike the two sum-check phases — whose inner multi-round sum-check completeness is the
sequential-composition keystone still being assembled in the framework layer — the inner
`RandomQuery.oracleReduction_completeness` is already a *closed, unconditional* theorem. Hence this
phase's completeness is **unconditional**: it takes no `h_inner` hypothesis.

* `firstChallengeRelIn` / `firstChallengeRelOut` — the outer relations, both "R1CS is satisfied".
  The challenge `τ` produced by the phase is recorded in the output statement but is irrelevant to
  R1CS satisfiability, so it is carried through unchanged.
* `firstChallengeLensComplete` — the `OracleContext.Lens.IsComplete` instance. Its `proj_complete`
  is exactly `zeroCheckVirtualPolynomial_eq_zero_of_satisfied`: an R1CS-satisfying instance makes the
  zero-check polynomial `𝒢` vanish, so the two `RandomQuery` virtual oracles `(𝒢, 0)` agree
  (`RandomQuery.relIn`). Its `lift_complete` is the R1CS pass-through.
* `firstChallenge_perfectCompleteness` — a direct run proof for the one-round challenge adapter:
  the verifier samples `τ`, the prover records it, and the statement/oracles/witness are carried
  through unchanged.
-/

open MvPolynomial OracleComp OracleSpec ProtocolSpec OracleInterface Function

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

local instance :
    VerifierOnly (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

/-- **Outer input relation of the `firstChallenge` phase.** The R1CS instance is satisfied: the
public input `𝕩` (the `AfterFirstMessage` statement is exactly `𝕩`) together with the matrix oracles
`A, B, C` and the witness oracle `𝕨` satisfy `(A𝕫)·(B𝕫) = C𝕫`. -/
def firstChallengeRelIn :
    Set ((Statement.AfterFirstMessage R pp ×
        (∀ i, OracleStatement.AfterFirstMessage R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **Outer output relation of the `firstChallenge` phase.** The same R1CS satisfiability, carried
through: the output statement `(τ, 𝕩)` records the sampled challenge `τ`, but the matrix/witness
oracles and the public input `𝕩 = stmt.2` are unchanged. This is the input relation of the following
first sum-check phase (`firstSumcheckRelIn`). -/
def firstChallengeRelOut :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **`OracleContext.Lens.IsComplete` for the `firstChallenge` lens.**

* `proj_complete`: an R1CS-satisfying Spartan instance projects to a `RandomQuery` instance whose two
  virtual oracles `(𝒢, 0)` agree, i.e. `𝒢 = 0` — exactly `zeroCheckVirtualPolynomial_eq_zero_of_satisfied`.
* `lift_complete`: the lift carries the matrices/witness/public input unchanged (only `τ` is
  recorded), so R1CS satisfiability transfers verbatim. -/
instance firstChallengeLensComplete :
    (firstChallengeContextLens R pp).toContext.IsComplete
      (firstChallengeRelIn pp)
      (RandomQuery.relIn (MvPolynomial (Fin pp.ℓ_m) R))
      (firstChallengeRelOut pp)
      (RandomQuery.relOut (MvPolynomial (Fin pp.ℓ_m) R))
      ((RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).toReduction.compatContext
        (firstChallengeContextLens R pp).toContext) where
  proj_complete := by
    rintro ⟨𝕩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstChallengeRelIn, Set.mem_ofPred_eq] at hRelIn
    simp only [firstChallengeContextLens, firstChallengeStmtLens, RandomQuery.relIn, Set.mem_ofPred_eq]
    exact zeroCheckVirtualPolynomial_eq_zero_of_satisfied pp 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨𝕩, oStmt⟩ ⟨⟩ ⟨q, innerO⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstChallengeRelIn, Set.mem_ofPred_eq] at hRelIn
    exact hRelIn

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- The completed downstream `Unit`-witness challenge phase preserves the R1CS relation and
honest prover/verifier agreement on every raw run outcome. It makes no completion claim about
the inherited canonical admitted constructor. -/
theorem completedFirstChallenge_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.completedFirstChallenge R pp oSpec).perfectCompleteness init impl
      (firstChallengeRelIn (R := R) pp) (firstChallengeRelOut (R := R) pp) := by
  change ((oracleReduction.completedFirstChallenge R pp oSpec).toReduction).perfectCompleteness
    init impl (firstChallengeRelIn (R := R) pp) (firstChallengeRelOut (R := R) pp)
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hRelIn z hz
  simp only [oracleReduction.completedFirstChallenge, OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, firstChallengeProver, firstChallengeVerifier,
    OracleVerifier.toVerifier, Verifier.run] at hz
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    simulateQ_pure, pure_bind, map_pure, liftM_pure,
    Option.elimM, Option.getM_some, Option.map_some] at hz
  simp_all [firstChallengeRelIn, firstChallengeRelOut]
  obtain ⟨q, _, rfl⟩ := hz
  exact ⟨_, q, stmt, oStmt, ⟨(), rfl⟩, hRelIn⟩

end Spartan.Spec

#print axioms Spartan.Spec.completedFirstChallenge_perfectCompleteness
