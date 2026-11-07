/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift

/-!
# Target-carrying mid-chain rounds for the tight Spartan composition (issue #329, X-lane)

The tight relation chain of #329 threads the first sum-check's terminal target `e₁` from the
landed `firstSumcheckReductionWithTarget` (`FirstSumcheckWithTarget.lean`) through the short
middle rounds to the final guard. This file provides the **carried variants** of the three
middle rounds, cloned from `Basic.lean` / `Composition.lean` with the extra leading `R` slot
forwarded untouched:

* `sendEvalClaimWithTarget` — the bundled-eval-claim message round at statement
  `(e₁, (r_x, τ, 𝕩))`;
* `linearCombinationWithTarget` — the RLC challenge round, output `(r, (e₁, (r_x, τ, 𝕩)))`;
* `prependRLCTargetWithTarget` — the honest RLC-target adapter, output
  `(T, (r, (e₁, (r_x, τ, 𝕩))))` with `T = ∑ idx, r idx * v idx` read from the bundled claim
  oracle.

Each round uses the same proved canonical output routing as its completed uncarried phase,
and has a compiled-verifier closed form
(mirroring `sendEvalClaim_toVerifier_closed` / `linearCombination_toVerifier_closed` /
`prependRLCTarget_toVerifier_pure`), which the tight leaves (`TightMidLeaves.lean`) consume.

The statement-type threading follows the target-first convention of
`Statement.AfterFirstSumcheckWithTarget = R × Statement.AfterFirstSumcheck` set by the landed
first-sum-check carry; see the type-threading spec posted on #329.
-/

open OracleComp OracleSpec ProtocolSpec Function

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-! ## Carried statement types -/

/-- Statement after the carried `sendEvalClaim`: the carried terminal target `e₁` in front of
the unchanged `AfterSendEvalClaim` statement. Definitionally equal to
`Statement.AfterFirstSumcheckWithTarget` since `sendEvalClaim` does not change the statement. -/
@[simp]
abbrev Statement.AfterSendEvalClaimWithTarget : Type :=
  R × Statement.AfterSendEvalClaim R pp

/-- Statement after the carried `linearCombination`: the RLC challenge prepended onto the
carried `AfterSendEvalClaim` statement, i.e. `(r, (e₁, (r_x, τ, 𝕩)))`. -/
@[simp]
abbrev Statement.AfterLinearCombinationWithTarget : Type :=
  LinearCombinationChallenge R × Statement.AfterSendEvalClaimWithTarget R pp

variable {R}

/-! ## The carried `sendEvalClaim` round -/

/-- The oracle prover for the carried `sendEvalClaim`: forwards the carried target and the
statement, sends the bundled evaluation claim computed from the *inner* statement (the carried
slot does not enter the claim computation). Clone of `sendEvalClaimProver`. -/
noncomputable def sendEvalClaimWithTargetProver :
    OracleProver oSpec
      (Statement.AfterFirstSumcheckWithTarget R pp) (OracleStatement.AfterFirstSumcheck R pp)
      Unit
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      Unit
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  PrvState := fun _ =>
    (Statement.AfterFirstSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × BundledEvalClaim R
  input := fun ⟨⟨stmt, oStmt⟩, _wit⟩ => (⟨stmt, oStmt⟩, evalClaimValue R pp stmt.2 oStmt)
  sendMessage | ⟨0, _⟩ => fun st => pure (st.2, st)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => pure
    (⟨st.1.1,
      fun i => match i with
        | .inl idx => st.2 idx
        | .inr j => st.1.2 j⟩,
     ())

/-- The oracle verifier for the carried `sendEvalClaim`: forwards the carried statement
unchanged, materializes each scalar claim from the bundled `P_to_V` message and forwards the
remaining input oracles. Clone of `sendEvalClaimVerifier`. -/
def sendEvalClaimWithTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterFirstSumcheckWithTarget R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  verify := fun stmt _challenges => pure stmt
  outputOracle := (sendEvalClaimVerifier R pp oSpec).outputOracle

/-- The carried `sendEvalClaim` oracle reduction. -/
noncomputable def sendEvalClaimWithTarget :
    OracleReduction oSpec
      (Statement.AfterFirstSumcheckWithTarget R pp) (OracleStatement.AfterFirstSumcheck R pp)
      Unit
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      Unit
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  prover := sendEvalClaimWithTargetProver pp oSpec
  verifier := sendEvalClaimWithTargetVerifier pp oSpec

/-- The oracle prover for the carried `linearCombination`: receives the RLC challenge and
prepends it onto the carried statement. Clone of `linearCombinationProver`. -/
def linearCombinationWithTargetProver :
    OracleProver oSpec
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      Unit
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  PrvState
  | 0 => (Statement.AfterSendEvalClaimWithTarget R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit
  | 1 => (Statement.AfterSendEvalClaimWithTarget R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × (LinearCombinationChallenge R)
  input := fun x => x
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st => pure fun r => (st.1, r)
  output := fun ⟨⟨stmt, oStmt⟩, r⟩ => pure (((r, stmt), oStmt), ())

/-- The oracle verifier for the carried `linearCombination`: returns the challenge prepended
onto the carried statement, identity-routing every oracle. Clone of
`linearCombinationVerifier`. -/
def linearCombinationWithTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp)
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  verify := fun stmt chal => do
    let r : LinearCombinationChallenge R := chal ⟨0, rfl⟩
    pure (r, stmt)
  outputOracle := (linearCombinationVerifier R pp oSpec).outputOracle

/-- The carried `linearCombination` oracle reduction. -/
def linearCombinationWithTarget :
    OracleReduction oSpec
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      Unit
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      ⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ where
  prover := linearCombinationWithTargetProver pp oSpec
  verifier := linearCombinationWithTargetVerifier pp oSpec

/-- The 0-round honest RLC-target oracle prover at the carried statement: emits
`∑ idx, r idx * v idx` (the RLC challenge is the *outer* slot `st.1.1.1` of the carried
statement), reading each canonical scalar claim oracle `.inl idx`. Clone of
`prependRLCTargetProver`. -/
noncomputable def prependRLCTargetWithTargetProver :
    OracleProver oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  PrvState := fun _ =>
    Statement.AfterLinearCombinationWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun st =>
    pure (((∑ idx, st.1.1 idx * (show R from st.2 (.inl idx)), st.1), st.2), ())

/-- The honest RLC-target verifier at the carried statement: queries the bundled claim oracle
for each matrix index and emits `(∑ idx, r idx * v idx, stmt)`. Clone of
`prependRLCTargetVerifier` (which reads the RLC challenge from the leading statement slot —
unchanged here, since the carried statement still has the RLC challenge outermost). -/
noncomputable def prependRLCTargetWithTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp)
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) !p[] where
  verify := fun stmt _ => do
    let claims ← (liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM
        (Bricks.rlcStep pp oSpec)) :
      OptionT (OracleComp _) (List (R1CS.MatrixIdx × R)))
    let rlc : R := (claims.map (fun p => stmt.1 p.1 * p.2)).sum
    pure (rlc, stmt)
  outputOracle := (Bricks.prependRLCTargetVerifier pp oSpec).outputOracle

/-- The carried honest RLC-target oracle reduction between `linearCombinationWithTarget` and
the carried second sum-check. -/
noncomputable def prependRLCTargetWithTarget :
    OracleReduction oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] where
  prover := prependRLCTargetWithTargetProver pp oSpec
  verifier := prependRLCTargetWithTargetVerifier pp oSpec

section ClosedForms

variable [Inhabited R]

/-- The closed-form output map of the compiled carried `sendEvalClaim` verifier: forward the
carried statement, materialize the indexed scalar claim from the bundled message, and pass the
remaining input oracles through. Clone of `sendEvalClaimRouteMap`. -/
def sendEvalClaimWithTargetRouteMap
    (p : Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)
    (m : ∀ i, EvalClaim R i) :
    Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i :=
  (p.1, fun i => match i with
    | .inl idx => m idx
    | .inr j => p.2 j)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] [Inhabited R] in
/-- The compiled carried `sendEvalClaim` verifier, in closed form. -/
theorem sendEvalClaimWithTarget_toVerifier_closed :
    (sendEvalClaimWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (sendEvalClaimWithTargetRouteMap (R := R) pp p
          (tr.messages ⟨0, rfl⟩))⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (sendEvalClaimWithTarget (R := R) pp oSpec).verifier (fun p _ => p.1)
    (fun _ _ _ => by
      simp only [sendEvalClaimWithTarget, sendEvalClaimWithTargetVerifier]
      exact simulateQ_pure _ _)]
  congr 1

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] [Inhabited R] in
/-- The compiled carried `linearCombination` verifier, in closed form: it returns the sampled
RLC challenge prepended onto the carried statement and passes every oracle through. -/
theorem linearCombinationWithTarget_toVerifier_closed :
    (linearCombinationWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure ((fun p (c : LinearCombinationChallenge R) => ((c, p.1), p.2)) p
          (tr.challenges ⟨0, rfl⟩))⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (linearCombinationWithTarget (R := R) pp oSpec).verifier
    (fun p tr => (tr.challenges ⟨0, rfl⟩, p.1))
    (fun _ _ _ => by
      simp only [linearCombinationWithTarget, linearCombinationWithTargetVerifier]
      exact simulateQ_pure _ _)]
  rfl

end ClosedForms

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.sendEvalClaimWithTarget_toVerifier_closed
#print axioms Spartan.Spec.linearCombinationWithTarget_toVerifier_closed
