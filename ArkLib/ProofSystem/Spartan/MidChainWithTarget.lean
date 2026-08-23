/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.ShortPhaseRbrKnowledgeLeaves

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

Each round comes with its `AppendCoherent` instance and its compiled-verifier closed form
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
        | .inl _ => st.2
        | .inr j => st.1.2 j⟩,
     ())

/-- The oracle verifier for the carried `sendEvalClaim`: forwards the carried statement
unchanged, routes the bundled claim output oracle from the `P_to_V` message and the rest from
the inputs. Clone of `sendEvalClaimVerifier`. -/
def sendEvalClaimWithTargetVerifier :
    OracleVerifier oSpec
      (Statement.AfterFirstSumcheckWithTarget R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Statement.AfterSendEvalClaimWithTarget R pp) (OracleStatement.AfterSendEvalClaim R pp)
      ⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ where
  verify := fun stmt _challenges => pure stmt
  embed := {
    toFun := fun
      | .inl _ => .inr default
      | .inr j => .inl j
    inj' := by
      intro a b h
      match a, b with
      | .inl _, .inl _ => congr 1; exact Subsingleton.elim _ _
      | .inl _, .inr _ => simp at h
      | .inr _, .inl _ => simp at h
      | .inr _, .inr _ => simpa using h
  }
  hEq := fun i => match i with
    | .inl _ => rfl
    | .inr _ => rfl

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

instance instSendEvalClaimWithTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (sendEvalClaimWithTargetVerifier (R := R) pp oSpec) where
  hCohInl i k h := by
    dsimp [sendEvalClaimWithTargetVerifier] at h
    cases i <;> cases h <;> rfl
  hCohInr i k h := by
    dsimp [sendEvalClaimWithTargetVerifier] at h
    cases i <;> cases h <;> rfl

/-! ## The carried `linearCombination` round -/

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
  embed := Function.Embedding.inl
  hEq := fun _ => rfl

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

instance instLinearCombinationWithTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (linearCombinationWithTargetVerifier (R := R) pp oSpec) where
  hCohInl i k h := by
    simp only [linearCombinationWithTargetVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [linearCombinationWithTargetVerifier, Function.Embedding.inl_apply] at h
    cases h

/-! ## The carried honest RLC-target adapter -/

/-- The 0-round honest RLC-target oracle prover at the carried statement: emits
`∑ idx, r idx * v idx` (the RLC challenge is the *outer* slot `st.1.1.1` of the carried
statement), reading the bundled eval-claim oracle `.inl 0`. Clone of
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
    pure (((∑ idx, st.1.1 idx * st.2 (.inl 0) idx, st.1), st.2), ())

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
  embed := Embedding.inl
  hEq := by intro i; simp

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

instance instPrependRLCTargetWithTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (prependRLCTargetWithTargetVerifier (R := R) pp oSpec) where
  hCohInl i k h := by
    simp only [prependRLCTargetWithTargetVerifier] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [prependRLCTargetWithTargetVerifier] at h
    cases h

/-! ## Compiled-verifier closed forms -/

section ClosedForms

variable [Inhabited R]

/-- The closed-form output map of the compiled carried `sendEvalClaim` verifier: forward the
carried statement, route the bundled claim oracle from the message, pass the remaining oracles
through. Clone of `sendEvalClaimRouteMap`. -/
def sendEvalClaimWithTargetRouteMap
    (p : Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)
    (m : ∀ i, EvalClaim R i) :
    Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i :=
  (p.1, fun i => match i with
    | .inl _ => m
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
  funext p tr
  congr 1
  unfold sendEvalClaimWithTargetRouteMap
  congr 1
  funext i
  cases i with
  | inl j => rfl
  | inr j => rfl

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
