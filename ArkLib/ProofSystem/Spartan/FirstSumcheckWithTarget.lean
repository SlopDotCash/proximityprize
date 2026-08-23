/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.FirstSumcheckRelComplete
import ArkLib.OracleReduction.LiftContext.HonestKnowledgeLens
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessUncondCorrect

/-!
# The target-preserving Spartan first sum-check lift (issue #329, Brick B)

`firstSumcheckReduction`'s lens **drops** the inner sum-check's terminal target: its
`toFunB := fun (stmt, oStmt) ((t', r_x), innerO) => ((r_x, stmt), oStmt)` discards `t'`, so nothing
downstream of the lifted reduction can refer to the value the sum-check pinned. This module builds
the **target-preserving variant**: the lifted output statement is
`Statement.AfterFirstSumcheckWithTarget := R × Statement.AfterFirstSumcheck` (target first,
matching the `prependRLCTarget` convention `R × stmt` used by the second sum-check's *input* side,
`secondSumcheckStmtLens.toFunA`), and the lens keeps `t'`:

  `toFunB := fun (stmt, oStmt) ((t', r_x), innerO) => ((t', (r_x, stmt)), oStmt)`.

Everything else (the projection `toFunA`, the oracle routing `simOStmt`/`embedOStmt`, and hence the
faithfulness content) is **identical** to `firstSumcheckStmtLens`/`firstSumcheckOracleLens`, so the
`LiftContextCoherent` and `AppendCoherent` instances and the completeness / rbr-KS transfers mirror
the originals.

## Where the kept target is pinned

* **rbr knowledge soundness** (`firstSumcheckWithTarget_rbrKnowledgeSoundness_honest`): the honest
  transported output relation `firstSumcheckWithTargetRbrRelOut` (the generic
  `Extractor.Lens.Honest.transportedRelOut` at the *new* lens) now genuinely constrains the carried
  target: since the lift keeps `t'`, every compatible inner terminal statement lifting to a given
  outer output must have its `target` equal to the outer statement's carried `t'`, and satisfy the
  terminal sum-check relation at that value. This is made explicit by
  `firstSumcheckWithTargetRbrRelOut_pins_target`. (With the original target-dropping lens the
  transported relation could not constrain the dropped target at all — keeping the pinned terminal
  is the whole point of this brick.)

* **Perfect completeness** (`firstSumcheckWithTarget_perfectCompleteness`): transfers exactly as
  for the original lens, with the R1CS pass-through relations restated at the new output statement
  type (`firstSumcheckWithTargetRelOut` records the carried target but does not pin it).

  HONEST FRONTIER NOTE: additionally *pinning* `t' = ℱ⸨r_x⸩` inside the completeness output
  relation is **not** a plumbing mirror. The `lift_complete` obligation only learns the inner
  terminal claim for the inner run's *output* oracle statement, while the outer relation can only
  mention the outer oracles; bridging them needs the "honest sum-check prover passes the polynomial
  oracle through unchanged" support characterization of the `seqCompose` prover run
  (`compatContext` hands run-support membership, and no such pass-through lemma exists in-tree).
  That is a genuinely new obstruction, deliberately not laundered here; the kept target is pinned
  on the knowledge-soundness side above, which is where the verifier-acceptance content lives.
-/

open MvPolynomial Matrix OracleComp OracleSpec OracleInterface OracleVerifier.LiftContext Sumcheck
open scoped NNReal

namespace Spartan.Spec

/-- The Spartan statement after the first sum-check, **with the sum-check's terminal target kept**:
`(t', (r_x, τ, 𝕩))`. Target first, matching the `R × stmt` convention of `prependRLCTarget` and of
the second sum-check's target-carrying input statement. -/
@[simp]
abbrev Statement.AfterFirstSumcheckWithTarget (R : Type) (pp : Spartan.PublicParams) : Type :=
  R × Statement.AfterFirstSumcheck R pp

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The **target-preserving** value-level oracle-statement lens for the first sum-check. The
projection `toFunA` is identical to `firstSumcheckStmtLens` (constant target `0`, oracle `ℱ`); the
lift `toFunB` additionally keeps the inner terminal target `t'` in the outer output statement. -/
noncomputable def firstSumcheckStmtLensWithTarget :
    OracleStatement.Lens
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) where
  toFunA := fun ⟨⟨τ, 𝕩⟩, oStmt⟩ =>
    ⟨⟨0, Fin.elim0⟩,
     fun _ => ⟨firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt,
               firstSumCheckVirtualPolynomial_mem_restrictDegree pp τ 𝕩 oStmt⟩⟩
  toFunB := fun ⟨stmt, oStmt⟩ ⟨⟨t', r_x⟩, _innerO⟩ => ⟨(t', (r_x, stmt)), oStmt⟩

/-- The **target-preserving** oracle-routing lens for the first sum-check. Identical routing to
`firstSumcheckOracleLens` (same `simOStmt` reconstruction `firstSCEvalFromOracles`, same
input-oracle embedding); only `liftStmt` differs, keeping the terminal target. -/
noncomputable def firstSumcheckOracleLensWithTarget :
    OracleStatement.OracleLens oSpec
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3)
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) where
  toLens := firstSumcheckStmtLensWithTarget pp
  projStmt := fun _ => ⟨0, Fin.elim0⟩
  liftStmt := fun stmt ⟨t', r_x⟩ => (t', (r_x, stmt))
  simOStmt := fun q => match q with
    | ⟨_, point⟩ => ReaderT.mk fun stmt => firstSCEvalFromOracles pp oSpec stmt point
  embedOStmt := Function.Embedding.inl
  hEqOStmt := fun _ => rfl

/-- The **target-preserving** value-level oracle context lens for the first sum-check. -/
noncomputable def firstSumcheckContextLensWithTarget :
    OracleContext.Lens
      (Statement.AfterFirstChallenge R pp) (Statement.AfterFirstSumcheckWithTarget R pp)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m 0)
      (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m))
      (OracleStatement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstSumcheck R pp)
      (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3) (Sumcheck.Spec.OracleStatement R pp.ℓ_m 3)
      Unit Unit Unit Unit where
  stmt := firstSumcheckStmtLensWithTarget pp
  wit := ⟨fun _ => (), fun _ _ => ()⟩

/-- **The target-preserving Spartan first sum-check oracle reduction** (issue #329, Brick B):
the lift of the proven full sum-check oracle reduction onto Spartan's virtual polynomial `ℱ(X)`,
keeping the sum-check's terminal target `t'` in the lifted output statement. -/
noncomputable def firstSumcheckReductionWithTarget :
    OracleReduction oSpec
      (Statement.AfterFirstChallenge R pp) (OracleStatement.AfterFirstChallenge R pp) Unit
      (Statement.AfterFirstSumcheckWithTarget R pp) (OracleStatement.AfterFirstSumcheck R pp) Unit
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m) :=
  (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).liftContext
    (firstSumcheckContextLensWithTarget pp) (firstSumcheckOracleLensWithTarget pp oSpec)

instance instFirstSumcheckWithTargetVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (firstSumcheckReductionWithTarget (R := R) pp oSpec).verifier where
  hCohInl i k h := by
    simp only [firstSumcheckReductionWithTarget, OracleVerifier.liftContext,
      Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [firstSumcheckReductionWithTarget, OracleVerifier.liftContext,
      Function.Embedding.inl_apply] at h
    cases h

/-- **`LiftContextCoherent` instance for the target-preserving first sum-check lens** — the #433
framework gate, mirroring `firstSumcheckCoherent` (the faithfulness content
`firstSCEvalFromOracles_simOracle2` is shared; only the output lift differs, and it is coherent by
construction). -/
@[reducible] noncomputable def firstSumcheckCoherentWithTarget :
    OracleVerifier.LiftContextCoherent (firstSumcheckOracleLensWithTarget pp oSpec)
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier :=
  liftContextCoherent_of (firstSumcheckOracleLensWithTarget pp oSpec) _
    (fun _ _ => rfl)
    (by
      intro os oos transcript q
      obtain ⟨τ, 𝕩⟩ := os
      obtain ⟨idx, point⟩ := q
      refine (firstSCEvalFromOracles_simOracle2 pp oSpec oos transcript.messages ⟨τ, 𝕩⟩
        point).trans ?_
      simp only [firstSumcheckOracleLensWithTarget, firstSumcheckStmtLensWithTarget,
        OracleStatement.Lens.proj, OracleInterface.simOracle2, QueryImpl.addLift,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply]
      rfl)
    (by
      intro os oos transcript so
      obtain ⟨τ, 𝕩⟩ := os
      obtain ⟨t', r_x⟩ := so
      simp [firstSumcheckOracleLensWithTarget, firstSumcheckStmtLensWithTarget,
        OracleStatement.Lens.lift, OracleStatement.Lens.proj])

/-! ## Perfect completeness at the target-preserving endpoint -/

/-- **Outer input relation** of the target-preserving first sum-check phase (identical to
`firstSumcheckRelIn`; restated to keep this module's import cone clean): the R1CS instance is
satisfied. -/
def firstSumcheckWithTargetRelIn :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **Outer output relation** of the target-preserving first sum-check phase: the same R1CS
satisfiability, carried through the sum-check. The output statement `(t', (r_x, τ, 𝕩))` now
*records* the sum-check terminal target `t'` (the `.1.1.1` component); the matrix/witness oracles
and public input `𝕩` (now the `.1.1.2.2.2` component) are unchanged.

The carried `t'` is *pinned* by the knowledge-soundness side
(`firstSumcheckWithTargetRbrRelOut_pins_target`); see the module docstring for why pinning it
inside this completeness relation is a genuinely new (non-plumbing) obstruction. -/
def firstSumcheckWithTargetRelOut :
    Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **`OracleContext.Lens.IsComplete` for the target-preserving first sum-check lens.**
`proj_complete` is exactly `firstSumcheck_proj_mem_relationRound` (shared with the original lens,
since the projection is identical); `lift_complete` is the R1CS pass-through (the lift records
`(t', r_x)` but leaves matrices/witness/public input untouched). -/
instance firstSumcheckWithTargetLensComplete :
    (firstSumcheckContextLensWithTarget pp).toContext.IsComplete
      (firstSumcheckWithTargetRelIn pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckWithTargetRelOut pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLensWithTarget pp).toContext) where
  proj_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstSumcheckWithTargetRelIn, Set.mem_setOf_eq] at hRelIn
    exact firstSumcheck_proj_mem_relationRound pp τ 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_x⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstSumcheckWithTargetRelIn, Set.mem_setOf_eq] at hRelIn
    simpa only [firstSumcheckWithTargetRelOut, Set.mem_setOf_eq] using hRelIn

/-- **Target-preserving first sum-check phase perfect completeness**, given the inner multi-round
sum-check perfect completeness `h_inner`. Mirrors `firstSumcheck_perfectCompleteness` with the
target-preserving lens and coherence instance. -/
theorem firstSumcheckWithTarget_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))) :
    (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (firstSumcheckWithTargetRelIn (R := R) pp) (firstSumcheckWithTargetRelOut (R := R) pp) := by
  haveI := firstSumcheckCoherentWithTarget (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec)
    (lens := firstSumcheckContextLensWithTarget pp)
    (stmtLens := firstSumcheckOracleLensWithTarget pp oSpec)
    (outerRelIn := firstSumcheckWithTargetRelIn (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
    (outerRelOut := firstSumcheckWithTargetRelOut (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    rfl h_inner

/-- **Target-preserving first sum-check phase perfect completeness, UNCONDITIONAL** modulo only the
honest execution-model data facts `hInit`/`hImplSupp`: the inner completeness is discharged by the
bridge-free `Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`. -/
theorem firstSumcheckWithTarget_perfectCompleteness_unconditional
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [Inhabited R] [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (firstSumcheckWithTargetRelIn (R := R) pp) (firstSumcheckWithTargetRelOut (R := R) pp) :=
  firstSumcheckWithTarget_perfectCompleteness pp oSpec
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional hInit hImplSupp)

/-! ## Round-by-round knowledge soundness at the target-preserving endpoint -/

/-- Sum-check round statements are inhabited (zero target, zero challenges). -/
local instance firstSumcheckWithTarget_instInhabitedStatementRound {n : ℕ} {i : Fin (n + 1)} :
    Inhabited (Sumcheck.Spec.StatementRound R n i) :=
  ⟨⟨0, fun _ => 0⟩⟩

/-- Sum-check oracle statements are inhabited (the zero polynomial). -/
noncomputable local instance firstSumcheckWithTarget_instInhabitedOracleStatement
    {n deg : ℕ} {i : Unit} :
    Inhabited (Sumcheck.Spec.OracleStatement R n deg i) :=
  ⟨⟨0, by simp⟩⟩

/-- Honest local input relation for the target-preserving first sum-check RBR-KS leaf: the inner
round-0 sum-check claim, pulled back through the target-preserving lens. (The projection is
identical to `firstSumcheckOracleLens`'s, so this relation coincides with
`firstSumcheckRbrRelIn`.) -/
abbrev firstSumcheckWithTargetRbrRelIn :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  Extractor.Lens.Honest.pullbackRelIn (firstSumcheckOracleLensWithTarget pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))

/-- Honest local output relation for the target-preserving first sum-check RBR-KS leaf: the inner
terminal sum-check claim transported back through the target-preserving lens. Because the lift
**keeps** the terminal target, this relation genuinely pins the outer statement's carried `t'`
(see `firstSumcheckWithTargetRbrRelOut_pins_target`), unlike the target-dropping
`firstSumcheckRbrRelOut`. -/
abbrev firstSumcheckWithTargetRbrRelOut :
    Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  Extractor.Lens.Honest.transportedRelOut (firstSumcheckOracleLensWithTarget pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
      |>.compatStatement (firstSumcheckOracleLensWithTarget pp oSpec).toLens)

/-- **The kept target is pinned.** Membership in the target-preserving transported output relation
pins the outer statement's carried target `y.1.1.1`: every compatible inner terminal statement
`sOut` lifting to `y.1` has `sOut.1.target = y.1.1.1` *and* satisfies the terminal sum-check
relation (the remaining-cube sum of its polynomial at its challenges equals that target). With the
original target-dropping lens, no analogous constraint on the terminal value is expressible at the
outer output — keeping the pinned terminal is the content of this brick. -/
theorem firstSumcheckWithTargetRbrRelOut_pins_target
    (y : (Statement.AfterFirstSumcheckWithTarget R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)
    (hy : y ∈ firstSumcheckWithTargetRbrRelOut pp oSpec)
    (sIn : Statement.AfterFirstChallenge R pp ×
      (∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (sOut : Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m) ×
      (∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    (hCompat : (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m
        oSpec).verifier.toVerifier.compatStatement
        (firstSumcheckOracleLensWithTarget pp oSpec).toLens sIn sOut)
    (hLift : (firstSumcheckOracleLensWithTarget pp oSpec).toLens.lift sIn sOut = y.1) :
    sOut.1.target = y.1.1.1 ∧
      (sOut, ()) ∈ Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R)
        (Fin.last pp.ℓ_m) := by
  refine ⟨?_, hy sIn sOut hCompat hLift⟩
  obtain ⟨stmt, oStmt⟩ := sIn
  obtain ⟨⟨t_out, r_x⟩, oStmt'⟩ := sOut
  rw [← hLift]
  rfl

set_option linter.unusedFintypeInType false in
/-- **The target-preserving first sum-check RBR-KS leaf** over the honest transported relation
contract, reduced to the inner generic multi-round sum-check RBR-KS theorem. Mirrors
`firstSumcheck_rbrKnowledgeSoundness_honest` at the target-preserving lens. -/
theorem firstSumcheckWithTarget_rbrKnowledgeSoundness_honest
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rbrKnowledgeError : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
        |>.rbrKnowledgeSoundness init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
        rbrKnowledgeError) :
    (firstSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckWithTargetRbrRelIn pp oSpec)
      (firstSumcheckWithTargetRbrRelOut pp oSpec)
      rbrKnowledgeError := by
  haveI := firstSumcheckCoherentWithTarget (R := R) pp oSpec
  letI : Extractor.Lens.IsKnowledgeSound
      (firstSumcheckWithTargetRbrRelIn pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckWithTargetRbrRelOut pp oSpec)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
        |>.compatStatement (firstSumcheckOracleLensWithTarget pp oSpec).toLens)
      (fun _ _ => True)
      ⟨(firstSumcheckOracleLensWithTarget pp oSpec).toLens, Witness.InvLens.trivial⟩ :=
    Extractor.Lens.Honest.honestLensKS (firstSumcheckOracleLensWithTarget pp oSpec).toLens
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier
        |>.compatStatement (firstSumcheckOracleLensWithTarget pp oSpec).toLens)
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (V := (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier)
    (stmtLens := firstSumcheckOracleLensWithTarget pp oSpec)
    (witLens := Witness.InvLens.trivial)
    h_inner

set_option linter.unusedFintypeInType false in
/-- **The target-preserving first sum-check RBR-KS leaf, with the generic multi-round sum-check
oracle RBR-KS theorem plugged in** (per-round error `3/|R|`). Mirrors
`firstSumcheck_rbrKnowledgeSoundness_honest_full` at the target-preserving lens. -/
theorem firstSumcheckWithTarget_rbrKnowledgeSoundness_honest_full [Inhabited R]
    {σ : Type} [Subsingleton σ] {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (firstSumcheckReductionWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (firstSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
      (fun _ => (3 : ℝ≥0) / (Fintype.card R)) :=
  firstSumcheckWithTarget_rbrKnowledgeSoundness_honest (R := R) pp oSpec
    (fun _ => (3 : ℝ≥0) / (Fintype.card R))
    (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      (R := R) (deg := 3) (D := boolEmbedding R) (n := pp.ℓ_m)
      (oSpec := oSpec) (init := init) (impl := impl) hInit hInitNF)

#print axioms firstSumcheckReductionWithTarget
#print axioms firstSumcheckWithTargetRbrRelOut_pins_target
#print axioms firstSumcheckWithTarget_perfectCompleteness
#print axioms firstSumcheckWithTarget_perfectCompleteness_unconditional
#print axioms firstSumcheckWithTarget_rbrKnowledgeSoundness_honest
#print axioms firstSumcheckWithTarget_rbrKnowledgeSoundness_honest_full

end Spartan.Spec
