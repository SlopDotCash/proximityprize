/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.FirstSumcheckRelComplete
import ArkLib.ProofSystem.Spartan.SumcheckPhaseRbr
import ArkLib.OracleReduction.LiftContext.HonestKnowledgeLens
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle

/-!
# The Spartan first sum-check phase preserves completeness (issue #114)

The Spartan first sum-check oracle reduction (`firstSumcheckReduction`) is the `liftContext` of the
generic multi-round sum-check oracle reduction onto Spartan's virtual polynomial `ℱ`. This module
assembles the **completeness transfer** for that lift:

* `firstSumcheckRelIn` / `firstSumcheckRelOut` — the outer (Spartan-context) input/output relations.
  Both are "the R1CS instance is satisfied" (`R1CS.relation`). The first sum-check adds the challenge
  `r_x` to the statement but leaves the matrices, witness, and public input untouched, so R1CS
  satisfiability is carried through unchanged. `firstSumcheckRelIn` is the output relation of the
  preceding `firstChallenge` phase; `firstSumcheckRelOut` is the input relation of the following
  `sendEvalClaim` phase.

* `firstSumcheckLensComplete` — the `OracleContext.Lens.IsComplete` instance for the first sum-check
  lens. Its `proj_complete` is exactly `firstSumcheck_proj_mem_relationRound` (an honest
  R1CS-satisfying instance projects to a sum-check round-`0` instance whose hypercube sum is the
  target `0`); its `lift_complete` is the R1CS pass-through (the lift only records `r_x`).

* `firstSumcheck_perfectCompleteness` — the phase completeness, obtained from
  `OracleReduction.liftContext_perfectCompleteness` applied to the inner multi-round sum-check
  perfect completeness `h_inner`, the coherence instance `firstSumcheckCoherent` (#433), and
  `firstSumcheckLensComplete`. It is stated taking `h_inner` as a hypothesis: the inner full
  sum-check perfect completeness is the sequential-composition keystone currently being assembled in
  the `OracleReduction/Composition/Sequential` framework layer; once it lands as a closed theorem,
  this transfer becomes unconditional by feeding it in.
-/

open MvPolynomial OracleComp Sumcheck
open scoped NNReal

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Outer input relation of the first sum-check phase.** The R1CS instance is satisfied: the public
input `𝕩` together with the matrix oracles `A, B, C` and the witness oracle `𝕨` satisfy
`(A𝕫)·(B𝕫) = C𝕫`. The first-challenge `τ` (the `.1` component of the statement) is recorded but
irrelevant to satisfiability. This is the output relation of the preceding `firstChallenge` phase. -/
def firstSumcheckRelIn :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **Outer output relation of the first sum-check phase.** The same R1CS satisfiability, carried
through the sum-check: the output statement `(r_x, τ, 𝕩)` adds the sum-check challenge `r_x`, but the
matrix/witness oracles and public input `𝕩` (the `.2.2` component) are unchanged. This is the input
relation of the following `sendEvalClaim` phase. -/
def firstSumcheckRelOut :
    Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **`OracleContext.Lens.IsComplete` for the first sum-check lens.** Completeness is preserved
through the `liftContext` onto `ℱ`:

* `proj_complete`: an R1CS-satisfying Spartan instance projects to a sum-check round-`0` instance
  satisfying `∑_{cube} ℱ(x) = 0` — exactly `firstSumcheck_proj_mem_relationRound`.
* `lift_complete`: the lift carries the matrices/witness/public input unchanged (only `r_x` is
  added), so R1CS satisfiability transfers verbatim from `firstSumcheckRelIn` to
  `firstSumcheckRelOut`. -/
instance firstSumcheckLensComplete :
    (firstSumcheckContextLens pp).toContext.IsComplete
      (firstSumcheckRelIn pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckRelOut pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLens pp).toContext) where
  proj_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstSumcheckRelIn, Set.mem_setOf_eq] at hRelIn
    exact firstSumcheck_proj_mem_relationRound pp τ 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_x⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstSumcheckRelIn, Set.mem_setOf_eq] at hRelIn
    simpa only [firstSumcheckRelOut, Set.mem_setOf_eq] using hRelIn

/-- **First sum-check phase perfect completeness (issue #114).** The Spartan first sum-check oracle
reduction is perfectly complete from `firstSumcheckRelIn` to `firstSumcheckRelOut`, given the inner
multi-round sum-check perfect completeness `h_inner`.

The transfer is `OracleReduction.liftContext_perfectCompleteness` applied with the coherence instance
`firstSumcheckCoherent` (#433), the lens-completeness instance `firstSumcheckLensComplete`, and
`hStmt = rfl` (`firstSumcheckOracleLens.toLens = firstSumcheckContextLens.stmt` by construction).

`h_inner` is the perfect completeness of the generic full sum-check oracle reduction over `ℓ_m`
variables (degree `3`, Boolean domain) — the sequential-composition completeness being assembled in
the framework layer; once it is a closed theorem, this transfer is unconditional. -/
theorem firstSumcheck_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelIn (R := R) pp) (firstSumcheckRelOut (R := R) pp) := by
  haveI := firstSumcheckCoherent (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec)
    (lens := firstSumcheckContextLens pp)
    (stmtLens := firstSumcheckOracleLens pp oSpec)
    (outerRelIn := firstSumcheckRelIn (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
    (outerRelOut := firstSumcheckRelOut (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    rfl h_inner


/-- `StatementRound` is inhabited over a ring: zero target, zero challenges (needed by the
pullback rbr-soundness transport). -/
local instance instInhabitedStatementRoundFirstSC {n : ℕ} {i : Fin (n + 1)} :
    Inhabited (Sumcheck.Spec.StatementRound R n i) :=
  ⟨⟨0, fun _ => 0⟩⟩

/-- The sum-check oracle statement (a degree-restricted polynomial) is inhabited: the zero
polynomial. -/
noncomputable local instance instInhabitedOracleStatementFirstSC {n deg : ℕ} {i : Unit} :
    Inhabited (Sumcheck.Spec.OracleStatement R n deg i) :=
  ⟨⟨0, by simp [MvPolynomial.mem_restrictDegree]⟩⟩

/-- **First sum-check phase round-by-round soundness (issue #114) — honest pullback transport.**

The lifted first sum-check phase inherits the inner sum-check's rbr soundness, with the *pullback*
input language (the inner sum-check claim `∑_cube ℱ = target`, read through the lens projection)
and the canonically *transported* output language, at the same per-round errors.

DESIGN NOTE (replaces the previously-sorried `firstSumcheck_rbrKnowledgeSoundness`): the
knowledge-soundness route via `Extractor.Lens.IsKnowledgeSound` with the R1CS-carrying
`firstSumcheckRelIn` is **provably unusable** — its `lift_knowledgeSound` field demands the FALSE
implication "inner cube-sum claim ⟹ R1CS satisfiability" (with `Unit` witnesses this is a bare
relation implication, and a τ-masked cube-sum identity at a *fixed* τ does not imply the R1CS
instance is satisfied). The honest phase-local security statement is this *soundness* transport on
the claim languages; the R1CS content enters the composed chain at the `FirstChallenge`
(τ-sampling) phase boundary, whose round-by-round error carries the Schwartz–Zippel content, and —
with `Unit` witnesses throughout — composed knowledge soundness for Spartan coincides with composed
soundness over the claim-language chain. -/
theorem firstSumcheck_rbrSoundness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (innerLangIn : Set (Sumcheck.Spec.StatementRound R pp.ℓ_m 0 ×
      ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    (innerLangOut : Set (Sumcheck.Spec.StatementRound R pp.ℓ_m (Fin.last pp.ℓ_m) ×
      ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_m 3 i))
    (rbrSoundnessError : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.rbrSoundness
        init impl innerLangIn innerLangOut rbrSoundnessError) :
    (firstSumcheckReduction pp oSpec).verifier.rbrSoundness init impl
      ((firstSumcheckOracleLens pp oSpec).toLens.proj ⁻¹' innerLangIn)
      ((firstSumcheckOracleLens pp oSpec).toLens.transportedLangOut innerLangOut
        ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R)
            pp.ℓ_m oSpec).verifier.toVerifier.compatStatement
          (firstSumcheckOracleLens pp oSpec).toLens))
      rbrSoundnessError := by
  haveI := firstSumcheckCoherent (R := R) pp oSpec
  exact OracleVerifier.liftContext_rbrSoundness_pullback
    (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier
    (subset_refl _) h_inner

/-- The honest pullback input relation used by the first sum-check rbr knowledge transfer. It says
that the projected inner sum-check round-`0` claim holds. -/
def firstSumcheckHonestRelIn :
    Set (((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit)) :=
  Extractor.Lens.Honest.pullbackRelIn
    (firstSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))

/-- The honest transported output relation used by the first sum-check rbr knowledge transfer. It
is the canonical outer relation induced by the inner final sum-check relation and the first
sum-check lens. -/
def firstSumcheckHonestRelOut :
    Set (((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)) :=
  Extractor.Lens.Honest.transportedRelOut
    (firstSumcheckOracleLens pp oSpec).toLens
    (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    (Verifier.compatStatement (firstSumcheckOracleLens pp oSpec).toLens
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier)

/-- **First sum-check phase round-by-round knowledge soundness (issue #114).** The Spartan lift of
the generic sum-check verifier is rbr knowledge sound on the honest pullback/transported claim
relations. This is the knowledge-sound analogue of `firstSumcheck_rbrSoundness`; it deliberately
uses the sum-check claim relations rather than the R1CS-carrying relations, avoiding the false
single-point implication described above. -/
theorem firstSumcheck_rbrKnowledgeSoundness_honest
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [Inhabited R] [Subsingleton σ]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckHonestRelIn (R := R) pp oSpec)
      (firstSumcheckHonestRelOut (R := R) pp oSpec)
      (fun _ => (3 : ℝ≥0) / (Fintype.card R)) := by
  haveI := firstSumcheckCoherent (R := R) pp oSpec
  change (OracleVerifier.liftContext (firstSumcheckOracleLens pp oSpec)
    (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier).rbrKnowledgeSoundness
      init impl
      (firstSumcheckHonestRelIn (R := R) pp oSpec)
      (firstSumcheckHonestRelOut (R := R) pp oSpec)
      (fun _ => (3 : ℝ≥0) / (Fintype.card R))
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (V := (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier)
    (stmtLens := firstSumcheckOracleLens pp oSpec)
    (witLens := Witness.InvLens.trivial)
    (lensKS := Extractor.Lens.Honest.honestLensKS
      (stmtLens := (firstSumcheckOracleLens pp oSpec).toLens)
      (innerRelIn :=
        Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (innerRelOut :=
        Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      (compatStmt :=
        Verifier.compatStatement (firstSumcheckOracleLens pp oSpec).toLens
          (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).verifier.toVerifier))
    (h := Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
      (R := R) (deg := 3) (D := boolEmbedding R) (n := pp.ℓ_m)
      (oSpec := oSpec) (init := init) (impl := impl) hInit hInitNF)

end Spartan.Spec
