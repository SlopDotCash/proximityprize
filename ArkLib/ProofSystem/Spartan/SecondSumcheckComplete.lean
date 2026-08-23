/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckRelIn
import ArkLib.ProofSystem.Spartan.SumcheckPhaseRbr
import ArkLib.ProofSystem.Spartan.SecondSumcheckFaithful
import ArkLib.OracleReduction.LiftContext.HonestKnowledgeLens
import ArkLib.ProofSystem.Sumcheck.Spec.RbrKnowledgeSoundnessOracle

/-!
# The Spartan second sum-check phase preserves completeness (issue #114)

The Spartan second sum-check oracle reduction (`secondSumcheckReduction`) is the `liftContext` of
the generic multi-round sum-check oracle reduction onto Spartan's virtual polynomial `ℳ`. This
module assembles the **completeness transfer** for that lift, the second-phase analogue of
`FirstSumcheckComplete`.

The new ingredient, relative to the first sum-check, is **target reconciliation**: the inner
sum-check target is *not* the constant `0` but the random-linear-combination of the bundled
evaluation claims, which `liftContext`'s `projStmt` cannot compute from the oracles and so is
carried in the outer input statement (the leading `R` of `R × Statement.AfterLinearCombination`).
The outer input relation `secondSumcheckRelIn` therefore pins that carried target to the honest RLC
(`t = ∑ idx, r idx · v_idx`); on that nose the cube-sum identity
(`secondSC_relationRound_zero`) discharges `proj_complete`.

* `secondSumcheckRelIn` — R1CS satisfiability **and** the carried target equals the RLC of the
  eval-claims. `secondSumcheckRelOut` — R1CS satisfiability, carried through (the sum-check adds the
  challenge `r_y` but leaves the matrices/witness/public input unchanged).
* `secondSumcheckLensComplete` — `proj_complete` via `secondSC_relationRound_zero` (rewriting the
  carried target by the RLC equation), `lift_complete` via R1CS pass-through.
* `secondSumcheck_perfectCompleteness` — `OracleReduction.liftContext_perfectCompleteness` with
  `secondSumcheckCoherent` (#433), `secondSumcheckLensComplete`, and the inner multi-round sum-check
  perfect completeness `h_inner` (taken as a hypothesis, as for the first sum-check).
-/

open MvPolynomial OracleComp Sumcheck
open scoped NNReal

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- `StatementRound` is inhabited over a ring: zero target, zero challenges. Needed by the
`liftContext` round-by-round knowledge-soundness transfer machinery. -/
local instance {n : ℕ} {i : Fin (n + 1)} : Inhabited (Sumcheck.Spec.StatementRound R n i) :=
  ⟨⟨0, fun _ => 0⟩⟩

/-- **Outer input relation of the second sum-check phase.** Two conjuncts:
* the R1CS instance is satisfied (public input `𝕩 = stmt.2.2.2`, matrices `A,B,C` and witness `𝕨`
  read from the oracle family at `.inr (.inl idx)` / `.inr (.inr 0)`);
* **target reconciliation** — the carried target `t` equals the honest random-linear-combination
  `∑ idx, r idx · v_idx` of the bundled eval-claims (`r = stmt.1`, `v = evalClaimValue`). -/
def secondSumcheckRelIn :
    Set (((R × Statement.AfterLinearCombination R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ x.1.1.1 = ∑ idx, x.1.1.2.1 idx *
            evalClaimValue R pp x.1.1.2.2 (fun i => x.1.2 (.inr i)) idx }

/-- **Outer output relation of the second sum-check phase.** R1CS satisfiability carried through:
the output statement `(r_y, stmt)` adds the sum-check challenge `r_y`, but the matrix/witness
oracles and public input `𝕩 = stmt.2.2.2` are unchanged. -/
def secondSumcheckRelOut :
    Set ((Statement.AfterSecondSumcheck R pp ×
        (∀ i, OracleStatement.AfterSecondSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

/-- **`OracleContext.Lens.IsComplete` for the second sum-check lens.**

* `proj_complete`: with the carried target equal to the RLC (the second conjunct of
  `secondSumcheckRelIn`), the projected sum-check round-`0` instance satisfies `∑_{cube} ℳ = target`
  — exactly `secondSC_relationRound_zero` after rewriting the target.
* `lift_complete`: the lift carries the matrices/witness/public input unchanged, so R1CS
  satisfiability (the first conjunct) transfers verbatim to `secondSumcheckRelOut`. -/
instance secondSumcheckLensComplete :
    (secondSumcheckContextLens pp).toContext.IsComplete
      (secondSumcheckRelIn pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckRelOut pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.compatContext
        (secondSumcheckContextLens pp).toContext) where
  proj_complete := by
    rintro ⟨⟨t, stmt⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [secondSumcheckRelIn, Set.mem_setOf_eq] at hRelIn
    obtain ⟨_hR1CS, ht⟩ := hRelIn
    rw [ht]
    exact Bricks.secondSC_relationRound_zero pp stmt oStmt
      ⟨secondSumCheckVirtualPolynomial R pp stmt oStmt, secondSCVP_mem_restrictDegree pp stmt oStmt⟩
      rfl
  lift_complete := by
    rintro ⟨⟨t, stmt⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_y⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [secondSumcheckRelIn, Set.mem_setOf_eq] at hRelIn
    simpa only [secondSumcheckRelOut, Set.mem_setOf_eq] using hRelIn.1

/-- **Second sum-check phase perfect completeness (issue #114).** The Spartan second sum-check
oracle reduction is perfectly complete from `secondSumcheckRelIn` to `secondSumcheckRelOut`, given
the inner multi-round sum-check perfect completeness `h_inner`.

The transfer is `OracleReduction.liftContext_perfectCompleteness` with the coherence instance
`secondSumcheckCoherent` (#433), the lens-completeness instance `secondSumcheckLensComplete`, and
`hStmt = rfl`. As for the first sum-check, `h_inner` is the perfect completeness of the generic full
sum-check oracle reduction (over `ℓ_n` variables, degree `2`, Boolean domain). -/
theorem secondSumcheck_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))) :
    (secondSumcheckReduction pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelIn (R := R) pp) (secondSumcheckRelOut (R := R) pp) := by
  haveI := secondSumcheckCoherent (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec)
    (lens := secondSumcheckContextLens pp)
    (stmtLens := secondSumcheckOracleLens pp oSpec)
    (outerRelIn := secondSumcheckRelIn (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
    (outerRelOut := secondSumcheckRelOut (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
    rfl h_inner


/-- **Second sum-check phase round-by-round soundness (issue #114) — honest pullback transport.**

The lifted second sum-check phase inherits the inner sum-check's rbr soundness, with the *pullback*
input language (the inner claim `∑_cube ℳ = target` read through the lens projection — which, by
`secondSC_relationRound_zero`, pins the carried target to the honest random linear combination) and
the canonically *transported* output language, at the same per-round errors.

DESIGN NOTE (replaces the previously-sorried `secondSumcheck_rbrKnowledgeSoundness`): the
knowledge-soundness route via `Extractor.Lens.IsKnowledgeSound` with the R1CS-carrying
`secondSumcheckRelIn` is **provably unusable** — its `lift_knowledgeSound` field demands the FALSE
implication "inner cube-sum claim ⟹ R1CS satisfiability" (a bare relation implication with `Unit`
witnesses). The honest phase-local security statement is this *soundness* transport on the claim
languages; with `Unit` witnesses throughout the Spartan PIOP, composed knowledge soundness
coincides with composed soundness over the claim-language chain, with the R1CS content entering at
the `FirstChallenge` (τ-sampling) phase boundary. -/
theorem secondSumcheck_rbrSoundness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (innerLangIn : Set (Sumcheck.Spec.StatementRound R pp.ℓ_n 0 ×
      ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i))
    (innerLangOut : Set (Sumcheck.Spec.StatementRound R pp.ℓ_n (Fin.last pp.ℓ_n) ×
      ∀ i, Sumcheck.Spec.OracleStatement R pp.ℓ_n 2 i))
    (rbrSoundnessError : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0)
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier.rbrSoundness
        init impl innerLangIn innerLangOut rbrSoundnessError) :
    (secondSumcheckReduction pp oSpec).verifier.rbrSoundness init impl
      ((secondSumcheckOracleLens pp oSpec).toLens.proj ⁻¹' innerLangIn)
      ((secondSumcheckOracleLens pp oSpec).toLens.transportedLangOut innerLangOut
        ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R)
            pp.ℓ_n oSpec).verifier.toVerifier.compatStatement
          (secondSumcheckOracleLens pp oSpec).toLens))
      rbrSoundnessError := by
  haveI := secondSumcheckCoherent (R := R) pp oSpec
  exact OracleVerifier.liftContext_rbrSoundness_pullback
    (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier
    (subset_refl _) h_inner

/- The honest pullback/transported rbr-KS relations and the second sum-check
rbr knowledge-soundness leaf were moved to `SumcheckKnowledgeLeaves.lean`
(`secondSumcheckRbrRelIn`/`secondSumcheckRbrRelOut`/`secondSumcheck_rbrKnowledgeSoundness_honest`);
the copies that lived here were deleted to resolve the duplicate-declaration clash (#329). -/

end Spartan.Spec
