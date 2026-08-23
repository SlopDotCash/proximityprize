/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.PinnedCompleteness
import ArkLib.ProofSystem.Spartan.FirstSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.TightFinalLeaf

/-!
# Enriched carried-first-sum-check completeness (issue #329, B7 transfer)

The completeness of the target-preserving first sum-check **with the carried terminal pinned**:
the honest output relation records `e₁ = eval r_x F̂` — the direct terminal identity that the
tight chain's binding relations consume — not just the R1CS pass-through of the weak
`firstSumcheckWithTargetRelOut`.

**The per-`P` instance trick.** The completeness lift transfer
(`OracleReduction.liftContext_perfectCompleteness`) needs a *fixed* inner relation pair, while
the pinned inner relations (`relationRoundPinned P`, `PinnedCompleteness.lean`) depend on the
outer input through its virtual polynomial. The reconciliation: restrict the outer input
relation to the fiber of each fixed `P`
(`firstSumcheckWithTargetRelInAt P := relIn ∩ {x | virtual oracle of x = P}`); on each fiber the
pinned relations are fixed, the lens-completeness instance is legitimate (`proj_complete`
produces the pin from the fiber equation; `lift_complete` converts the pinned terminal back
through `relationRound_last_iff_deg`), and perfect completeness is a pointwise (per-input)
statement, so the fibers reassemble into the full input relation.
-/

open OracleComp OracleSpec ProtocolSpec MvPolynomial
open scoped NNReal

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Inhabited R] (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The first-sum-check virtual polynomial of an outer input, as the inner sum-check oracle
statement (the value `firstSumcheckOracleLensWithTarget`'s projection supplies). -/
noncomputable def firstSumcheckVirtualOracle
    (x : Statement.AfterFirstChallenge R pp ×
      (∀ i, OracleStatement.AfterFirstChallenge R pp i)) :
    R⦃≤ 3⦄[X Fin pp.ℓ_m] :=
  ⟨firstSumCheckVirtualPolynomial pp x.1.1 x.1.2 x.2,
   firstSumCheckVirtualPolynomial_mem_restrictDegree pp x.1.1 x.1.2 x.2⟩

/-- The outer input relation restricted to the fiber of a fixed virtual polynomial `P`. -/
def firstSumcheckWithTargetRelInAt (P : R⦃≤ 3⦄[X Fin pp.ℓ_m]) :
    Set ((Statement.AfterFirstChallenge R pp ×
      (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  firstSumcheckWithTargetRelIn pp ∩ { x | firstSumcheckVirtualOracle pp x.1 = P }

/-- **The enriched carried-first output relation**: the R1CS pass-through *and* the direct
terminal identity `e₁ = eval r_x F̂` (the tight chain's `relD`-direct). -/
def firstSumcheckWithTargetRelOutEnriched :
    Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  firstSumcheckWithTargetRelOut pp ∩
  { x | x.1.1.1 = MvPolynomial.eval x.1.1.2.1
      (firstSumCheckVirtualPolynomial pp x.1.1.2.2.1 x.1.1.2.2.2 x.1.2) }

set_option linter.unusedSectionVars false in
/-- **The per-fiber lens-completeness instance**: on the fiber of `P`, the carried lens is
complete from the `P`-restricted outer input relation and the `P`-pinned inner relations to the
enriched outer output relation. -/
@[reducible] def firstSumcheckWithTargetLensCompleteAt (P : R⦃≤ 3⦄[X Fin pp.ℓ_m]) :
    (firstSumcheckContextLensWithTarget pp).toContext.IsComplete
      (firstSumcheckWithTargetRelInAt pp P)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_m 3 (boolEmbedding R) P (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckWithTargetRelOutEnriched pp)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_m 3 (boolEmbedding R) P (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLensWithTarget pp).toContext) where
  proj_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨hRelIn, hP⟩
    refine ⟨?_, ?_⟩
    · exact firstSumcheck_proj_mem_relationRound pp τ 𝕩 oStmt hRelIn
    · show (fun _ => firstSumcheckVirtualOracle pp (⟨τ, 𝕩⟩, oStmt)) = fun _ => P
      rw [hP]
  lift_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_x⟩, innerO⟩ ⟨⟩ _hCompat ⟨hRelIn, hP⟩ ⟨hRel, hPin⟩
    refine ⟨?_, ?_⟩
    · simpa only [firstSumcheckWithTargetRelOut, Set.mem_setOf_eq] using hRelIn
    · -- The pinned terminal collapses to the direct identity at the fiber's polynomial.
      have hpoly : innerO = fun _ => P := hPin
      have hterm : MvPolynomial.eval r_x (innerO ()).val = t_out :=
        (Bricks.relationRound_last_iff_deg (R := R) t_out r_x innerO).mp hRel
      show t_out = MvPolynomial.eval r_x (firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt)
      rw [← hterm, hpoly]
      have : ((P : R⦃≤ 3⦄[X Fin pp.ℓ_m]) : MvPolynomial (Fin pp.ℓ_m) R)
          = firstSumCheckVirtualPolynomial pp τ 𝕩 oStmt := by
        rw [← hP]
        rfl
      rw [this]

section Theorem

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **Enriched carried-first-sum-check perfect completeness (issue #329, B7).** The honest
output satisfies the R1CS pass-through *and* the direct terminal identity `e₁ = eval r_x F̂`,
unconditional modulo the standard honest execution-model facts. Assembled per input through the
fiber of its virtual polynomial. -/
theorem firstSumcheckWithTarget_perfectCompleteness_enriched
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      (firstSumcheckWithTargetRelIn (R := R) pp)
      (firstSumcheckWithTargetRelOutEnriched (R := R) pp) := by
  intro stmtIn witIn hmem
  -- Work on the fiber of this input's virtual polynomial.
  set P : R⦃≤ 3⦄[X Fin pp.ℓ_m] := firstSumcheckVirtualOracle pp stmtIn with hPdef
  letI : (firstSumcheckContextLensWithTarget pp).toContext.IsComplete
      (firstSumcheckWithTargetRelInAt pp P)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_m 3 (boolEmbedding R) P (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckWithTargetRelOutEnriched pp)
      (Sumcheck.Spec.relationRoundPinned R pp.ℓ_m 3 (boolEmbedding R) P (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R)
          pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLensWithTarget pp).toContext) :=
    firstSumcheckWithTargetLensCompleteAt pp oSpec P
  haveI := firstSumcheckCoherentWithTarget (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (lens := firstSumcheckContextLensWithTarget pp)
    (stmtLens := firstSumcheckOracleLensWithTarget pp oSpec)
    (outerRelIn := firstSumcheckWithTargetRelInAt pp P)
    (outerRelOut := firstSumcheckWithTargetRelOutEnriched pp)
    rfl
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_pinned_unconditional P hInit hImplSupp)
    stmtIn witIn ⟨hmem, rfl⟩

end Theorem

end Spartan.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.firstSumcheckWithTargetLensCompleteAt
#print axioms Spartan.Spec.firstSumcheckWithTarget_perfectCompleteness_enriched
