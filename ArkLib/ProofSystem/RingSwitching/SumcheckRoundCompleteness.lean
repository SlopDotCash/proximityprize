/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.SumcheckPhase

set_option linter.unusedSimpArgs false

/-!
# Domain-free ring-switching round completeness

The shared native `iteratedSumcheckOracleReduction_perfectCompleteness_proved` theorem now works
for every nontrivial commutative ring. These historical public wrappers delegate that owner rather
than repeat its execution proof. Prefix fixing and `Fin.snoc` use the canonical sumcheck convention.

The historical `NeverFail init` argument remains accepted by this compatibility surface. Canonical
`ProbComp` is lossless, so this argument does not require a new restriction on its programs.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ProbabilityTheory
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase

noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Domain-free compatibility wrapper of the shared native per-round completeness proof. -/
theorem iteratedSumcheckRound_perfectCompleteness_residual_holds
    (hInit : NeverFail init) :
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) := by
  exact iteratedSumcheckOracleReduction_perfectCompleteness_proved κ L K P ℓ ℓ' h_l aOStmtIn hInit

/-- **Per-round perfect completeness (consumer form).** Every iterated ring-switching sumcheck
round `i : Fin ℓ'` is perfectly complete, from `NeverFail init` alone. This is the residual's
in-file consumer `iteratedSumcheckOracleReduction_perfectCompleteness` fed with the discharge
above. -/
theorem iteratedSumcheckRound_perfectCompleteness
    (hInit : NeverFail init) (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) :=
  iteratedSumcheckOracleReduction_perfectCompleteness
    (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
    (iteratedSumcheckRound_perfectCompleteness_residual_holds
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) hInit) i

end

end RingSwitching.SumcheckPhase

#print axioms RingSwitching.SumcheckPhase.iteratedSumcheckRound_perfectCompleteness_residual_holds
#print axioms RingSwitching.SumcheckPhase.iteratedSumcheckRound_perfectCompleteness
