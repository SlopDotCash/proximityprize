/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterRun
import ArkLib.ProofSystem.Logup.Security.Completeness

/-!
# Verifier-side outer completeness for LogUp Protocol 2 (issue #13)

This file connects the two already-proven halves of the outer LogUp completeness argument:

* the **closed form of the compiled outer verifier** (`Logup.simulateQ_outerVerify_eq`,
  `Security/OuterRun.lean`): the verifier accepts iff the `x`-challenge avoids every table pole, and
* the **pole-probability bound** (`Logup.probEvent_pole_le_logupCompletenessError`,
  `Security/Completeness.lean`): a uniformly sampled `x` hits a pole with probability at most
  `logupCompletenessError F n = |Hypercube n| / |F|`.

Concretely, `outerVerifyAccepts oStmt x` names the verifier's acceptance condition as a predicate on
the `x`-challenge alone, `simulateQ_outerVerify_eq_accepts` repackages the closed form against it,
and `probEvent_outerVerify_reject_le` shows the verifier's *rejection* probability under a uniformly
sampled challenge is bounded by `logupCompletenessError F n`. The verifier's rejection event is
*definitionally* the complement of the pole-avoidance condition, so the bound is exactly the proven
pole bound transported through `not_forall`.

This is the **verifier-side** half of `OuterCompletenessResidual` (`Security/SubPhaseSplit.lean`):
it discharges everything about the outer phase *downstream of the honest prover's challenge sample*.
What remains for the full outer completeness obligation is the prover-run side — unfolding
`Reduction.run (outerOracleReduction …)` to show the honest prover feeds a *uniformly sampled* `x`
into this verifier and never fails for any other reason — which is the `OptionT`/`simulateQ`
run-unfolding wall flagged in `Security/Completeness.lean` (genuinely in-tree closable but not yet
finished). No new axioms: the bridge is the two proven facts plus a classical predicate rewrite.
-/

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

namespace Logup

section OuterAcceptance

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ)
variable (params : ProtocolParams M)

/-- The compiled outer LogUp verifier's **acceptance condition**, as a predicate on the
`x`-challenge alone: `x` must avoid every table pole `-t(u)` on the hypercube. By
`simulateQ_outerVerify_eq` this is exactly the condition under which the verifier returns `pure …`
rather than `failure`. -/
def outerVerifyAccepts (oStmt : ∀ i, OStmtIn F n M i) (x : F) : Prop :=
  ∀ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u ≠ 0

/-- The compiled outer verifier closed form, stated against the named acceptance predicate
`outerVerifyAccepts`. A direct repackaging of `simulateQ_outerVerify_eq`. -/
theorem simulateQ_outerVerify_eq_accepts (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (chal : ∀ i, (outerPSpec F n params).Challenge i)
    (msgs : ∀ i, (outerPSpec F n params).Message i)
    [Decidable (outerVerifyAccepts F n M oStmt (chalX F n M params chal))] :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((outerVerifier oSpec F n M params).verify stmt chal)
      = (if outerVerifyAccepts F n M oStmt (chalX F n M params chal)
          then (pure { xChallenge := chalX F n M params chal,
                       zChallenge := (chalBatch F n M params chal).1,
                       batchingScalars := (chalBatch F n M params chal).2 }
                : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params))
          else failure) := by
  rw [simulateQ_outerVerify_eq]
  exact if_congr Iff.rfl rfl rfl

/-- The verifier-rejection event (the `x`-challenge hits some table pole) is *definitionally* the
complement of `outerVerifyAccepts`, i.e. the pole event of `probEvent_pole_le`. -/
theorem not_outerVerifyAccepts_iff (oStmt : ∀ i, OStmtIn F n M i) (x : F) :
    ¬ outerVerifyAccepts F n M oStmt x
      ↔ ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0 := by
  unfold outerVerifyAccepts
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h hc
  · rintro ⟨u, hu⟩ h
    exact (h u) hu

/-- **Verifier-side outer completeness.** The compiled outer LogUp verifier *rejects* a uniformly
sampled `x`-challenge with probability at most `logupCompletenessError F n = |Hypercube n| / |F|`.

The verifier's rejection event is the pole event, so this is exactly the proven
`probEvent_pole_le_logupCompletenessError` transported through the classical equivalence
`¬(∀ u, … ≠ 0) ↔ (∃ u, … = 0)`. This bounds the only failure source of the outer phase *after* the
honest prover's challenge sample. -/
theorem probEvent_outerVerify_reject_le [SampleableType F] (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ¬ outerVerifyAccepts F n M oStmt x)
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  have hcongr :
      (fun x : F => ¬ outerVerifyAccepts F n M oStmt x)
        = (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0) := by
    funext x
    exact propext (not_outerVerifyAccepts_iff F n M oStmt x)
  rw [hcongr]
  exact probEvent_pole_le_logupCompletenessError F n M oStmt

end OuterAcceptance

end Logup

/- Axiom audit for the verifier-side outer completeness bridge. -/
#print axioms Logup.simulateQ_outerVerify_eq_accepts
#print axioms Logup.not_outerVerifyAccepts_iff
#print axioms Logup.probEvent_outerVerify_reject_le
