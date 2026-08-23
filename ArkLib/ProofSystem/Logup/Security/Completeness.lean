/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol

/-!
# LogUp Completeness

Main completeness statement for Protocol 2 of `paper.txt`.

## Proof architecture and the named residual wall

`logupOracleReduction` is *definitionally* the sequential composition
`outerOracleReduction.append sumcheckOracleReduction` (see `logupOracleReduction_eq_append`).
Completeness therefore follows from `OracleReduction.append_completeness`, supplying:

* outer-phase completeness with error `logupCompletenessError F n` (the pole-rejection error,
  whose mathematical content is the genuinely-proven `card_poleSet_le` / `probEvent_pole_le`
  below: a uniformly sampled `x : F` hits a table pole `-t(u)` with probability at most
  `|Hypercube n| / |F|`), and
* embedded-sumcheck completeness with error `0` (the honest sumcheck run is deterministic and
  correct).

Both sub-facts, and the composition lemma `OracleReduction.append_completeness` itself, are blocked
by missing upstream security lemmas introduced *outside* `ArkLib/ProofSystem/Logup/**`, which this
development is not permitted to modify:

* `OracleReduction.append_completeness` currently exposes the sequential-composition completeness
  obligation as an explicit `hAppendCompleteness` hypothesis. This is an honest named residual
  interface, not a hidden `sorryAx`.
* No full generic `Sumcheck.Spec.oracleReduction` completeness theorem exists in-tree. The generic
  single-round sumcheck reduction has `oracleReduction_perfectCompleteness`, but
  `Sumcheck.Spec.oracleReduction` is the `seqCompose` of those rounds and no seq-compose
  completeness theorem is available for this use.
* Lifting the generic sumcheck reduction through `logupSumcheckContextLens` would additionally
  require the lens completeness instance demanded by
  `OracleReduction.liftContext_completeness`.

Consequently `logup_completeness` is closed via the genuine composition skeleton, with a named
residual `Prop` (`SubPhaseCompletenessResidual`) standing for the upstream-blocked
sub-completeness facts. For callers that can discharge only one side at a time,
`Security/SubPhaseSplit.lean` exposes the same residual as `OuterCompletenessResidual` and
`SumcheckCompletenessResidual`. The pole-probability lemmas the outer half relies on are fully
proven.
-/

open scoped NNReal ENNReal

open OracleComp

-- Elaborating the sub-phase completeness statement over the embedded sumcheck `pSpec` is heavy;
-- give the elaborator extra budget.
set_option maxHeartbeats 800000

namespace Logup

section PoleBound

variable (F : Type) [Field F] [Fintype F] [DecidableEq F]
variable (n M : ℕ)

set_option linter.unusedDecidableInType false in
/-- The number of "bad" verifier challenges `x` — those hitting a table pole `-t(u)` on some
hypercube row `u` — is at most `|Hypercube n|` (at most one pole per row).

This is the combinatorial heart of the LogUp completeness error: the honest prover/verifier run is
deterministic and correct *except* when the sampled `x` is one of these poles, and there are at most
`|Hypercube n|` of them. Fully proven (no `sorryAx`). -/
theorem card_poleSet_le (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    (Finset.univ.filter
        (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ Fintype.card (Hypercube n) := by
  classical
  -- Every bad `x` equals `-t(u)` for some `u`, so the bad set embeds into the image of
  -- `u ↦ -t(u)`, which has at most `|Hypercube n|` elements.
  have hsub : (Finset.univ.filter
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)) ⊆
      Finset.univ.image (fun u : Hypercube n => - evalOnHypercube (tableOracle oStmt) u) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨u, hu⟩ := hx
    refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
    linear_combination -hu
  calc (Finset.univ.filter
        (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)).card
      ≤ (Finset.univ.image
          (fun u : Hypercube n => - evalOnHypercube (tableOracle oStmt) u)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Hypercube n)).card := Finset.card_image_le
    _ = Fintype.card (Hypercube n) := by rw [Finset.card_univ]

set_option linter.unusedDecidableInType false in
/-- The probability that a uniformly sampled challenge `x : F` is a table pole is at most
`|Hypercube n| / |F|` — exactly the LogUp completeness error.

Fully proven (no `sorryAx`); this is the probabilistic statement of `card_poleSet_le`. -/
theorem probEvent_pole_le [SampleableType F] (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)
      ≤ (Fintype.card (Hypercube n) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_poleSet_le F n M oStmt) _

end PoleBound

section Completeness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances. Explicitly named (rather than anonymous) so it does not collide with the
identically-typed anonymous `local instance` in `Security/Soundness.lean` when a downstream
module imports both files. -/
local instance instInhabitedFieldLogupCompleteness : Inhabited F := ⟨0⟩

/-- Completeness error forced by the current rejection-based model of the `x` challenge.

Protocol 2 samples `x` from the complement of the table poles. The current verifier samples from
all of `F` and rejects poles, so the intended completeness statement carries this explicit bad-`x`
probability. Once the challenge sampler is modeled as the complement distribution, this should
collapse to perfect completeness.

The numerator `|Hypercube n|` is exactly the pole count bounded by `card_poleSet_le`.
-/
noncomputable def logupCompletenessError (F : Type) [Fintype F] (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Hypercube n) : ℝ≥0) / (Fintype.card F)

omit [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The LogUp completeness error is never zero** (issue #13, dmvt audit defect 2):
`logupCompletenessError F n = |Hypercube n| / |F| = 2^n / |F|`, and both numerator and
denominator are positive for a finite field `F`. Consequently any statement hypothesizing
`logupCompletenessError F n = 0` (the historical "perfect special case" lemmas) is **vacuous**;
those lemmas have been removed rather than restated. -/
theorem logupCompletenessError_ne_zero :
    logupCompletenessError F n ≠ 0 := by
  have hne : Nonempty F := ⟨0⟩
  have h1 : (Fintype.card (Hypercube n) : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Hypercube n)
  have h2 : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  simp only [logupCompletenessError, ne_eq, div_eq_zero_iff, h1, h2, or_self,
    not_false_eq_true]

omit [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The LogUp completeness error is strictly positive (`ℝ≥0` form of
`logupCompletenessError_ne_zero`). -/
theorem logupCompletenessError_pos :
    0 < logupCompletenessError F n :=
  pos_iff_ne_zero.mpr (logupCompletenessError_ne_zero F n)

/-- Paper-shaped form of `probEvent_pole_le`: the outer-phase pole event is bounded by the
same `logupCompletenessError` constant consumed by `OuterCompletenessResidual`.

This is only the probabilistic front door for the outer completeness proof; it does not discharge
the run-unfolding, sumcheck, or append-composition residuals. -/
theorem probEvent_pole_le_logupCompletenessError (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)
      ≤ (logupCompletenessError F n : ℝ≥0∞) := by
  simpa [logupCompletenessError] using (probEvent_pole_le F n M oStmt)

/-- The intermediate relation threaded between the outer LogUp phase and the embedded sumcheck:
the set of intermediate statement-witness pairs whose embedded-sumcheck claim
`logupOuterSumcheckClaim` is true (i.e. zero). This is the completeness twin of the soundness-side
`midLanguage` (`Security/Soundness.lean`): the honest outer phase delivers exactly the zero-claim
that the embedded sumcheck then verifies (`grandSum_identity` /
`honest_helper_sum_zero_of_inputRelation_all`), and completeness of the embedded sumcheck is only
demanded on claim-true intermediate statements.

(Historical note, issue #13: this was previously `Set.univ`, which made the embedded-sumcheck
completeness obligation `SumcheckCompletenessResidual` demand success from *every* intermediate
statement — including junk oracles whose round-`0` claim is nonzero, where the inner sumcheck
verifier rejects. That made the residual unsatisfiable. The corrected relation matches the
soundness-side `midLanguage` fix.) -/
def midRelation : Set ((StmtAfterOuter F n M params ×
    (∀ i, OStmtAfterOuter F n M params i)) × Unit) :=
  { p | logupOuterSumcheckClaim F n M params p.1.1 p.1.2 = 0 }

set_option linter.unusedSectionVars false in
/-- Membership in `midRelation` is exactly the zero LogUp outer sumcheck claim (definitional). -/
@[simp] theorem mem_midRelation_iff
    (p : (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × Unit) :
    p ∈ midRelation F n M params ↔
      logupOuterSumcheckClaim F n M params p.1.1 p.1.2 = 0 :=
  Iff.rfl

/-- The full LogUp oracle reduction is, definitionally, the sequential composition of the outer
phase and the embedded sumcheck phase. This is the structural fact driving the completeness proof
via `OracleReduction.append_completeness`. -/
theorem logupOracleReduction_eq_append :
    logupOracleReduction oSpec F n M params =
      OracleReduction.append (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params) := rfl

/-- The two sub-phase completeness obligations of the LogUp composition, stated as a single named
`Prop` residual (not proved here).

* The outer phase (`outerOracleReduction`) is complete with error `logupCompletenessError F n`: its
  honest run is deterministic and correct except when the sampled `x` is one of the at most
  `|Hypercube n|` table poles (see `probEvent_pole_le`); the verifier's pole-rejection `guard` then
  fails.
* The embedded sumcheck (`sumcheckOracleReduction`) is complete with error `0`.

WALL (upstream security/composition gaps, outside `ArkLib/ProofSystem/Logup/**`, not modifiable
here):

* Outer completeness requires unfolding `Reduction.run (outerOracleReduction …)`. The prover and
  verifier of the outer phase are themselves `sorryAx`-free, and the failure event is exactly the
  pole event bounded by `probEvent_pole_le`. This direction is in principle closable in-tree but is
  not finished here.
* Sumcheck completeness is blocked: `sumcheckOracleReduction` is a `liftContext` of
  `Sumcheck.Spec.oracleReduction`. No full `Sumcheck.Spec` completeness theorem exists in-tree, and
  the lift also needs the corresponding `OracleContext.Lens.IsComplete` instance for
  `logupSumcheckContextLens`.
* The top-level composition step uses `OracleReduction.append_completeness`, whose current API
  carries the append-completeness theorem as an explicit hypothesis instead of hiding it behind an
  incomplete proof.

This is therefore kept as an explicit named residual `Prop` (no `sorry`); the main theorem
`logup_completeness_of_residual` consumes it. -/
def SubPhaseCompletenessResidual : Prop :=
    (outerOracleReduction oSpec F n M params).completeness init impl
        (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) ∧
      (sumcheckOracleReduction oSpec F n M params).completeness init impl
        (midRelation F n M params) outputRelation 0

/-- Main ArkLib completeness theorem for LogUp Protocol 2, **reduced to the named residual**
`SubPhaseCompletenessResidual` through the genuine sequential-composition completeness interface
`OracleReduction.append_completeness` (whose append theorem is an explicit residual hypothesis; see
the module docstring).

The completeness error `logupCompletenessError F n = |Hypercube n| / |F|` is the sum
`logupCompletenessError F n + 0` of the outer pole-rejection error and the (perfect) sumcheck
error. This reduction's own body contains no `sorry`. -/
theorem logup_completeness_of_residual
    (h : SubPhaseCompletenessResidual oSpec F n M params init impl)
    (hAppendCompleteness :
      (outerOracleReduction oSpec F n M params).appendCompletenessResidual
        (sumcheckOracleReduction oSpec F n M params) h.1 h.2) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  obtain ⟨hOuter, hSum⟩ := h
  -- `logupOracleReduction` is definitionally `append outerOracleReduction sumcheckOracleReduction`
  -- (`logupOracleReduction_eq_append`), so the composed completeness fact unifies with the goal up
  -- to `logupCompletenessError F n + 0 = logupCompletenessError F n`. `OracleReduction.append_completeness`
  -- now carries the sequential-composition completeness fact as the explicit residual hypothesis
  -- `hAppendCompleteness` (mirroring `append_soundness`'s `hAppendSoundness`), which we thread through
  -- (bridging the `+ 0`); the body still contains no `sorry`.
  have hc := OracleReduction.append_completeness.{0, 0}
    (rel₂ := midRelation F n M params)
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    hOuter hSum
    hAppendCompleteness
  simpa only [add_zero] using hc

end Completeness

end Logup
