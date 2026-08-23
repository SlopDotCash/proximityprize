/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToVCVio.OracleComp.RandomOracleEagerTableDep
import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Eager challenge-table sampling for the Fiat-Shamir challenge oracle (#116)

The state-restoration / Fiat-Shamir challenge oracle `fsChallengeOracle Statement pSpec` has a
*dependent* range — the response to a query keyed by challenge round `i` lives in
`pSpec.Challenge i`. This file supplies the finiteness/decidability/sampleability instances for that
oracle (its domain is the finite sigma `Σ i : ChallengeIdx, Statement × MessagesUpTo`, its responses
are the finite sampleable challenge types) and the full dependent answer-table type
`(q : Domain) → Range q`, then specializes the dependent lazy-vs-eager equivalence
`OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep` to it.

The resulting `fsChallenge_lazy_eq_eager` says: running any computation under the lazy Fiat-Shamir
random oracle (uniform-on-first-query, cached) from the empty cache has the same output distribution
as pre-sampling a uniform full challenge table and evaluating deterministically against it. This is
the form in which the honest Fiat-Shamir prover and verifier read the *same* sampled challenge table
(so honest transcripts verify), which is needed to couple the Fiat-Shamir honest-transcript
distribution to the interactive one (the remaining `coupling` kernel of the basic-FS HVZK transfer).

The key bridge is `take`-based: `(pSpec⟦:k⟧).Message i` is definitionally `pSpec.«Type»` at the
embedded index, so the ambient `VCVCompatible (pSpec.Message _)` instances transport to the
truncated protocol via `MessageIdxUpTo.eq_MessageIdx`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-! ### Finiteness of the truncated-protocol messages and the Fiat-Shamir oracle domain -/

/-- A message of a truncated protocol `pSpec⟦:k⟧` is, definitionally, `pSpec.«Type»` at the embedded
index; finiteness transports from the ambient `VCVCompatible (pSpec.Message _)`. -/
instance messageUpToFinite (k : Fin (n + 1)) (i : pSpec.MessageIdxUpTo k) :
    Finite (pSpec.MessageUpTo k i) := by
  show Finite (pSpec.«Type» (i.val.castLE (by omega : k.val ≤ n)))
  exact (inferInstance : Finite (pSpec.Message ⟨i.val.castLE (by omega), i.2⟩))

/-- Decidable equality of a truncated-protocol message, transported from the ambient instances. -/
instance messageUpToDecEq (k : Fin (n + 1)) (i : pSpec.MessageIdxUpTo k) :
    DecidableEq (pSpec.MessageUpTo k i) := by
  show DecidableEq (pSpec.«Type» (i.val.castLE (by omega : k.val ≤ n)))
  exact (inferInstance : DecidableEq (pSpec.Message ⟨i.val.castLE (by omega), i.2⟩))

instance messagesUpToFinite (k : Fin (n + 1)) : Finite (pSpec.MessagesUpTo k) := by
  unfold ProtocolSpec.MessagesUpTo; infer_instance

instance messagesUpToDecEq (k : Fin (n + 1)) : DecidableEq (pSpec.MessagesUpTo k) := by
  unfold ProtocolSpec.MessagesUpTo; infer_instance

instance fsDomainFinite : Finite (fsChallengeOracle StmtIn pSpec).Domain := by
  show Finite ((i : pSpec.ChallengeIdx) × (StmtIn × pSpec.MessagesUpTo i.1.castSucc))
  infer_instance

instance fsDomainDecEq : DecidableEq (fsChallengeOracle StmtIn pSpec).Domain := by
  show DecidableEq ((i : pSpec.ChallengeIdx) × (StmtIn × pSpec.MessagesUpTo i.1.castSucc))
  infer_instance

noncomputable instance fsDomainFintype : Fintype (fsChallengeOracle StmtIn pSpec).Domain := by
  classical exact Fintype.ofFinite _

/-! ### Range instances of the Fiat-Shamir challenge oracle (responses are challenge types) -/

instance fsRangeFintype : ∀ q, Fintype ((fsChallengeOracle StmtIn pSpec).Range q) := fun ⟨i, _⟩ =>
  (inferInstance : Fintype (pSpec.Challenge i))

instance fsRangeNonempty : ∀ q, Nonempty ((fsChallengeOracle StmtIn pSpec).Range q) := fun ⟨i, _⟩ =>
  (inferInstance : Nonempty (pSpec.Challenge i))

instance fsRangeSampleable : ∀ q, SampleableType ((fsChallengeOracle StmtIn pSpec).Range q) :=
  fun ⟨i, _⟩ => (inferInstance : SampleableType (pSpec.Challenge i))

/-- The full dependent Fiat-Shamir challenge table `(q : Domain) → Range q` is sampleable: its
domain is finite and each response type is a finite nonempty sampleable challenge type. -/
noncomputable instance fsTableSampleable :
    SampleableType ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := by
  have _ftF : Finite ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := inferInstance
  have _nt : Nonempty ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := ⟨fun q => (fsRangeNonempty q).some⟩
  classical
  have _ftFin : Fintype ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := Fintype.ofFinite _
  exact SampleableType.ofFintype _

/-! ### Lazy = eager challenge-table sampling for the Fiat-Shamir oracle -/

set_option linter.unusedSectionVars false in
/-- **Lazy Fiat-Shamir random oracle equals eager challenge-table sampling.**

Running any `OracleComp (fsChallengeOracle StmtIn pSpec) α` under the lazy random oracle
(uniform-on-first-query with caching) from the empty cache has the same output distribution as:
sample a uniform full challenge table `g : (q : Domain) → Range q` once, then evaluate the
computation deterministically against `g`. Specialization of
`OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep` to the Fiat-Shamir
challenge oracle. -/
theorem fsChallenge_lazy_eq_eager {α : Type}
    (oa : OracleComp (fsChallengeOracle StmtIn pSpec) α) :
    evalDist ((simulateQ randomOracle oa).run' ∅) =
      evalDist (do
        let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
          (fsChallengeOracle StmtIn pSpec).Range q)
        pure (evalWithAnswerFn (QueryImpl.ofFn g) oa)) :=
  OracleComp.evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTableDep oa

end Reduction

#print axioms Reduction.fsChallenge_lazy_eq_eager
