/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeFinal
import ArkLib.ProofSystem.Spartan.ComposedCompletenessWithClaimFinal
import ArkLib.ProofSystem.Spartan.FinalCheckRbrKnowledgeLeaf

/-!
# Composed Spartan RBR knowledge soundness, target-carrying — the WithClaim residuals (issue #114)

This file discharges the three target-carrying composed RBR-KS residuals of
`ToMathlib/SpartanBricks.lean` —

* `composedRbrKnowledgeSoundnessWithClaimStatement` (broad terminal, `Set.univ`),
* `composedRbrKnowledgeSoundnessWithClaimValueRelStatement` (semantic value relation),
* `composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement` (endpoint form),

at the same composition witness as the proven WithClaim completeness apex:
`Rc := (composedPIOP_Rc …).append (prependClaim …)`.

Pipeline:

1. the full composed 8-fold verifier compiles to a *failing-deterministic* verifier
   (`composedPIOP_Rc_toVerifier_isFailingDet`): fold `Verifier.IsFailingDet.append` over the
   seven seams, with the five pure phase witnesses, the two sum-check failing-det witnesses,
   and the identity `finalCheck`;
2. the 0-round `prependClaim` adapter is a pure statement-reshaper, hence perfectly rbr
   knowledge-sound along the carrier-forgetting relation transport
   (`prependClaim_rbrKnowledgeSoundness_carrier`, error `0`);
3. the failing-det **empty-seam** keystone glues the unconditional relation-preserving apex
   (`composedRbrKnowledgeSoundnessPreserving_unconditional`) to the adapter leaf;
4. the truncation combinator converts the terminal relation to each of the three residuals'
   relations, at the **unchanged** error vector — legitimate because the apex error vector
   already pays the proven-forced `err₅ = 1` at the `linearCombination` round.

**Read the error vector before citing this** (same caveat as `ComposedRbrKnowledgeFinal.lean`):
per-round errors are `0 / ℓ_m·|R|⁻¹ / 3·|R|⁻¹ / 0 / 1 / 0 / 2·|R|⁻¹ / 0 / (empty)`. The
knowledge content is the rbr-KS of the prefix up to `linearCombination`. The *tight* WithClaim
statement — `err₅ = O(1/|R|)` via a terminal `CheckClaim` that actually binds the carried
target — is issue #329 and is **not** claimed here: the in-tree `prependClaim` emits the `0`
target slot (the D1 design gap), so the carried target is not yet bound to the second
sum-check endpoint.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ### Step 1 — the composed verifier is failing-deterministic -/

/-- The compiled `prependClaim` verifier is pure: it returns `((0, stmt), oStmt)` (the `0`
target slot; `embed = inl` routes every oracle through). -/
theorem prependClaim_toVerifier_pure :
    (prependClaim (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p _tr => pure ((0, p.1), p.2)⟩ := by
  have h := OracleVerifier.toVerifier_eq_pure_of_collapse
    (prependClaim (R := R) pp oSpec).verifier
    (fun p _tr => (0, p.1))
    (fun stmt oStmt tr => by
      simp only [prependClaim, prependSlot, prependSlotVerifier]
      exact simulateQ_pure _ _)
  rw [h]
  congr 1

/-- **The full composed 8-fold Spartan verifier compiles to a failing-deterministic verifier.**
Fold of `Verifier.IsFailingDet.append` over the seven seams. -/
theorem composedPIOP_Rc_toVerifier_isFailingDet :
    (composedPIOP_Rc (R := R) pp oSpec).verifier.toVerifier.IsFailingDet := by
  obtain ⟨v₁, hv₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨v₂, hv₂⟩ := firstChallenge_toVerifier_pure.{0} (R := R) pp oSpec
  obtain ⟨v₄, hv₄⟩ := sendEvalClaim_toVerifier_pure (R := R) pp oSpec
  obtain ⟨v₅, hv₅⟩ := linearCombination_toVerifier_pure.{0} (R := R) pp oSpec
  have fd₁ := Verifier.IsFailingDet.of_pure _ hv₁
  have fd₂ := Verifier.IsFailingDet.of_pure _ hv₂
  have fd₃ := Spartan.Spec.firstSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  have fd₄ := Verifier.IsFailingDet.of_pure _ hv₄
  have fd₅ := Verifier.IsFailingDet.of_pure _ hv₅
  have fd₆ := prependRLCTarget_toVerifier_isFailingDet (R := R) pp oSpec
  have fd₇ := Spartan.Spec.secondSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  have fd₈ : (finalCheck R pp oSpec).verifier.toVerifier.IsFailingDet := by
    rw [finalCheck_toVerifier_id (R := R) pp oSpec]
    exact Verifier.id_isFailingDet
  show (OracleVerifier.append (oracleReduction.firstMessage R pp oSpec).verifier
    (OracleVerifier.append (oracleReduction.firstChallenge R pp oSpec).verifier
      (OracleVerifier.append (firstSumcheckReduction pp oSpec).verifier
        (OracleVerifier.append (oracleReduction.sendEvalClaim R pp oSpec).verifier
          (OracleVerifier.append (oracleReduction.linearCombination R pp oSpec).verifier
            (OracleVerifier.append (prependRLCTarget pp oSpec).verifier
              (OracleVerifier.append (secondSumcheckReduction pp oSpec).verifier
                (finalCheck R pp oSpec).verifier))))))).toVerifier.IsFailingDet
  rw [OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier,
    OracleReduction.oracleVerifier_append_toVerifier]
  exact fd₁.append (fd₂.append (fd₃.append (fd₄.append (fd₅.append (fd₆.append
    (fd₇.append fd₈))))))

/-! ### Step 2 — the `prependClaim` adapter leaf -/

/-- The carrier relation on the target-carrying terminal context: forget the (unbound, `0`)
target slot and read the second-sum-check transported terminal relation. -/
@[reducible]
def withClaimCarrierRelOut :
    Set (((R × FinalStatement R pp) × ∀ i, FinalOracleStatement R pp i) × Unit) :=
  {x | ((x.1.1.2, x.1.2), ()) ∈ Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec}

/-- **The `prependClaim` adapter leaf**: perfect (error-`0`) rbr knowledge soundness from the
second-sum-check transported terminal relation to its carrier reading. -/
theorem prependClaim_rbrKnowledgeSoundness_carrier
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (prependClaim (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec)
      (withClaimCarrierRelOut pp oSpec) 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [prependClaim_toVerifier_pure (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_zeroRound_pure init impl _ (fun stmtIn h => h)

/-! ### Step 3 — the glued base fact at the appended composition -/

/-- The apex per-round error vector of the composed 8-fold (see
`composedRbrKnowledgeSoundnessPreserving_unconditional`). -/
def composedApexRbrError : (composedPSpec (R := R) pp).ChallengeIdx → ℝ≥0 :=
  composedRbrError pp
    (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
    (fun _ => (3 : ℝ≥0) / (Fintype.card R))
    (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (fun _ => 1)
    (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
    (fun _ => (2 : ℝ≥0) / (Fintype.card R))
    (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)

/-- The apex error vector extended over the trailing 0-round `prependClaim` phase. -/
def composedWithClaimApexError :
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).ChallengeIdx → ℝ≥0 :=
  Sum.elim (composedApexRbrError (R := R) pp)
      (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
    ∘ ChallengeIdx.sumEquiv.symm

/-- The `linearCombination` challenge round inside the with-claim composed spec. -/
def withClaimLinearCombinationChallengeIdx :
    ((composedPSpec (R := R) pp) ++ₚ (!p[] : ProtocolSpec 0)).ChallengeIdx :=
  ChallengeIdx.sumEquiv (.inl (linearCombinationChallengeIdx (R := R) pp))

/-- The extended apex error vector pays `1` at the `linearCombination` round. -/
theorem one_le_composedWithClaimApexError_lc :
    1 ≤ composedWithClaimApexError (R := R) pp
      (withClaimLinearCombinationChallengeIdx (R := R) pp) := by
  simp only [composedWithClaimApexError, withClaimLinearCombinationChallengeIdx,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, composedApexRbrError,
    composedRbrError_linearCombinationChallengeIdx]
  exact le_rfl

/-- **Base fact**: rbr knowledge soundness of the appended with-claim composition, from
`spartanRelIn` to the carrier reading of the second-sum-check terminal relation, at the
extended apex error vector. Empty-seam failing-det keystone over the unconditional apex and
the adapter leaf. -/
theorem composedWithClaim_rbrKnowledgeSoundness_base [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    ((composedPIOP_Rc (R := R) pp oSpec).append
        (prependClaim (R := R) pp oSpec)).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (withClaimCarrierRelOut pp oSpec)
      (composedWithClaimApexError (R := R) pp) := by
  obtain ⟨verify?, hV⟩ := composedPIOP_Rc_toVerifier_isFailingDet (R := R) pp oSpec
  have h₁ := composedRbrKnowledgeSoundnessPreserving_unconditional (R := R) pp oSpec
    (init := init) (impl := impl) hm hn hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
  have h₂ := prependClaim_rbrKnowledgeSoundness_carrier (R := R) pp oSpec
    (init := init) (impl := impl)
  exact OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty
    (composedPIOP_Rc (R := R) pp oSpec).verifier
    (prependClaim (R := R) pp oSpec).verifier
    verify? hV hInit ⟨()⟩ h₁ h₂

/-! ### Step 4 — the three named residuals -/

/-- **`composedRbrKnowledgeSoundnessWithClaimStatement`, discharged** at
`Rc := (composedPIOP_Rc …).append (prependClaim …)` with the extended apex error vector
(`err₅ = 1`; see the module docstring). -/
theorem composedRbrKnowledgeSoundnessWithClaimStatement_proven [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    composedRbrKnowledgeSoundnessWithClaimStatement R pp oSpec
      ((composedPIOP_Rc (R := R) pp oSpec).append (prependClaim (R := R) pp oSpec))
      init impl (composedWithClaimApexError (R := R) pp) := by
  have h := composedWithClaim_rbrKnowledgeSoundness_base (R := R) pp oSpec
    (init := init) (impl := impl) hm hn hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
  unfold composedRbrKnowledgeSoundnessWithClaimStatement
  exact OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error h
    (withClaimLinearCombinationChallengeIdx (R := R) pp)
    (one_le_composedWithClaimApexError_lc (R := R) pp) _

/-- **`composedRbrKnowledgeSoundnessWithClaimValueRelStatement`, discharged** at the same
composition and error vector. -/
theorem composedRbrKnowledgeSoundnessWithClaimValueRelStatement_proven [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    composedRbrKnowledgeSoundnessWithClaimValueRelStatement R pp oSpec
      ((composedPIOP_Rc (R := R) pp oSpec).append (prependClaim (R := R) pp oSpec))
      init impl (composedWithClaimApexError (R := R) pp) := by
  have h := composedWithClaim_rbrKnowledgeSoundness_base (R := R) pp oSpec
    (init := init) (impl := impl) hm hn hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
  unfold composedRbrKnowledgeSoundnessWithClaimValueRelStatement
  exact OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error h
    (withClaimLinearCombinationChallengeIdx (R := R) pp)
    (one_le_composedWithClaimApexError_lc (R := R) pp) _

/-- **`composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement`, discharged** at the
same composition and error vector. -/
theorem composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_proven [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement R pp oSpec
      ((composedPIOP_Rc (R := R) pp oSpec).append (prependClaim (R := R) pp oSpec))
      init impl (composedWithClaimApexError (R := R) pp) := by
  have h := composedWithClaim_rbrKnowledgeSoundness_base (R := R) pp oSpec
    (init := init) (impl := impl) hm hn hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
  unfold composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement
  exact OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error h
    (withClaimLinearCombinationChallengeIdx (R := R) pp)
    (one_le_composedWithClaimApexError_lc (R := R) pp) _

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.prependClaim_toVerifier_pure
#print axioms Spartan.Spec.Bricks.composedPIOP_Rc_toVerifier_isFailingDet
#print axioms Spartan.Spec.Bricks.prependClaim_rbrKnowledgeSoundness_carrier
#print axioms Spartan.Spec.Bricks.composedWithClaim_rbrKnowledgeSoundness_base
#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessWithClaimStatement_proven
#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessWithClaimValueRelStatement_proven
#print axioms
  Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessWithClaimSecondSumcheckEvalStatement_proven
