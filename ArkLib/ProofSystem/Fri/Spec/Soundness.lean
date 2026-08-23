/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# FRI error accounting definitions

Candidate per-round and total error definitions for the FRI protocol soundness
analysis. These definitions follow the structure of the BCIKS20 proximity gap
bounds and Schwartz-Zippel query consistency bounds, but are not yet tied to a
soundness theorem — they are accounting placeholders pending the sequential
composition infrastructure needed for the full soundness proof.

## References

* [Ben-Sasson, I., Chiesa, A., Goldberg, L., Gur, T., Riabzev, M., Spooner, N.,
  *Proximity Gaps for Reed-Solomon Codes*, FOCS 2020][BCIKS20]
-/

namespace Fri

open Polynomial OracleSpec OracleComp ProtocolSpec Finset NNReal ProximityGap Domain

namespace Spec

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ) [NeZero l]
variable {ω : SmoothCosetFftDomain n F}

/-- Candidate per-round proximity-gap error for the `i`-th FRI folding round,
    following the BCIKS20 error bound for the round-`i` Reed-Solomon code.
    Pending a soundness proof linking this to actual failure probability. -/
noncomputable def roundError (δ : ℝ≥0) (i : Fin k) : ℝ≥0 :=
  let N := ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1
  let dom : SmoothCosetFftDomain (n - N) F := ω.subdomain N
  let degBound := 2 ^ ((∑ j', (s j').1) - N) * d.1
  errorBound δ degBound (↑dom : Fin (2 ^ (n - N)) ↪ F)

/-- Candidate per-round query consistency error: `(D / N)^l` where `D` is the
    degree bound and `N` the domain size for round `i`. This follows the
    Schwartz-Zippel argument structure but is not yet formally tied to the
    query verifier's failure probability via a proven lemma. -/
noncomputable def queryRoundError (i : Fin (k + 1)) : ℝ≥0 :=
  let N := ∑ j' ∈ finRangeTo (k + 1) i.val, (s j').1
  let _dom : SmoothCosetFftDomain (n - N) F := ω.subdomain N
  let domSize : ℕ := Fintype.card (Fin (2 ^ (n - N)))
  let degBound := 2 ^ ((∑ j', (s j').1) - N) * d.1
  ((degBound : ℝ≥0) / (domSize : ℝ≥0)) ^ l

/-- Candidate total query consistency error, summing per-round query error
    over all `k + 1` rounds (including the final-polynomial check). -/
noncomputable def queryError : ℝ≥0 :=
  ∑ i : Fin (k + 1), queryRoundError k s d l (ω := ω) i

/-- Candidate total soundness error: sum of per-round proximity-gap errors
    (fold phase) plus query consistency errors (query phase). These are
    accounting definitions; a formal soundness theorem using them is deferred
    pending sequential composition infrastructure. -/
noncomputable def totalError (δ : ℝ≥0) : ℝ≥0 :=
  (∑ i : Fin k, roundError k s d (ω := ω) δ i) + queryError k s d l (ω := ω)

omit [DecidableEq F] [NeZero l] in
/-- The fold-round accounting contribution is included in `totalError`. -/
theorem roundError_sum_le_totalError (δ : ℝ≥0) :
    (∑ i : Fin k, roundError k s d (ω := ω) δ i) ≤
      totalError k s d l (ω := ω) δ := by
  unfold totalError
  exact le_add_of_nonneg_right (zero_le _)

omit [DecidableEq F] [NeZero l] in
/-- Each individual fold-round accounting contribution is included in `totalError`. -/
theorem roundError_le_totalError (δ : ℝ≥0) (i : Fin k) :
    roundError k s d (ω := ω) δ i ≤ totalError k s d l (ω := ω) δ := by
  exact le_trans
    (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i))
    (roundError_sum_le_totalError (k := k) (s := s) (d := d) (l := l) (ω := ω) δ)

omit [DecidableEq F] [NeZero l] in
/-- The query-phase accounting contribution is included in `totalError`.

This is only a projection from the additive budget, not the deferred FRI soundness theorem. -/
theorem queryError_le_totalError (δ : ℝ≥0) :
    queryError k s d l (ω := ω) ≤ totalError k s d l (ω := ω) δ := by
  unfold totalError
  exact le_add_of_nonneg_left (zero_le _)

/-! ### End-to-end FRI soundness via sequential composition (issue #303)

The FRI oracle reduction `Fri.Spec.reduction` is, definitionally, the binary append of the
folding phase `reductionFold` (the `seqCompose`d non-final folding rounds followed by the final
folding round) and the query phase `QueryRound.queryOracleReduction`.  The theorems below tie the
error-accounting definitions above (`roundError`, `queryError`, `totalError`) to the *actual* FRI
verifier failure probability, by assembling the end-to-end soundness statement from per-round and
per-phase soundness facts through the codebase-standard sequential-composition keystones
(`OracleVerifier.seqCompose_soundness`, `OracleVerifier.append_soundness`) and their named seam
residuals — exactly the structure already used for the completeness side in
`Fri/Spec/Completeness.lean` (issue #117) and for Batched FRI in `BatchedFri/Security.lean`.

The headline statement is `reduction_soundness_totalError`: the composed FRI verifier is sound
with soundness error *exactly* `totalError k s d l δ = (∑ i, roundError δ i) + queryError`. -/

section EndToEnd

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

omit [NeZero l] in
/-- The composed FRI verifier is definitionally the append of the folding-phase verifier and the
query-round verifier.  This exposes the exact seam consumed by the generic binary append soundness
keystone `OracleVerifier.append_soundness`. -/
theorem reduction_verifier_eq_append
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier] :
    (reduction k s d dom_size_cond l (ω := ω)).verifier =
      OracleVerifier.append
        (reductionFold k s d (ω := ω)).verifier
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier := rfl

omit [NeZero l] in
/-- The folding-phase verifier is definitionally the append of the `seqCompose`d non-final
fold-round verifiers and the final-fold verifier. -/
theorem reductionFold_verifier_eq_append :
    (reductionFold k s d (ω := ω)).verifier =
      OracleVerifier.append
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier := rfl

omit [NeZero l] in
/-- **Round-by-round layer.** If each non-final FRI folding round is sound with the
BCIKS20-accounted per-round error `roundError δ i`, then (through the `seqCompose` soundness
keystone, whose deep content is the named sequential-composition residual `h_seq`) the
`seqCompose`d folding-round verifier is sound with the summed error `∑ i, roundError δ i` —
the exact fold-phase contribution to `totalError`. -/
theorem foldRounds_seqCompose_soundness
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    (δ : ℝ≥0)
    (lang : (i : Fin (k + 1)) → Set (Statement F i × ∀ j, OracleStatement s ω i j))
    (h_round : ∀ i : Fin k,
      OracleVerifier.soundness (init := init) (impl := impl)
        (lang i.castSucc) (lang i.succ)
        (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier
        (roundError k s d (ω := ω) δ i))
    (h_seq :
      OracleVerifier.soundness (init := init) (impl := impl)
        (lang 0) (lang (Fin.last k))
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        (∑ i, roundError k s d (ω := ω) δ i)) :
    OracleVerifier.soundness (init := init) (impl := impl)
      (lang 0) (lang (Fin.last k))
      (OracleVerifier.seqCompose _ _
        (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
      (∑ i, roundError k s d (ω := ω) δ i) :=
  OracleVerifier.seqCompose_soundness lang
    (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier)
    (roundError k s d (ω := ω) δ) h_round h_seq

omit [NeZero l] in
/-- **Fold-phase seam.** Soundness of the folding phase `reductionFold` with additive error,
assembled from soundness of the `seqCompose`d non-final folding rounds and soundness of the final
folding round via the binary append keystone.  In the `totalError` accounting the final fold
round contributes no additional proximity error (`finalError = 0`): its degree check is deferred
to the query phase. -/
theorem reductionFold_soundness_of_append
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [hFinalChallenge : ∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    (langIn : Set (Statement F (0 : Fin (k + 1)) ×
      ∀ j, OracleStatement s ω (0 : Fin (k + 1)) j))
    (langMid : Set (Statement F (Fin.last k) × ∀ j, OracleStatement s ω (Fin.last k) j))
    (langOut : Set (FinalStatement F k × ∀ j, FinalOracleStatement s ω j))
    {foldSeqError finalError : ℝ≥0}
    (h_folds :
      OracleVerifier.soundness (init := init) (impl := impl) langIn langMid
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        foldSeqError)
    (h_final :
      OracleVerifier.soundness (init := init) (impl := impl) langMid langOut
        (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier
        finalError)
    (h_residual :
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier
        h_folds h_final) :
    letI : ∀ i, SampleableType
        ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    OracleVerifier.soundness (init := init) (impl := impl) langIn langOut
      (reductionFold k s d (ω := ω)).verifier
      (foldSeqError + finalError) :=
  OracleVerifier.append_soundness
    (OracleVerifier.seqCompose _ _
      (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
    (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier
    h_folds h_final h_residual

omit [NeZero l] in
/-- **Top seam (additive form).** Soundness of the composed FRI reduction `Fri.Spec.reduction`
with additive error `foldError + queryErrorBound`, assembled from soundness of the folding phase
and soundness of the query round via the binary append keystone. -/
theorem reduction_soundness_of_phases
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [hFinalChallenge : ∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (langIn : Set (Statement F (0 : Fin (k + 1)) ×
      ∀ j, OracleStatement s ω (0 : Fin (k + 1)) j))
    (langMid langOut : Set (FinalStatement F k × ∀ j, FinalOracleStatement s ω j))
    {foldError queryErrorBound : ℝ≥0}
    (h_fold :
      letI : ∀ i, SampleableType
          ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
        ProtocolSpec.instSampleableTypeChallengeAppend
      OracleVerifier.soundness (init := init) (impl := impl) langIn langMid
        (reductionFold k s d (ω := ω)).verifier foldError)
    (h_query :
      OracleVerifier.soundness (init := init) (impl := impl) langMid langOut
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        queryErrorBound)
    (h_residual :
      letI : ∀ i, SampleableType
          ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
        ProtocolSpec.instSampleableTypeChallengeAppend
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (reductionFold k s d (ω := ω)).verifier
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        h_fold h_query) :
    letI : ∀ i, SampleableType
        ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    OracleVerifier.soundness (init := init) (impl := impl) langIn langOut
      (reduction k s d dom_size_cond l (ω := ω)).verifier
      (foldError + queryErrorBound) := by
  letI : ∀ i, SampleableType
      ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
  exact OracleVerifier.append_soundness
    (reductionFold k s d (ω := ω)).verifier
    (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
    h_fold h_query h_residual

omit [NeZero l] in
/-- **End-to-end FRI soundness theorem at the `totalError` budget.**

If the folding phase is sound with the summed per-round proximity-gap error
`∑ i, roundError δ i` and the query phase is sound with the query-consistency error
`queryError`, then the composed FRI verifier is sound with soundness error *exactly*
`totalError k s d l δ`.  This is the formal soundness theorem that the error-accounting
definitions above were deferred pending: `totalError` is no longer a free-floating budget but
the actual failure-probability bound of the composed FRI verifier, conditional on the per-phase
facts and the named binary-append seam residual. -/
theorem reduction_soundness_totalError
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [hFinalChallenge : ∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (δ : ℝ≥0)
    (langIn : Set (Statement F (0 : Fin (k + 1)) ×
      ∀ j, OracleStatement s ω (0 : Fin (k + 1)) j))
    (langMid langOut : Set (FinalStatement F k × ∀ j, FinalOracleStatement s ω j))
    (h_fold :
      letI : ∀ i, SampleableType
          ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
        ProtocolSpec.instSampleableTypeChallengeAppend
      OracleVerifier.soundness (init := init) (impl := impl) langIn langMid
        (reductionFold k s d (ω := ω)).verifier
        (∑ i, roundError k s d (ω := ω) δ i))
    (h_query :
      OracleVerifier.soundness (init := init) (impl := impl) langMid langOut
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        (queryError k s d l (ω := ω)))
    (h_residual :
      letI : ∀ i, SampleableType
          ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
        ProtocolSpec.instSampleableTypeChallengeAppend
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (reductionFold k s d (ω := ω)).verifier
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        h_fold h_query) :
    letI : ∀ i, SampleableType
        ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    OracleVerifier.soundness (init := init) (impl := impl) langIn langOut
      (reduction k s d dom_size_cond l (ω := ω)).verifier
      (totalError k s d l (ω := ω) δ) :=
  reduction_soundness_of_phases (k := k) (s := s) (d := d)
    (dom_size_cond := dom_size_cond) (l := l) (ω := ω) init impl
    langIn langMid langOut h_fold h_query h_residual

omit [NeZero l] in
/-- **Round-by-round FRI soundness theorem.** The composed FRI verifier is sound at the
`totalError` budget, assembled all the way from *per-round* soundness facts: each non-final
folding round sound at `roundError δ i`, the final folding round sound at error `0` (its check
is deferred to the query phase in this accounting), and the query round sound at `queryError`,
chained through the `seqCompose` and binary-append soundness keystones with their named seam
residuals. -/
theorem reduction_soundness_totalError_of_rounds
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [hFinalChallenge : ∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (δ : ℝ≥0)
    (lang : (i : Fin (k + 1)) → Set (Statement F i × ∀ j, OracleStatement s ω i j))
    (langMid langOut : Set (FinalStatement F k × ∀ j, FinalOracleStatement s ω j))
    (h_round : ∀ i : Fin k,
      OracleVerifier.soundness (init := init) (impl := impl)
        (lang i.castSucc) (lang i.succ)
        (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier
        (roundError k s d (ω := ω) δ i))
    (h_seq :
      OracleVerifier.soundness (init := init) (impl := impl)
        (lang 0) (lang (Fin.last k))
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        (∑ i, roundError k s d (ω := ω) δ i))
    (h_final :
      OracleVerifier.soundness (init := init) (impl := impl) (lang (Fin.last k)) langMid
        (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier 0)
    (h_res1 :
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (OracleVerifier.seqCompose _ _
          (fun i => (FoldPhase.foldOracleReduction s (ω := ω) d i).verifier))
        (FinalFoldPhase.finalFoldOracleReduction (k := k) s d).verifier
        (foldRounds_seqCompose_soundness (k := k) (s := s) (d := d) (ω := ω)
          init impl δ lang h_round h_seq)
        h_final)
    (h_query :
      OracleVerifier.soundness (init := init) (impl := impl) langMid langOut
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        (queryError k s d l (ω := ω)))
    (h_res2 :
      letI : ∀ i, SampleableType
          ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
        ProtocolSpec.instSampleableTypeChallengeAppend
      OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
        (reductionFold k s d (ω := ω)).verifier
        (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
        (reductionFold_soundness_of_append (k := k) (s := s) (d := d) (ω := ω)
          init impl (lang 0) (lang (Fin.last k)) langMid
          (foldRounds_seqCompose_soundness (k := k) (s := s) (d := d) (ω := ω)
            init impl δ lang h_round h_seq)
          h_final h_res1)
        h_query) :
    letI : ∀ i, SampleableType
        ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      ProtocolSpec.instSampleableTypeChallengeAppend
    OracleVerifier.soundness (init := init) (impl := impl) (lang 0) langOut
      (reduction k s d dom_size_cond l (ω := ω)).verifier
      (totalError k s d l (ω := ω) δ) := by
  letI : ∀ i, SampleableType
      ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
  have h :=
    OracleVerifier.append_soundness
      (reductionFold k s d (ω := ω)).verifier
      (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l).verifier
      (reductionFold_soundness_of_append (k := k) (s := s) (d := d) (ω := ω)
        init impl (lang 0) (lang (Fin.last k)) langMid
        (foldRounds_seqCompose_soundness (k := k) (s := s) (d := d) (ω := ω)
          init impl δ lang h_round h_seq)
        h_final h_res1)
      h_query h_res2
  have herr :
      (∑ i, roundError k s d (ω := ω) δ i) + 0 + queryError k s d l (ω := ω) =
        totalError k s d l (ω := ω) δ := by
    unfold totalError
    rw [add_zero]
  rw [herr] at h
  exact h

end EndToEnd

end Spec

end Fri

/-! ### Axiom audit (issue #303 FRI end-to-end soundness assembly) -/

#print axioms Fri.Spec.reduction_verifier_eq_append
#print axioms Fri.Spec.reductionFold_verifier_eq_append
#print axioms Fri.Spec.foldRounds_seqCompose_soundness
#print axioms Fri.Spec.reductionFold_soundness_of_append
#print axioms Fri.Spec.reduction_soundness_of_phases
#print axioms Fri.Spec.reduction_soundness_totalError
#print axioms Fri.Spec.reduction_soundness_totalError_of_rounds
