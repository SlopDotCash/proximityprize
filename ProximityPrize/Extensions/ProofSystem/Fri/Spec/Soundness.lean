/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Fri.Spec.Soundness

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ProximityPrize.Extensions.ProofSystem.Fri.Spec.General
import ProximityPrize.Extensions.Data.Domain.CosetFftDomain.Subdomain
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ProximityPrize.Extensions.OracleReduction.Security.Basic
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.General

/-!
# FRI error accounting definitions

Candidate per-round and total error definitions for the FRI protocol soundness
analysis. These definitions follow the structure of the BCIKS20 proximity gap
bounds and Schwartz-Zippel query consistency bounds, but are not yet tied to a
proved soundness theorem — they are accounting placeholders. The `EndToEnd`
section below only adds *conditional* assembly theorems whose conclusions are
supplied as hypotheses (see that section's scope note). The proved FRI results are
the canonical `Fri.Spec.soundness` and `Fri.Spec.rbr_soundness` in
`ArkLib/ProofSystem/Fri/Spec/Soundness.lean`, at their own errors `soundnessError`
and `challengeError`, not at the `totalError` defined here.

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
  exact le_add_of_nonneg_right (by positivity)

omit [DecidableEq F] [NeZero l] in
/-- Each individual fold-round accounting contribution is included in `totalError`. -/
theorem roundError_le_totalError (δ : ℝ≥0) (i : Fin k) :
    roundError k s d (ω := ω) δ i ≤ totalError k s d l (ω := ω) δ := by
  exact le_trans
    (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i))
    (roundError_sum_le_totalError (k := k) (s := s) (d := d) (l := l) (ω := ω) δ)

omit [DecidableEq F] [NeZero l] in
/-- The query-phase accounting contribution is included in `totalError`.

This is only a projection from the additive budget, not the deferred FRI soundness theorem. -/
theorem queryError_le_totalError (δ : ℝ≥0) :
    queryError k s d l (ω := ω) ≤ totalError k s d l (ω := ω) δ := by
  unfold totalError
  exact le_add_of_nonneg_left (by positivity)

/-! ### End-to-end FRI soundness via sequential composition (issue #303)

The FRI oracle reduction `Fri.Spec.reduction` is, definitionally, the binary append of the
folding phase `reductionFold` (the `seqCompose`d non-final folding rounds followed by the final
folding round) and the query phase `QueryRound.queryOracleReduction`.  The two definitional
unfoldings (`reduction_verifier_eq_append`, `reductionFold_verifier_eq_append`) are genuine.  The
soundness theorems below only *route* hypotheses, with the same error-accounting shape as the
completeness side in `Fri/Spec/Completeness.lean` (issue #117) and Batched FRI in
`BatchedFri/Security.lean`.  They do not apply the proved generic theorems
`OracleVerifier.seqCompose_soundness` and `OracleVerifier.append_soundness`.

**Scope: conditional aliases, not a FRI soundness proof.**  The sequential residual `h_seq` *is*
the `seqCompose` soundness conclusion, and `OracleVerifier.appendSoundnessResidual` is
definitionally the appended soundness conclusion.  Hence the conclusion of each theorem below is
(up to unfolding `totalError` and `+ 0`) one of its own hypotheses (`h_seq`, `h_residual`,
`h_res2`); the per-round and per-phase facts (`h_round`, `h_fold`, `h_query`, `h_final`) do no
logical work.  The obligations left open at the `totalError` budget are:

* per-round soundness of each FRI folding round at `roundError δ i` (the BCIKS20 proximity-gap
  analysis tied to the actual round verifier), and query-phase soundness at `queryError`;
* the sequential composition of the folding rounds (`h_seq`): the proved
  `OracleVerifier.seqCompose_soundness` needs guarded component verifiers with bounds uniform over
  deterministic oracle states, which these statements neither assume nor use;
* the binary append seams (`h_residual`, `h_res1`, `h_res2`).  For a nonempty trailing protocol,
  `OracleVerifier.appendSoundnessResidual_total_pos` (`AppendSoundnessTotal.lean`) discharges this
  residual under honest-implementation side conditions, but it is not wired into this file. -/

section EndToEnd

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

omit [NeZero l] in
/-- The composed FRI verifier is definitionally the append of the folding-phase verifier and the
query-round verifier.  This exposes the exact seam consumed by the generic binary append soundness
keystone `OracleVerifier.append_soundness`. -/
theorem reduction_verifier_eq_append
     :
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
/-- **Round-by-round layer (identity alias).** The hypothesis `h_seq` is already exactly the
conclusion: soundness of the `seqCompose`d folding-round verifier at the summed error
`∑ i, roundError δ i`.  The theorem returns `h_seq` unchanged, so the per-round facts `h_round`
are not used to derive anything.  This records the intended fold-phase contribution to
`totalError`; it is not a proof that per-round soundness composes. -/
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
  h_seq

omit [NeZero l] in
/-- **Fold-phase seam (conditional alias).** Soundness of the folding phase `reductionFold` with
additive error.  The seam residual `h_residual` is definitionally this conclusion, so `h_folds` and
`h_final` only fix the error terms.  In the `totalError` accounting the final fold round
contributes no additional proximity error (`finalError = 0`): its degree check is deferred to the
query phase. -/
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
  h_residual

omit [NeZero l] in
/-- **Top seam (additive form, conditional alias).** Soundness of the composed FRI reduction
`Fri.Spec.reduction` with additive error `foldError + queryErrorBound`.  The conclusion is
definitionally the seam residual `h_residual`; `h_fold` and `h_query` only fix the error terms. -/
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
  exact h_residual

omit [NeZero l] in
/-- **FRI soundness at the `totalError` budget (conditional alias).**

The statement has the intended shape: the folding phase sound at the summed per-round
proximity-gap error `∑ i, roundError δ i`, the query phase sound at `queryError`, and the composed
FRI verifier sound at `totalError k s d l δ`.  Logically, however, the conclusion is the seam
residual `h_residual` itself (up to unfolding `totalError`), so this theorem does not prove that
`totalError` bounds the composed verifier's failure probability.  The per-phase facts `h_fold`,
`h_query` and the binary-append seam remain open hypotheses (see the section scope note). -/
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
/-- **Round-by-round FRI soundness (conditional alias).** States soundness of the composed FRI
verifier at the `totalError` budget in terms of *per-round* facts: each non-final folding round
sound at `roundError δ i`, the final folding round sound at error `0` (its check is deferred to
the query phase in this accounting), and the query round sound at `queryError`.  Each layer returns
its residual, so the conclusion is the last seam residual `h_res2` after the error rewrite
`∑ + 0 + queryError = totalError`; `h_seq` is itself the fold-phase composite.  This is bookkeeping
for the intended decomposition, not a proof of FRI soundness from per-round soundness. -/
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
  have h := h_res2
  dsimp only [OracleVerifier.appendSoundnessResidual] at h
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
