/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Paper-faithful redundant-entry dedup for the duplex-sponge trace (CO25 Def. 5.5)

`BadEvents.lean`'s `redundantEntryDS` deviates from CO25 (ePrint 2025/536) Definition 5.5: its
swapped certificate for a permutation entry uses the **same direction** with the state pair
reversed, where the paper uses the **opposite-direction** entry (`(p, x, y)` is redundant given a
prior `(p⁻¹, y, x)`, and vice versa). That deviation is not cosmetic — both honest residuals
written against it are *refuted* by machine-checked countermodels
(`Lemma516TimePFalse.lean`, `Lemma514ForkFalse.lean`).

This file introduces the paper-faithful definition `redundantEntryDSPaper` (the two swapped
disjuncts corrected to opposite-direction certificates) together with its dedup machinery
(`NoRedundantEntryDSPaper`, `removeRedundantEntryDSPaper`, fixpoint lemmas), mirroring the
legacy API so the downstream chain (`Lemma512Honest.lean`, the `KeyLemmaFoundations.lean`
honest residuals) can migrate incrementally. The legacy definition stays in place — the landed
refutations are *about it* and remain meaningful as the record of why this repair exists.

Note the semantic consequence flagged by the refutation analysis: under paper semantics a raw
*inverse* entry can dedup against a prior *forward* entry (and vice versa), so the legacy
"inverse entry ⇒ E" keystone of `Lemma512Honest.lean` changes shape under migration.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleSpec

namespace QueryLog

section DuplexSpongeFS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- **Paper-faithful redundant entry (CO25 Def. 5.5).** An entry is redundant if a prior entry
answers it: same hash query-answer pair; same-direction same permutation pair; or — the corrected
clause — the **opposite-direction** permutation entry with input/output exchanged
(`(p, x, y)` given a prior `(p⁻¹, y, x)`; `(p⁻¹, y, x)` given a prior `(p, x, y)`). -/
def redundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  | ⟨.inl u, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl u, stmt, state⟩
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inl stateIn), stateOut⟩ ∨
      log[j'] = ⟨.inr <|.inr stateOut, stateIn⟩
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inr stateOut), stateIn⟩ ∨
      log[j'] = ⟨.inr <|.inl stateIn, stateOut⟩

/-- A trace has no paper-redundant entries. -/
def NoRedundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ log.redundantEntryDSPaper idx

/-- Remove paper-redundant entries by repeated erasure (classical choice of a redundant index),
mirroring `removeRedundantEntryDS`. Terminates since each erasure shortens the trace. -/
noncomputable def removeRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDSPaper} :=
  letI : Decidable (∃ idx : Fin log.length, log.redundantEntryDSPaper idx) :=
    Classical.propDecidable _
  if h : ∃ idx : Fin log.length, log.redundantEntryDSPaper idx then
    removeRedundantEntryDSPaper (log.eraseIdx (Classical.choose h).val)
  else
    ⟨log, fun idx => not_exists.mp h idx⟩
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

/-- `removeRedundantEntryDSPaper` is a fixpoint on already-deduplicated traces. -/
theorem removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDSPaper) :
    removeRedundantEntryDSPaper log = ⟨log, h⟩ := by
  have hnone : ¬ ∃ idx : Fin log.length, log.redundantEntryDSPaper idx := not_exists.mpr h
  rw [removeRedundantEntryDSPaper]
  simp [hnone]

/-- First-projection form of the fixpoint lemma. -/
theorem removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDSPaper) :
    (removeRedundantEntryDSPaper log).1 = log := by
  rw [removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h]

/-- Subtype fixpoint form for the canonical output. -/
theorem removeRedundantEntryDSPaper_eq_self
    (base : {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) |
      log.NoRedundantEntryDSPaper}) :
    removeRedundantEntryDSPaper base.1 = base := by
  cases base with
  | mk log h =>
      exact removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h

/-- A hash entry's paper-redundancy coincides with legacy redundancy (the repair only touches
the permutation arms). -/
theorem redundantEntryDSPaper_iff_of_hash
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin log.length)
    {u : StmtIn} {v : _} (hidx : log[idx] = ⟨.inl u, v⟩) :
    log.redundantEntryDSPaper idx ↔ log.redundantEntryDS idx := by
  unfold redundantEntryDSPaper redundantEntryDS
  rw [hidx]
  rcases v with ⟨stmt, state⟩
  rfl


namespace BadEventDSPaper

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-!
We define the main simulator failure conditions (the "bad events" of CO25 Section 5.6):
1. **Capacity collision** ($E_{\text{dup}}$): Duplicate occurrences of capacity segments in the
   reduced trace.
2. **Permutation inconsistency** ($E_{\text{func}}$): Conflicting evaluations of the permutation
   oracle, where the same input yields different outputs or the forward and inverse permutation
   directions conflict.
-/

def capacitySegmentDupHash : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    ∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩ ∧
      ∃ j' < j,
        ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩ ∨
        (∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩
          ∧ stateOut1.capacitySegment = capSeg) ∨
        (∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩
          ∧ stateIn2.capacitySegment = capSeg) ∨
        (∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩
          ∧ stateIn3.capacitySegment = capSeg) ∨
        (∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩
          ∧ stateOut4.capacitySegment = capSeg)

alias E_h := capacitySegmentDupHash

def capacitySegmentDupPerm : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          stateIn2.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
          stateOut4.capacitySegment = capSeg)
      )

alias E_p := capacitySegmentDupPerm

def capacitySegmentDupPermInv : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' < j, ∃ stateIn2 stateOut2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          CanonicalSpongeState.capacitySegment stateIn2 = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn4 stateOut4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
          CanonicalSpongeState.capacitySegment stateIn4 = capSeg)
      )

alias E_pinv := capacitySegmentDupPermInv

/-- The combined capacity segment collision event. This occurs if there is any capacity segment
collision in the hash query, forward permutation query, or inverse permutation query logs. -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/- The same query to `p` leads to different answers, or there are inconsistent queries across `p`
and `p⁻¹` -/
def notFunction : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ j : Fin baseTrace.length, ∃ stateIn _stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <|.inl stateIn, _stateOut⟩ ∧
      ∃ j' < j,
        ∃ stateOut1 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∨
        ∃ stateOut2 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩

alias E_func := notFunction

def combined : Prop :=
  capacitySegmentDup trace ∨ notFunction trace

alias E := combined

/-- The combined bad event only depends on the deduplicated base trace. -/
theorem E_removeRedundantEntryDSPaper_iff :
    E (removeRedundantEntryDSPaper trace).1 ↔ E trace := by
  let base := removeRedundantEntryDSPaper trace
  have hbase : removeRedundantEntryDSPaper base.1 = base := removeRedundantEntryDSPaper_eq_self base
  constructor
  · intro h
    unfold E combined capacitySegmentDup capacitySegmentDupHash
      capacitySegmentDupPerm capacitySegmentDupPermInv notFunction at h ⊢
    dsimp only at h ⊢
    rw [hbase] at h
    simpa [base] using h
  · intro h
    unfold E combined capacitySegmentDup capacitySegmentDupHash
      capacitySegmentDupPerm capacitySegmentDupPermInv notFunction at h ⊢
    dsimp only at h ⊢
    rw [hbase]
    simpa [base] using h

/-!
We define supplementary collision events (forward-forward, backward-backward, and mixed collisions)
and show that they are bounded by the combined collision event $E$.
-/

def collisionFwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inl stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_p_pinv := collisionFwdBwd

def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDSPaper trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

alias E_prp := collisionPerm

lemma not_collisionPerm_of_not_combined (h : ¬ E trace) : ¬ E_prp trace := by
  intro hprp
  apply h; clear h
  rcases hprp with hff | hbb | hfb | hbf
  · -- collisionFwdFwd → E
    obtain ⟨sI, sI', sO, hm1, hm2, hne⟩ := hff
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact hne (congrArg (fun x => match x with | ⟨.inr (.inl s), _⟩ => s | _ => sI) hgj)
    left; right; left
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · exact ⟨⟨j, hj⟩, sO.capacitySegment, ⟨sI', sO, hgj, rfl⟩,
        Or.inr (Or.inl ⟨⟨i, hi⟩, h_lt, sI, sO, hgi, rfl⟩)⟩
    · exact ⟨⟨i, hi⟩, sO.capacitySegment, ⟨sI, sO, hgi, rfl⟩,
        Or.inr (Or.inl ⟨⟨j, hj⟩, h_lt, sI', sO, hgj, rfl⟩)⟩
  · -- collisionBwdBwd → E
    obtain ⟨sO, sO', sI, hm1, hm2, hne⟩ := hbb
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact hne (congrArg (fun x => match x with | ⟨.inr (.inr s), _⟩ => s | _ => sO) hgj)
    left; right; right
    unfold capacitySegmentDupPermInv
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · refine ⟨⟨j, hj⟩, sI.capacitySegment, ⟨sO', sI, hgj, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨i, hi⟩, h_lt, sI, sO, hgi, rfl⟩
    · refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨j, hj⟩, h_lt, sI, sO', hgj, rfl⟩
  · -- collisionFwdBwd → E
    obtain ⟨sI, sO, sO', hm1, hm2, hne⟩ := hfb
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact absurd (congrArg Sigma.fst hgj) (by simp)
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · -- forward at i, backward at j, i < j: use capacitySegmentDupPermInv at j
      left; right; right
      unfold capacitySegmentDupPermInv
      refine ⟨⟨j, hj⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO', sI, hgj, rfl⟩, ?_⟩
      right; left
      exact ⟨⟨i, hi⟩, h_lt, sO, sI, hgi, rfl⟩
    · -- forward at i, backward at j, j < i: use capacitySegmentDupPerm at i
      left; right; left
      unfold capacitySegmentDupPerm
      refine ⟨⟨i, hi⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO, sI, hgi, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨j, hj⟩, Nat.le_of_lt h_lt, sO', sI, hgj, rfl⟩
  · -- collisionBwdFwd → E
    obtain ⟨sI, sO, sO', hm1, hm2, hne⟩ := hbf
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact absurd (congrArg Sigma.fst hgj) (by simp)
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · -- backward at i, forward at j, i < j: use capacitySegmentDupPerm at j
      left; right; left
      unfold capacitySegmentDupPerm
      refine ⟨⟨j, hj⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO', sI, hgj, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨i, hi⟩, Nat.le_of_lt h_lt, sO, sI, hgi, rfl⟩
    · -- backward at i, forward at j, j < i: use capacitySegmentDupPermInv at i
      left; right; right
      unfold capacitySegmentDupPermInv
      refine ⟨⟨i, hi⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO, sI, hgi, rfl⟩, ?_⟩
      right; left
      exact ⟨⟨j, hj⟩, h_lt, sO', sI, hgj, rfl⟩

/-- CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does
not occur, then the permutation-consistency event `E_prp(tr)` does not occur. -/
theorem lemma_5_10 (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) h


end BadEventDSPaper

end DuplexSpongeFS

end QueryLog

end OracleSpec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_iff_of_hash
#print axioms OracleSpec.QueryLog.BadEventDSPaper.E_removeRedundantEntryDSPaper_iff
#print axioms OracleSpec.QueryLog.BadEventDSPaper.lemma_5_10
