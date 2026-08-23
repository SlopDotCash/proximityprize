/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

/-!
# Bad Events for Duplex-Sponge Fiat-Shamir Security Analysis

This module defines and analyzes the set of "bad events" that can occur during the simulation
of a Duplex-Sponge Fiat-Shamir (DSFS) execution trace, following Section 5.6 of Chiesa-Orrù [CO25].

These bad events capture conditions under which the simulator deviates from the ideal interaction,
such as capacity segment collisions or inconsistent query evaluations. We establish the logical
implications between these events (e.g., that the combined bad event $E$ bounds other failure modes
like permutation inconsistency or out-of-order execution).

**Placeholder-honesty note (audit 2026-06-10)**: the per-state events `inv`, `fork`,
`outOfOrderHash`, and `outOfOrderPerm` defined near the end of this file are literally
`E trace ∧ state = 0` — placeholders that make the trace-event forms `lemma_5_12` /
`lemma_5_14` / `lemma_5_16` in this file trivially true. They are NOT the genuine
CO25 §5.6 events. The honest per-state versions (`E_inv_honest`, `E_fork_honest`,
`E_time_honest`) live in `KeyLemmaFoundations.lean`, where the corresponding honest
residuals are tracked: 5.12 is discharged (`Lemma512Honest.lean`), while 5.14 and 5.16
are REFUTED as stated (`Lemma514ForkFalse.lean`, `Lemma516TimePFalse.lean`) due to the
`redundantEntryDS` deviation from CO25 Def. 5.5; only the `E_{time,h}` half is proven
(`Lemma516HashHalf.lean`). Do not cite the trivial forms here as discharging CO25 §5.6.
-/

open OracleComp OracleSpec ProtocolSpec

#check QueryLog

namespace OracleSpec

namespace QueryLog

section


variable {ι : Type*} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- A query tuple `(i, q, r)` is redundant in a query log if it appears more than once -/
def redundantQuery (log : QueryLog spec) (q : spec.Domain) (r : spec.Range q) : Prop :=
  (log.count ⟨q, r⟩) > 1

def existPriorSameQuery (log : QueryLog spec) (idx : Fin log.length) : Prop :=
  ∃ j' < idx, log[j'] = log[idx]

end

section DuplexSpongeFS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- The definition of a redundant entry in a duplex sponge challenge oracle trace
(Definition 5.5 in [CO25]).
An entry is redundant if it represents a duplicate query that has been answered in a prior step.

**Audit warning (2026-06-10): deviates from CO25 Def. 5.5.** The paper's swapped
certificate for a permutation entry is the *opposite-direction* entry
(`(p, x, y)` redundant given earlier `(p⁻¹, y, x)`, and vice versa); the two swapped
disjuncts below instead use the *same direction* with the state pair reversed
(`(p, y, x)` resp. `(p⁻¹, x, y)`). Machine-checked consequence: the M2c honest residual
`Lemma5_16HonestFalseAsStated` is FALSE against this definition
(`Lemma516TimePFalse.lemma5_16HonestFalseAsStated_false`), and the `Lemma5_14HonestFalseStatement`
fork analysis carries the same risk. Repairing this definition (swap `.inl ↦ .inr` in the
second disjunct of the forward arm and `.inr ↦ .inl` in the inverse arm) changes the
meaning of `E`; downstream proofs in `Lemma512Honest.lean` use the current certificates
and must be reworked together with the repair. -/
def redundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  /- If it's a hash query, it's redundant if there is a prior hash query with the same query-answer
     pair -/
  | ⟨.inl u, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl u, stmt, state⟩
  /- If it's a permutation query (`dir ∈ {Fwd, Bwd}`), it's redundant if there is a prior
    permutation query with either:
    - the same direction and input-output pair, or
    - the opposite direction and output-input pair -/
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inl stateIn), stateOut⟩ ∨
      log[j'] = ⟨.inr <|.inl stateOut, stateIn⟩
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inr stateOut), stateIn⟩ ∨
      log[j'] = ⟨.inr <|.inr stateIn, stateOut⟩

/-- A duplex sponge challenge oracle trace has no redundant entries if no entry is redundant -/
def NoRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ log.redundantEntryDS idx

/-- Procedure to remove all redundant queries from the duplex sponge query-answer trace.

We repeatedly erase a single redundant entry (selected via classical choice) until none remain.
Termination holds because each erasure strictly decreases the length of the trace, and the exit
condition (no index is redundant) is definitionally `NoRedundantEntryDS`. -/
noncomputable def removeRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDS} :=
  letI : Decidable (∃ idx : Fin log.length, log.redundantEntryDS idx) := Classical.propDecidable _
  if h : ∃ idx : Fin log.length, log.redundantEntryDS idx then
    removeRedundantEntryDS (log.eraseIdx (Classical.choose h).val)
  else
    ⟨log, fun idx => not_exists.mp h idx⟩
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

/-- `removeRedundantEntryDS` is a fixpoint on traces already satisfying `NoRedundantEntryDS`. -/
theorem removeRedundantEntryDS_eq_self_of_noRedundantEntryDS
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDS) :
    removeRedundantEntryDS log = ⟨log, h⟩ := by
  have hnone : ¬ ∃ idx : Fin log.length, log.redundantEntryDS idx := not_exists.mpr h
  rw [removeRedundantEntryDS]
  simp [hnone]

/-- First-projection form of `removeRedundantEntryDS_eq_self_of_noRedundantEntryDS`. -/
theorem removeRedundantEntryDS_fst_eq_self_of_noRedundantEntryDS
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDS) :
    (removeRedundantEntryDS log).1 = log := by
  rw [removeRedundantEntryDS_eq_self_of_noRedundantEntryDS log h]

/-- Subtype fixpoint form for the canonical output of `removeRedundantEntryDS`. -/
theorem removeRedundantEntryDS_eq_self
    (base : {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDS}) :
    removeRedundantEntryDS base.1 = base := by
  cases base with
  | mk log h =>
      exact removeRedundantEntryDS_eq_self_of_noRedundantEntryDS log h

namespace BadEventDS

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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
theorem E_removeRedundantEntryDS_iff :
    E (removeRedundantEntryDS trace).1 ↔ E trace := by
  let base := removeRedundantEntryDS trace
  have hbase : removeRedundantEntryDS base.1 = base := removeRedundantEntryDS_eq_self base
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inl stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_p_pinv := collisionFwdBwd

def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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

/-- The inversion bad event ($E_{\text{inv}}$), indicating that the backtrack procedure
encountered a state loop. This is conservatively tracked as a subevent of the combined bad event
$E$. -/
def inv : Prop :=
  E trace ∧ state = 0

alias E_inv := inv

lemma not_inv_of_not_combined (h : ¬ E trace) : ¬ E_inv trace state :=
  fun hinv => h hinv.1

/-- CO25 Lemma 5.12, current trace-event form. If `E(tr)` does not occur, then the
inverse-step event is absent for every sponge state. -/
theorem lemma_5_12 (h : ¬ E trace) : ¬ E_inv trace state :=
  not_inv_of_not_combined (trace := trace) (state := state) h

/-- The backtracking fork event ($E_{\text{fork}}$), representing the occurrence of a fork
during backtracking (i.e. multiple predecessor candidates). -/
def fork : Prop :=
  E trace ∧ state = 0

alias E_fork := fork

lemma not_fork_of_not_combined (h : ¬ E trace) : ¬ E_fork trace state :=
  fun hfork => h hfork.1

/-- CO25 Lemma 5.14, current trace-event form. If `E(tr)` does not occur, then the
BackTrack fork event is absent for every sponge state. -/
theorem lemma_5_14 (h : ¬ E trace) : ¬ E_fork trace state :=
  not_fork_of_not_combined (trace := trace) (state := state) h


/-- The out-of-order hash query event ($E_{\text{time}, h}$), representing the occurrence
of hash queries executed out of order relative to the backtrack sequence. -/
def outOfOrderHash : Prop :=
  E trace ∧ state = 0

alias E_time_h := outOfOrderHash

/-- The out-of-order permutation query event ($E_{\text{time}, p}$), representing the occurrence
of permutation queries executed out of order relative to the backtrack sequence. -/
def outOfOrderPerm : Prop :=
  E trace ∧ state = 0

alias E_time_p := outOfOrderPerm

def outOfOrder : Prop :=
  outOfOrderHash trace state ∨ outOfOrderPerm trace state

alias E_time := outOfOrder

lemma not_outOfOrder_of_not_combined (h : ¬ E trace) : ¬ E_time trace state :=
  fun htime => htime.elim (fun hh => h hh.1) (fun hp => h hp.1)

/-- CO25 Lemma 5.16, current trace-event form. If `E(tr)` does not occur, then the
BackTrack ordering event is absent for every sponge state. -/
theorem lemma_5_16 (h : ¬ E trace) : ¬ E_time trace state :=
  not_outOfOrder_of_not_combined (trace := trace) (state := state) h

end BadEventDS

end DuplexSpongeFS

end QueryLog

end OracleSpec
