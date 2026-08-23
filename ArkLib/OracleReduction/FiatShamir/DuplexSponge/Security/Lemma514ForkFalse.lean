/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma516TimePFalse

/-!
# `Lemma5_14HonestFalseStatement` is FALSE as stated: a machine-checked fork countermodel

This file settles the audit question for the M2b residual (CO25 Lemma 5.14, honest form):
like its sibling `Lemma5_16HonestFalseAsStated` (refuted in `Lemma516TimePFalse.lean`), the
in-tree statement is **false**, for exactly the same root cause — the same-direction
swapped certificate in `redundantEntryDS` (deviation from CO25 Definition 5.5).

## The countermodel

`U := UInt8`, sponge geometry `{N := 2, R := 1}` (reused from `Lemma516TimePFalse`).
States `(rate, cap)`: `t1 = (0,1)`, `t2 = (1,2)`, `t3 = (2,1)`, `t4 = (3,3)`.
Note `cap t1 = cap t3 = [1]` while `t1 ≠ t3` (different rates).

Raw trace (5 entries, in order):
0. `(h, (), [1])` — single hash anchor with capacity `1`;
1. `(p, t1, t2)` — orientation 1 of the alternating pair `{t1, t2}`;
2. `(p, t2, t1)` — orientation 2; **in-tree-redundant** w.r.t. entry 1;
3. `(p, t3, t4)` — orientation 1 of the alternating pair `{t3, t4}`;
4. `(p, t4, t3)` — orientation 2; **in-tree-redundant** w.r.t. entry 3.

Two backtrack chains end at the same target state `t1`:
* `seqOne`: `inputState = [t1, t2, t1]` (steps `t1→t2` via entry 1, `t2→t1` via entry 2);
* `seqTwo`: `inputState = [t3, t4, t1]` (steps `t3→t4` via entry 3, `t4→t3` via entry 4 —
  the final output `t3` matches the target capacity `cap t1 = [1]`).

Both chains share the single hash anchor (capacity `1`). Neither chain's `inputState` is
a `List.Subset` of the other's (`t2 ∉ {t3,t4,t1}`, `t4 ∉ {t1,t2}`), so the two-element
family is maximal and `E_fork_honest` fires (`|S_BT| = 2 > 1`).

Meanwhile the dedup'd trace is `[hash(1), (p,t1,t2), (p,t3,t4)]`: the in-tree
`redundantEntryDS` erases both reversed orientations (entries 2 and 4), and the answer
capacities of the survivors are `2` and `3` — each fresh. The duplicated capacity `1`
occurs only on **query** sides (`t1`, `t3`) and the hash (hash-first order), where no
`capacitySegmentDup*` / `notFunction` anchor can fire. So `¬ E` holds.

Under CO25's actual Definition 5.5 (opposite-direction `p⁻¹` certificates), entries 2 and
4 would survive dedup; their answer capacities (`1` twice) would collide with the hash
capacity and with each other, firing `E` — so this countermodel is *specific to the
in-tree dedup*, and the same one-token statement repair flagged in `BadEvents.lean`
(`.inl ↦ .inr` in the swapped certificates) is the prerequisite for the honest
Lemma 5.14.

Unlike the 5.16 countermodel, the dedup here erases **two** entries; since
`removeRedundantEntryDS` picks redundant indices by classical choice, the fixpoint
computation case-splits on which of `{2, 4}` is erased first (both orders converge to the
same 3-entry trace).
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

namespace DuplexSpongeFS.Sponge316.ForkCounter

open DuplexSpongeFS.Sponge316.TimePCounter (St mkSt)

/-- Entry type at `StmtIn := Unit`, `U := UInt8` (sponge geometry `{N := 2, R := 1}`
inherited from `TimePCounter.smallSponge`). -/
abbrev Entry := OracleSpec.duplexSpongeTraceEntry (StartType := Unit) (U := UInt8)

def t1 : St := mkSt 0 1
def t2 : St := mkSt 1 2
def t3 : St := mkSt 2 1
def t4 : St := mkSt 3 3

def eH : Entry := ⟨Sum.inl (), #v[1]⟩
def q1 : Entry := ⟨Sum.inr (Sum.inl t1), t2⟩
def q2 : Entry := ⟨Sum.inr (Sum.inl t2), t1⟩
def q3 : Entry := ⟨Sum.inr (Sum.inl t3), t4⟩
def q4 : Entry := ⟨Sum.inr (Sum.inl t4), t3⟩

/-- The raw countermodel trace. -/
def trcF : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, q1, q2, q3, q4]

/-- Intermediate trace after erasing slot 2 first. -/
def trcA : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, q1, q3, q4]

/-- Intermediate trace after erasing slot 4 first. -/
def trcB : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, q1, q2, q3]

/-- The dedup fixpoint: both erasure orders converge here. -/
def trcD : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, q1, q3]

/-! ## The two backtrack chains and the fork family -/

/-- Chain 1: the alternating loop `t1 → t2 → t1` on the first pair. -/
def seqOne : DuplexSpongeFS.Backtrack.BacktrackSequence trcF t1 where
  stmt := ()
  inputState := [t1, t2, t1]
  outputState := [t2, t1]
  inputState_length_eq_outputState_length_succ := rfl
  last_inputState_eq_state := rfl
  hash_in_trace := List.Mem.head _
  permute_or_inv_in_trace := by
    intro i
    fin_cases i
    · exact Or.inl (List.Mem.tail _ (List.Mem.head _))
    · exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  capacitySegment_output_eq_input := by decide
  capacitySegment_input_ne_output := by decide

/-- Chain 2: the alternating loop `t3 → t4 → (cap t3 = cap t1)` on the second pair,
ending at the same target `t1`. -/
def seqTwo : DuplexSpongeFS.Backtrack.BacktrackSequence trcF t1 where
  stmt := ()
  inputState := [t3, t4, t1]
  outputState := [t4, t3]
  inputState_length_eq_outputState_length_succ := rfl
  last_inputState_eq_state := rfl
  hash_in_trace := List.Mem.head _
  permute_or_inv_in_trace := by
    intro i
    fin_cases i
    · exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    · exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))
  capacitySegment_output_eq_input := by decide
  capacitySegment_input_ne_output := by decide

/-- The two chains are distinct (their `inputState` lists differ). -/
lemma seqOne_ne_seqTwo : seqOne ≠ seqTwo := by
  intro h
  exact absurd (congrArg DuplexSpongeFS.Backtrack.BacktrackSequence.inputState h) (by decide)

/-- The two-element backtrack family `{seqOne, seqTwo}`; maximality holds because
neither chain's state lists are (membership-)subsets of the other's. -/
def famF : DuplexSpongeFS.Backtrack.S_BT trcF t1 where
  seqFamily := Finset.cons seqOne {seqTwo}
    (fun h => seqOne_ne_seqTwo (Finset.mem_singleton.mp h))
  maximality := by
    intro s hs s' hs' hne hsub
    rcases Finset.mem_cons.mp hs with h1 | h1 <;>
      rcases Finset.mem_cons.mp hs' with h2 | h2 <;>
      try rw [Finset.mem_singleton] at *
    · exact hne (h1.trans h2.symm)
    · -- s = seqOne, s' = seqTwo: t2 would have to be among {t3, t4, t1}
      subst h1; subst h2
      have ht2 : t2 ∈ seqTwo.inputState :=
        hsub.2.1 (show t2 ∈ seqOne.inputState from List.Mem.tail _ (List.Mem.head _))
      revert ht2
      decide
    · -- s = seqTwo, s' = seqOne: t4 would have to be among {t1, t2}
      subst h1; subst h2
      have ht4 : t4 ∈ seqOne.inputState :=
        hsub.2.1 (show t4 ∈ seqTwo.inputState from List.Mem.tail _ (List.Mem.head _))
      revert ht4
      decide
    · exact hne (h1.trans h2.symm)

/-- The fork event fires: the family has two elements. -/
theorem e_fork_holds :
    DuplexSpongeFS.KeyLemmaFoundations.E_fork_honest trcF t1 famF := by
  show 1 < famF.seqFamily.card
  rw [show famF.seqFamily =
    Finset.cons seqOne {seqTwo}
      (fun h => seqOne_ne_seqTwo (Finset.mem_singleton.mp h)) from rfl]
  rw [Finset.card_cons, Finset.card_singleton]
  omega

/-! ## Dedup computation: slots 2 and 4 are redundant, both erasure orders give `trcD` -/

/-- Slot 2 (`(p, t2, t1)`) is in-tree-redundant: slot 1 is its swapped certificate. -/
lemma trcF_redundant_two (h2 : 2 < trcF.length) : trcF.redundantEntryDS ⟨2, h2⟩ :=
  ⟨⟨1, by norm_num [trcF]⟩, by simp [Fin.lt_def], Or.inr rfl⟩

/-- Slot 4 (`(p, t4, t3)`) is in-tree-redundant: slot 3 is its swapped certificate. -/
lemma trcF_redundant_four (h4 : 4 < trcF.length) : trcF.redundantEntryDS ⟨4, h4⟩ :=
  ⟨⟨3, by norm_num [trcF]⟩, by simp [Fin.lt_def], Or.inr rfl⟩

/-- No slot of `trcF` other than `2` and `4` is redundant. -/
lemma trcF_redundant_only (idx : Fin trcF.length) (hred : trcF.redundantEntryDS idx) :
    idx.val = 2 ∨ idx.val = 4 := by
  obtain ⟨v, hv⟩ := idx
  have hv5 : v < 5 := hv
  interval_cases v
  · -- hash at 0: no prior slot
    obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · -- (p, t1, t2) at 1: slot 0 is a hash entry
    obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trcF[(⟨0, hw⟩ : Fin trcF.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · exact Or.inl rfl
  · -- (p, t3, t4) at 3: slots 0/1/2 hold neither orientation
    obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw012 with h0 | h1 | h2
    · subst h0
      rw [show trcF[(⟨0, hw⟩ : Fin trcF.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trcF[(⟨1, hw⟩ : Fin trcF.length)] = q1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h2
      rw [show trcF[(⟨2, hw⟩ : Fin trcF.length)] = q2 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
  · exact Or.inr rfl

/-- In `trcA = [eH, q1, q3, q4]`, slot 3 is redundant (slot 2 is its certificate). -/
lemma trcA_redundant_three (h3 : 3 < trcA.length) : trcA.redundantEntryDS ⟨3, h3⟩ :=
  ⟨⟨2, by norm_num [trcA]⟩, by simp [Fin.lt_def], Or.inr rfl⟩

/-- In `trcA`, only slot 3 is redundant. -/
lemma trcA_redundant_only (idx : Fin trcA.length) (hred : trcA.redundantEntryDS idx) :
    idx.val = 3 := by
  obtain ⟨v, hv⟩ := idx
  have hv4 : v < 4 := hv
  interval_cases v
  · obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trcA[(⟨0, hw⟩ : Fin trcA.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw01 with h0 | h1
    · subst h0
      rw [show trcA[(⟨0, hw⟩ : Fin trcA.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trcA[(⟨1, hw⟩ : Fin trcA.length)] = q1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
  · rfl

/-- In `trcB = [eH, q1, q2, q3]`, slot 2 is redundant (slot 1 is its certificate). -/
lemma trcB_redundant_two (h2 : 2 < trcB.length) : trcB.redundantEntryDS ⟨2, h2⟩ :=
  ⟨⟨1, by norm_num [trcB]⟩, by simp [Fin.lt_def], Or.inr rfl⟩

/-- In `trcB`, only slot 2 is redundant. -/
lemma trcB_redundant_only (idx : Fin trcB.length) (hred : trcB.redundantEntryDS idx) :
    idx.val = 2 := by
  obtain ⟨v, hv⟩ := idx
  have hv4 : v < 4 := hv
  interval_cases v
  · obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trcB[(⟨0, hw⟩ : Fin trcB.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · rfl
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw012 with h0 | h1 | h2
    · subst h0
      rw [show trcB[(⟨0, hw⟩ : Fin trcB.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trcB[(⟨1, hw⟩ : Fin trcB.length)] = q1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h2
      rw [show trcB[(⟨2, hw⟩ : Fin trcB.length)] = q2 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)

/-- No slot of the 3-entry trace `trcD` is redundant. -/
lemma trcD_noRedundant : ∀ idx : Fin trcD.length, ¬ trcD.redundantEntryDS idx := by
  intro idx hred
  obtain ⟨v, hv⟩ := idx
  have hv3 : v < 3 := hv
  interval_cases v
  · obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw01 with h0 | h1
    · subst h0
      rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)

/-- The dedup fixpoint of `trcF` is `trcD`: classical choice first erases slot 2 or
slot 4, and both branches converge after erasing the remaining redundant slot. -/
lemma dedup_eq : (removeRedundantEntryDS trcF).1 = trcD := by
  have hex : ∃ idx : Fin trcF.length, trcF.redundantEntryDS idx :=
    ⟨⟨2, by norm_num [trcF]⟩, trcF_redundant_two _⟩
  rw [removeRedundantEntryDS]
  split
  · rename_i hex2
    rcases trcF_redundant_only _ (Classical.choose_spec hex2) with hch | hch
    · -- slot 2 erased first → `trcA`, then slot 3
      rw [hch, show trcF.eraseIdx 2 = trcA from rfl]
      have hexA : ∃ idx : Fin trcA.length, trcA.redundantEntryDS idx :=
        ⟨⟨3, by norm_num [trcA]⟩, trcA_redundant_three _⟩
      rw [removeRedundantEntryDS]
      split
      · rename_i hex3
        have hch3 : (Classical.choose hex3).val = 3 :=
          trcA_redundant_only _ (Classical.choose_spec hex3)
        rw [hch3, show trcA.eraseIdx 3 = trcD from rfl]
        rw [removeRedundantEntryDS]
        split
        · rename_i hex4
          obtain ⟨i, hi⟩ := hex4
          exact absurd hi (trcD_noRedundant i)
        · rfl
      · rename_i hnone
        exact absurd hexA hnone
    · -- slot 4 erased first → `trcB`, then slot 2
      rw [hch, show trcF.eraseIdx 4 = trcB from rfl]
      have hexB : ∃ idx : Fin trcB.length, trcB.redundantEntryDS idx :=
        ⟨⟨2, by norm_num [trcB]⟩, trcB_redundant_two _⟩
      rw [removeRedundantEntryDS]
      split
      · rename_i hex3
        have hch3 : (Classical.choose hex3).val = 2 :=
          trcB_redundant_only _ (Classical.choose_spec hex3)
        rw [hch3, show trcB.eraseIdx 2 = trcD from rfl]
        rw [removeRedundantEntryDS]
        split
        · rename_i hex4
          obtain ⟨i, hi⟩ := hex4
          exact absurd hi (trcD_noRedundant i)
        · rfl
      · rename_i hnone
        exact absurd hexB hnone
  · rename_i hnone
    exact absurd hex hnone

/-- Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events. -/
lemma dedup_eq' : removeRedundantEntryDS trcF = ⟨trcD, trcD_noRedundant⟩ :=
  Subtype.ext dedup_eq

/-! ### `E` is absent

On `trcD = [hash(1), (p,t1,t2), (p,t3,t4)]` the answer-side capacities are
`cap t2 = 2` (slot 1) and `cap t4 = 3` (slot 2); the hash capacity is `1`; the query
capacities are `1` (`t1`, `t3`), in hash-first order. No `capacitySegmentDup*` anchor
(all of which anchor on answer-side capacities) or `notFunction` witness exists. -/

/-- The combined bad event `E` does NOT fire on the countermodel trace. -/
theorem not_E_trcF : ¬ BadEventDS.E trcF := by
  intro hE
  rcases hE with (hh | hp | hpinv) | hfunc
  · -- E_h: the only hash entry is at slot 0, with no earlier slot
    unfold capacitySegmentDupHash at hh
    rw [dedup_eq'] at hh
    obtain ⟨j, capSeg, stmt, hj, j', hj', -⟩ := hh
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · exact absurd hj' (by simp [Fin.lt_def])
    · rw [show trcD[(⟨1, hv⟩ : Fin trcD.length)] = q1 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [q1])
    · rw [show trcD[(⟨2, hv⟩ : Fin trcD.length)] = q3 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [q3])
  · -- E_p: forward anchors at slots 1 (ans cap 2) and 2 (ans cap 3)
    unfold capacitySegmentDupPerm at hp
    rw [dedup_eq'] at hp
    obtain ⟨j, capSeg, ⟨sIn, sOut, hj, hcap⟩, hdisj⟩ := hp
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · -- slot 0 is the hash, not a forward entry
      rw [show trcD[(⟨0, hv⟩ : Fin trcD.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · -- anchor (p, t1, t2): capSeg = cap t2 = [2]
      rw [show trcD[(⟨1, hv⟩ : Fin trcD.length)] =
        (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = t1 := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hsOut : sOut = t2 := by simpa [eq_comm] using eq_of_heq hinj.2
      subst hsOut
      subst hcap
      rcases hdisj with ⟨⟨w, hw⟩, hwlt, stmt', hbad⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩
      -- disjunct 1: earlier hash with capSeg = cap t2 = [2]: hash cap is [1]
      · have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hwlt; omega
        subst hw0
        rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = (⟨Sum.inl (), #v[1]⟩ : Entry)
          from rfl] at hbad
        have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
        exact absurd (show (#v[1] : Vector UInt8 SpongeSize.C) =
          CanonicalSpongeState.capacitySegment t2 from eq_of_heq hinj'.2) (by decide)
      -- disjunct 2: earlier forward with answer-cap [2]: slot 0 is a hash
      · have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hwlt; omega
        subst hw0
        rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
        exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
      -- disjunct 3: earlier-or-equal inverse: none exist
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q1])
      -- disjunct 4: earlier-or-equal forward with query-cap [2]: query caps are [1]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] =
            (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = t1 := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
      -- disjunct 5: earlier-or-equal inverse: none exist
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q1])
    · -- anchor (p, t3, t4): capSeg = cap t4 = [3]
      rw [show trcD[(⟨2, hv⟩ : Fin trcD.length)] =
        (⟨Sum.inr (Sum.inl t3), t4⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = t3 := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hsOut : sOut = t4 := by simpa [eq_comm] using eq_of_heq hinj.2
      subst hsOut
      subst hcap
      rcases hdisj with ⟨⟨w, hw⟩, hwlt, stmt', hbad⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩
      -- disjunct 1: earlier hash with capSeg = cap t4 = [3]: hash cap is [1]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = (⟨Sum.inl (), #v[1]⟩ : Entry)
            from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          exact absurd (show (#v[1] : Vector UInt8 SpongeSize.C) =
            CanonicalSpongeState.capacitySegment t4 from eq_of_heq hinj'.2) (by decide)
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q1])
      -- disjunct 2: earlier forward answer-caps: cap t2 = [2] ≠ [3]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] =
            (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = t1 := by simpa [eq_comm] using hinj'.1
          subst hs1
          have hs2 : s2 = t2 := by simpa [eq_comm] using eq_of_heq hinj'.2
          rw [hs2] at hc
          revert hc
          decide
      -- disjunct 3: inverse entries: none exist
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q1])
        · subst h2
          rw [show trcD[(⟨2, hw⟩ : Fin trcD.length)] = q3 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q3])
      -- disjunct 4: forward query-caps: cap t1 = cap t3 = [1] ≠ [3]
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] =
            (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = t1 := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
        · subst h2
          rw [show trcD[(⟨2, hw⟩ : Fin trcD.length)] =
            (⟨Sum.inr (Sum.inl t3), t4⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = t3 := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
      -- disjunct 5: inverse entries: none exist
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] = q1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q1])
        · subst h2
          rw [show trcD[(⟨2, hw⟩ : Fin trcD.length)] = q3 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [q3])
  · -- E_pinv: no inverse entries exist in the dedup'd trace
    unfold capacitySegmentDupPermInv at hpinv
    rw [dedup_eq'] at hpinv
    obtain ⟨j, capSeg, ⟨sOut, sIn, hj, -⟩, -⟩ := hpinv
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · rw [show trcD[(⟨0, hv⟩ : Fin trcD.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · rw [show trcD[(⟨1, hv⟩ : Fin trcD.length)] = q1 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [q1])
    · rw [show trcD[(⟨2, hv⟩ : Fin trcD.length)] = q3 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [q3])
  · -- E_func: the two forward queries t1, t3 are distinct; no inverse entries
    unfold notFunction at hfunc
    rw [dedup_eq'] at hfunc
    obtain ⟨j, sIn, sOut, hj, ⟨w, hw⟩, hj', hcase⟩ := hfunc
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · rw [show trcD[(⟨0, hv⟩ : Fin trcD.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · -- anchor (p, t1, t2): only earlier slot is the hash
      rw [show trcD[(⟨1, hv⟩ : Fin trcD.length)] =
        (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = t1 := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
      subst hw0
      rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hcase
      rcases hcase with ⟨s, h | ⟨s2, h⟩⟩ <;>
        exact absurd (congrArg Sigma.fst h) (by simp [eH])
    · -- anchor (p, t3, t4): earlier slots are the hash and (p, t1, ·) with t1 ≠ t3
      rw [show trcD[(⟨2, hv⟩ : Fin trcD.length)] =
        (⟨Sum.inr (Sum.inl t3), t4⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = t3 := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
      rcases hw01 with h0 | h1
      · subst h0
        rw [show trcD[(⟨0, hw⟩ : Fin trcD.length)] = eH from rfl] at hcase
        rcases hcase with ⟨s, h | ⟨s2, h⟩⟩ <;>
          exact absurd (congrArg Sigma.fst h) (by simp [eH])
      · subst h1
        rw [show trcD[(⟨1, hw⟩ : Fin trcD.length)] =
          (⟨Sum.inr (Sum.inl t1), t2⟩ : Entry) from rfl] at hcase
        rcases hcase with ⟨s, h | ⟨s2, h⟩⟩
        · have hinj' := (Sigma.mk.injEq _ _ _ _).mp h
          have hcontra : t1 = t3 := by simpa using hinj'.1
          revert hcontra
          decide
        · exact absurd (congrArg Sigma.fst h) (by simp)

/-- **The in-tree `Lemma5_14HonestFalseStatement` is FALSE** (at `StmtIn := Unit`,
`U := UInt8`, sponge width 2 / rate 1): two alternating-pair loop chains end at the
same state while the combined bad event `E` is absent — the fork event
`E_fork_honest` fires off `E`. Statement repair of `redundantEntryDS`
(opposite-direction certificates, CO25 Def. 5.5) is required before the full
Lemma 5.14 can be discharged, exactly as for the refuted `Lemma5_16HonestFalseAsStated`. -/
theorem lemma5_14HonestFalseStatement_false :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.Lemma5_14HonestFalseStatement Unit UInt8 := by
  intro h
  exact h trcF t1 famF not_E_trcF e_fork_holds

end DuplexSpongeFS.Sponge316.ForkCounter

#print axioms DuplexSpongeFS.Sponge316.ForkCounter.e_fork_holds
#print axioms DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF
#print axioms DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestFalseStatement_false
