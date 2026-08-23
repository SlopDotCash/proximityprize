/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HashHalf

/-!
# #316 — `Lemma5_16HonestFalseAsStated` is FALSE as stated: a machine-checked countermodel

The in-tree `redundantEntryDS` (BadEvents.lean) deviates from CO25 Definition 5.5: it
accepts a **same-direction swapped** forward entry `(p, y, x)` as a redundancy certificate
for `(p, x, y)`, where the paper uses the **opposite-direction** entry `(p⁻¹, y, x)`. With
the in-tree dedup, a backtrack chain can traverse a single permutation pair in *both*
directions (an "alternating" chain segment), and the dedup'd trace then keeps only one
orientation of that pair — carrying the chain-link capacity on its **query** side, where
none of the `capacitySegmentDup*` anchors (which all anchor on **answer**-side capacities)
can fire. This lets the out-of-order-permutation event `E_time_p_honest` occur while the
combined bad event `E` does not, refuting `Lemma5_16HonestFalseAsStated` as stated.

## The countermodel

`U := UInt8`, `SpongeSize := {N := 2, R := 1}` (capacities are single bytes).
States `(rate, cap)`: `sB = (1,1)`, `sA = (0,2)`, `sa = (2,1)`, `sb = (0,3)`,
target `sT = (1,3)`.

Raw trace (4 entries, in order):
0. `(h, (), [1])` — hash anchor, capacity `1 = cap sB`;
1. `(p, sa, sb)` — the *later* chain step's forward query, **early in the trace**;
2. `(p, sB, sA)` — one orientation of the alternating pair `{sB, sA}`;
3. `(p, sA, sB)` — the other orientation; **in-tree-redundant** w.r.t. entry 2.

Backtrack chain ending at `sT`: `inputState = [sB, sA, sa, sT]`,
`outputState = [sA, sB, sb]` (steps `sB→sA`, `sA→sB`, `sa→sb`); all five Definition 5.3
side conditions hold.

* **`E_time_p` fires**: the first-occurrence index of step 1's pair `(sA, sB)` is `3`,
  while step 2's pair `(sa, sb)` sits at index `1 < 3` — an out-of-order permutation pair.
* **`E` does not fire**: the dedup'd trace is `[hash(1), (p,sa,sb), (p,sB,sA)]`; the only
  answer-side capacities are `3` (`sb`) and `2` (`sA`), each occurring once and matching
  no earlier hash/permutation capacity; the duplicated capacity `1` occurs only on
  *query* sides (`sa`, `sB`) and the hash, in hash-first order. No
  `capacitySegmentDupHash/Perm/PermInv` anchor or `notFunction` witness exists.

Under the paper's Definition 5.5, entry 3 would NOT be redundant, both orientations of
`{sA, sB}` would survive dedup, and the answer capacity `1` of entry 3 would collide with
the earlier hash capacity, firing `E` — so this countermodel is *specific to the in-tree
dedup*; the one-token statement repair (`.inl ↦ .inr` in the swapped certificates of
`redundantEntryDS`) is the prerequisite for the honest Lemma 5.16 (and the same caveat
applies to the `E_fork` analysis of Lemma 5.14).
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

namespace DuplexSpongeFS.Sponge316.TimePCounter

/-- Tiny sponge geometry: width 2, rate 1, capacity 1 — capacities are single `UInt8`s. -/
instance smallSponge : SpongeSize := { N := 2, R := 1 }

/-- States are `Vector UInt8 2 = (rate, cap)`. -/
abbrev St : Type := CanonicalSpongeState UInt8

def mkSt (r c : UInt8) : St := #v[r, c]

def sB : St := mkSt 1 1
def sA : St := mkSt 0 2
def sa : St := mkSt 2 1
def sb : St := mkSt 0 3
def sT : St := mkSt 1 3

abbrev Entry := OracleSpec.duplexSpongeTraceEntry (StartType := Unit) (U := UInt8)

def eH : Entry := ⟨Sum.inl (), #v[1]⟩
def e1 : Entry := ⟨Sum.inr (Sum.inl sa), sb⟩
def e2 : Entry := ⟨Sum.inr (Sum.inl sB), sA⟩
def e3 : Entry := ⟨Sum.inr (Sum.inl sA), sB⟩

/-- The raw countermodel trace. -/
def trc : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, e1, e2, e3]

/-- The dedup'd trace: entry 3 (`(p, sA, sB)`) is in-tree-redundant w.r.t. entry 2. -/
def trc' : QueryLog (duplexSpongeChallengeOracle Unit UInt8) := [eH, e1, e2]

/-- The backtrack chain `sB → sA → sB`, then `sa → sb`, ending at `sT`. -/
def seqC : DuplexSpongeFS.Backtrack.BacktrackSequence trc sT where
  stmt := ()
  inputState := [sB, sA, sa, sT]
  outputState := [sA, sB, sb]
  inputState_length_eq_outputState_length_succ := rfl
  last_inputState_eq_state := rfl
  hash_in_trace := List.Mem.head _
  permute_or_inv_in_trace := by
    intro i
    fin_cases i
    · exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · exact Or.inl (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    · exact Or.inl (List.Mem.tail _ (List.Mem.head _))
  capacitySegment_output_eq_input := by decide
  capacitySegment_input_ne_output := by decide

/-- The singleton backtrack family `{seqC}` (maximality is vacuous). -/
def famC : DuplexSpongeFS.Backtrack.S_BT trc sT where
  seqFamily := {seqC}
  maximality := by
    intro s hs s' hs' hne
    rw [Finset.mem_singleton] at hs hs'
    exact absurd (hs.trans hs'.symm) hne

/-! ## Index computation: the chain's first-occurrence indices are out of order -/

/-- Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`. -/
lemma slots_pair_ASB (v : ℕ) (hv : v < trc.length)
    (h : trc[v] = (⟨Sum.inr (Sum.inl sA), sB⟩ : Entry) ∨
         trc[v] = (⟨Sum.inr (Sum.inr sB), sA⟩ : Entry)) : v = 3 := by
  have hv4 : v < 4 := hv
  interval_cases v <;>
    simp_all [trc, eH, e1, e2, e3, sA, sB, sa, sb, mkSt]

/-- Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`. -/
lemma slots_pair_asb (v : ℕ) (hv : v < trc.length)
    (h : trc[v] = (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) ∨
         trc[v] = (⟨Sum.inr (Sum.inr sb), sa⟩ : Entry)) : v = 1 := by
  have hv4 : v < 4 := hv
  interval_cases v <;>
    simp_all [trc, eH, e1, e2, e3, sA, sB, sa, sb, mkSt]

/-- The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`. -/
lemma index_step1 (hpf : (1 : ℕ) < seqC.inputState.length) :
    ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index trc sT seqC).2
      ⟨1, hpf⟩).val = 3 := by
  have hpair : (1 : ℕ) < seqC.outputState.length := by norm_num [seqC]
  have h := DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
    (trace := trc) (state := sT) (seq := seqC) (pairIdx := ⟨1, hpf⟩) hpair
  set v := ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index trc sT seqC).2
    ⟨1, hpf⟩).val with hvdef
  have hvlt : v < trc.length := by
    rcases h with h | h
    · exact (List.getElem?_eq_some_iff.mp h).1
    · exact (List.getElem?_eq_some_iff.mp h).1
  refine slots_pair_ASB v hvlt ?_
  rcases h with h | h
  · rw [List.getElem?_eq_getElem hvlt] at h
    exact Or.inl (by simpa [seqC] using Option.some.inj h)
  · rw [List.getElem?_eq_getElem hvlt] at h
    exact Or.inr (by simpa [seqC] using Option.some.inj h)

/-- The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`. -/
lemma index_step2 (hpf : (1 + 1 : ℕ) < seqC.inputState.length) :
    ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index trc sT seqC).2
      ⟨1 + 1, hpf⟩).val = 1 := by
  have hpair : (1 + 1 : ℕ) < seqC.outputState.length := by norm_num [seqC]
  have h := DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
    (trace := trc) (state := sT) (seq := seqC) (pairIdx := ⟨1 + 1, hpf⟩) hpair
  set v := ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index trc sT seqC).2
    ⟨1 + 1, hpf⟩).val with hvdef
  have hvlt : v < trc.length := by
    rcases h with h | h
    · exact (List.getElem?_eq_some_iff.mp h).1
    · exact (List.getElem?_eq_some_iff.mp h).1
  refine slots_pair_asb v hvlt ?_
  rcases h with h | h
  · rw [List.getElem?_eq_getElem hvlt] at h
    exact Or.inl (by simpa [seqC] using Option.some.inj h)
  · rw [List.getElem?_eq_getElem hvlt] at h
    exact Or.inr (by simpa [seqC] using Option.some.inj h)

/-- The out-of-order-permutation event fires on the countermodel. -/
theorem e_time_p_holds :
    DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest trc sT famC := by
  classical
  refine ⟨⟨seqC, DuplexSpongeFS.Backtrack.BacktrackSequence.Index trc sT seqC⟩, ?_, ?_⟩
  · unfold DuplexSpongeFS.Backtrack.J_BT
    rw [Finset.mem_image]
    exact ⟨seqC, Finset.mem_singleton_self seqC, rfl⟩
  · refine ⟨⟨1, by norm_num [seqC]⟩, ?_⟩
    rw [index_step1, index_step2]
    omega

/-! ## The dedup'd trace and the absence of the combined bad event `E` -/

/-- Entry 3 is in-tree-redundant: entry 2 is its same-direction swapped certificate. -/
lemma redundant_three (h3 : 3 < trc.length) : trc.redundantEntryDS ⟨3, h3⟩ := by
  refine ⟨⟨2, by norm_num [trc]⟩, by simp [Fin.lt_def], Or.inr rfl⟩

/-- No slot of `trc` other than `3` is redundant. -/
lemma redundant_only_three (idx : Fin trc.length) (hred : trc.redundantEntryDS idx) :
    idx.val = 3 := by
  obtain ⟨v, hv⟩ := idx
  have hv4 : v < 4 := hv
  interval_cases v
  · -- hash at 0: no prior slot
    obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · -- (p, sa, sb) at 1: slot 0 is a hash entry
    obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trc[(⟨0, hw⟩ : Fin trc.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · -- (p, sB, sA) at 2: slots 0/1 hold neither orientation
    obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw01 with h0 | h1
    · subst h0
      rw [show trc[(⟨0, hw⟩ : Fin trc.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trc[(⟨1, hw⟩ : Fin trc.length)] = e1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
  · rfl

/-- No slot of the 3-entry trace `trc'` is redundant. -/
lemma trc'_noRedundant : ∀ idx : Fin trc'.length, ¬ trc'.redundantEntryDS idx := by
  intro idx hred
  obtain ⟨v, hv⟩ := idx
  have hv3 : v < 3 := hv
  interval_cases v
  · obtain ⟨j', hj', -⟩ := hred
    exact absurd hj' (by simp [Fin.lt_def])
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
    subst hw0
    rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hcase
    rcases hcase with h | h <;>
      exact absurd (congrArg Sigma.fst h) (by decide)
  · obtain ⟨⟨w, hw⟩, hj', hcase⟩ := hred
    have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
    rcases hw01 with h0 | h1
    · subst h0
      rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)
    · subst h1
      rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hcase
      rcases hcase with h | h <;>
        exact absurd (congrArg Sigma.fst h) (by decide)

/-- The dedup fixpoint of the countermodel trace is `trc'` (erase slot 3, then stop). -/
lemma dedup_eq : (removeRedundantEntryDS trc).1 = trc' := by
  have hex : ∃ idx : Fin trc.length, trc.redundantEntryDS idx :=
    ⟨⟨3, by norm_num [trc]⟩, redundant_three _⟩
  rw [removeRedundantEntryDS]
  split
  · rename_i hex2
    have hch : (Classical.choose hex2).val = 3 :=
      redundant_only_three _ (Classical.choose_spec hex2)
    rw [hch, show trc.eraseIdx 3 = trc' from rfl]
    rw [removeRedundantEntryDS]
    split
    · rename_i hex3
      obtain ⟨i, hi⟩ := hex3
      exact absurd hi (trc'_noRedundant i)
    · rfl
  · rename_i hnone
    exact absurd hex hnone

/-- Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events. -/
lemma dedup_eq' : removeRedundantEntryDS trc = ⟨trc', trc'_noRedundant⟩ :=
  Subtype.ext dedup_eq

/-! ### `E` is absent

All `capacitySegmentDup*` anchors require an **answer**-side capacity. On `trc'` the
answer capacities are `cap sb = 3` (slot 1) and `cap sA = 2` (slot 2); the hash capacity
is `1`; the query capacities are `1` (`sa`, `sB`). No anchor finds an earlier-or-equal
matching touch. -/

/-- The combined bad event `E` does NOT fire on the countermodel trace. -/
theorem not_E_trc : ¬ BadEventDS.E trc := by
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
    · rw [show trc'[(⟨1, hv⟩ : Fin trc'.length)] = e1 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [e1])
    · rw [show trc'[(⟨2, hv⟩ : Fin trc'.length)] = e2 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [e2])
  · -- E_p: forward anchors at slots 1 (ans cap 3) and 2 (ans cap 2)
    unfold capacitySegmentDupPerm at hp
    rw [dedup_eq'] at hp
    obtain ⟨j, capSeg, ⟨sIn, sOut, hj, hcap⟩, hdisj⟩ := hp
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · -- slot 0 is the hash, not a forward entry
      rw [show trc'[(⟨0, hv⟩ : Fin trc'.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · -- anchor (p, sa, sb): capSeg = cap sb = [3]
      rw [show trc'[(⟨1, hv⟩ : Fin trc'.length)] =
        (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = sa := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hsOut : sOut = sb := by simpa [eq_comm] using eq_of_heq hinj.2
      subst hsOut
      subst hcap
      rcases hdisj with ⟨⟨w, hw⟩, hwlt, stmt', hbad⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩
      -- disjunct 1: earlier hash with capSeg = cap sb = [3]: hash cap is [1]
      · have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hwlt; omega
        subst hw0
        rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = (⟨Sum.inl (), #v[1]⟩ : Entry)
          from rfl] at hbad
        have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
        exact absurd (show (#v[1] : Vector UInt8 SpongeSize.C) =
          CanonicalSpongeState.capacitySegment sb from eq_of_heq hinj'.2) (by decide)
      -- disjunct 2: earlier forward with answer-cap [3]: slot 0 is a hash
      · have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hwlt; omega
        subst hw0
        rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
        exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
      -- disjunct 3: earlier-or-equal inverse: none exist
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e1])
      -- disjunct 4: earlier-or-equal forward with query-cap [3]: query caps are [1]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] =
            (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = sa := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
      -- disjunct 5: earlier-or-equal inverse: none exist
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e1])
    · -- anchor (p, sB, sA): capSeg = cap sA = [2]
      rw [show trc'[(⟨2, hv⟩ : Fin trc'.length)] =
        (⟨Sum.inr (Sum.inl sB), sA⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = sB := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hsOut : sOut = sA := by simpa [eq_comm] using eq_of_heq hinj.2
      subst hsOut
      subst hcap
      rcases hdisj with ⟨⟨w, hw⟩, hwlt, stmt', hbad⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ | ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩ |
        ⟨⟨w, hw⟩, hwlt, s1, s2, hbad, hc⟩
      -- disjunct 1: earlier hash with capSeg = cap sA = [2]: hash cap is [1]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = (⟨Sum.inl (), #v[1]⟩ : Entry)
            from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          exact absurd (show (#v[1] : Vector UInt8 SpongeSize.C) =
            CanonicalSpongeState.capacitySegment sA from eq_of_heq hinj'.2) (by decide)
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e1])
      -- disjunct 2: earlier forward answer-caps: cap sb = [3] ≠ [2]
      · have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hwlt; omega
        rcases hw01 with h0 | h1
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] =
            (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = sa := by simpa [eq_comm] using hinj'.1
          subst hs1
          have hs2 : s2 = sb := by simpa [eq_comm] using eq_of_heq hinj'.2
          rw [hs2] at hc
          revert hc
          decide
      -- disjunct 3: inverse entries: none exist
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e1])
        · subst h2
          rw [show trc'[(⟨2, hw⟩ : Fin trc'.length)] = e2 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e2])
      -- disjunct 4: forward query-caps: cap sa = cap sB = [1] ≠ [2]
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] =
            (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = sa := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
        · subst h2
          rw [show trc'[(⟨2, hw⟩ : Fin trc'.length)] =
            (⟨Sum.inr (Sum.inl sB), sA⟩ : Entry) from rfl] at hbad
          have hinj' := (Sigma.mk.injEq _ _ _ _).mp hbad
          have hs1 : s1 = sB := by simpa [eq_comm] using hinj'.1
          rw [hs1] at hc
          revert hc
          decide
      -- disjunct 5: inverse entries: none exist
      · have hw012 : w = 0 ∨ w = 1 ∨ w = 2 := by have := Fin.mk_le_mk.mp hwlt; omega
        rcases hw012 with h0 | h1 | h2
        · subst h0
          rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [eH])
        · subst h1
          rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] = e1 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e1])
        · subst h2
          rw [show trc'[(⟨2, hw⟩ : Fin trc'.length)] = e2 from rfl] at hbad
          exact absurd (congrArg Sigma.fst hbad) (by simp [e2])
  · -- E_pinv: no inverse entries exist in the dedup'd trace
    unfold capacitySegmentDupPermInv at hpinv
    rw [dedup_eq'] at hpinv
    obtain ⟨j, capSeg, ⟨sOut, sIn, hj, -⟩, -⟩ := hpinv
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · rw [show trc'[(⟨0, hv⟩ : Fin trc'.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · rw [show trc'[(⟨1, hv⟩ : Fin trc'.length)] = e1 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [e1])
    · rw [show trc'[(⟨2, hv⟩ : Fin trc'.length)] = e2 from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [e2])
  · -- E_func: the two forward queries sa, sB are distinct; no inverse entries
    unfold notFunction at hfunc
    rw [dedup_eq'] at hfunc
    obtain ⟨j, sIn, sOut, hj, ⟨w, hw⟩, hj', hcase⟩ := hfunc
    obtain ⟨v, hv⟩ := j
    have hv3 : v < 3 := hv
    interval_cases v
    · rw [show trc'[(⟨0, hv⟩ : Fin trc'.length)] = eH from rfl] at hj
      exact absurd (congrArg Sigma.fst hj) (by simp [eH])
    · -- anchor (p, sa, sb): only earlier slot is the hash
      rw [show trc'[(⟨1, hv⟩ : Fin trc'.length)] =
        (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = sa := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hw0 : w = 0 := by have := Fin.mk_lt_mk.mp hj'; omega
      subst hw0
      rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hcase
      rcases hcase with ⟨s, h | ⟨s2, h⟩⟩ <;>
        exact absurd (congrArg Sigma.fst h) (by simp [eH])
    · -- anchor (p, sB, sA): earlier slots are the hash and (p, sa, ·) with sa ≠ sB
      rw [show trc'[(⟨2, hv⟩ : Fin trc'.length)] =
        (⟨Sum.inr (Sum.inl sB), sA⟩ : Entry) from rfl] at hj
      have hinj := (Sigma.mk.injEq _ _ _ _).mp hj
      have hsIn : sIn = sB := by simpa [eq_comm] using hinj.1
      subst hsIn
      have hw01 : w = 0 ∨ w = 1 := by have := Fin.mk_lt_mk.mp hj'; omega
      rcases hw01 with h0 | h1
      · subst h0
        rw [show trc'[(⟨0, hw⟩ : Fin trc'.length)] = eH from rfl] at hcase
        rcases hcase with ⟨s, h | ⟨s2, h⟩⟩ <;>
          exact absurd (congrArg Sigma.fst h) (by simp [eH])
      · subst h1
        rw [show trc'[(⟨1, hw⟩ : Fin trc'.length)] =
          (⟨Sum.inr (Sum.inl sa), sb⟩ : Entry) from rfl] at hcase
        rcases hcase with ⟨s, h | ⟨s2, h⟩⟩
        · have hinj' := (Sigma.mk.injEq _ _ _ _).mp h
          have hcontra : sa = sB := by simpa using hinj'.1
          revert hcontra
          decide
        · exact absurd (congrArg Sigma.fst h) (by simp)

/-- **The in-tree `Lemma5_16HonestFalseAsStated` is FALSE** (at `StmtIn := Unit`,
`U := UInt8`, sponge width 2 / rate 1): the countermodel trace realizes
`E_time_p_honest` while the combined bad event `E` is absent. Statement repair of
`redundantEntryDS` (opposite-direction certificates, CO25 Def. 5.5) is required before
the full Lemma 5.16 can be discharged. -/
theorem lemma5_16HonestFalseAsStated_false :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated Unit UInt8 := by
  intro h
  exact h trc sT famC not_E_trc (Or.inr e_time_p_holds)

end DuplexSpongeFS.Sponge316.TimePCounter

#print axioms DuplexSpongeFS.Sponge316.TimePCounter.e_time_p_holds
#print axioms DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc
#print axioms DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestFalseAsStated_false
