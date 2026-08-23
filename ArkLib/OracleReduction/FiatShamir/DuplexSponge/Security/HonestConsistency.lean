/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

set_option linter.style.longFile 2000

/-!
# #316 — Duplex-Sponge Fiat-Shamir: discharge of the M2a honest bad-event residual
`DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual`
(CO25 Lemma 5.12, honest form: `¬E(tr) → ¬E_inv_honest(tr, s, S)`).

Route (all new content, no probability needed):

1. `hasInvEntry_eraseIdx` — erasing one *redundant* entry preserves "the trace contains an
   inverse-permutation (`p⁻¹`) entry": if the erased slot holds the witness, its redundancy
   certificate (`redundantEntryDS`, third arm) is itself an **earlier inverse entry**, which
   survives the erasure; otherwise the witness occurrence survives (index-shifted).
2. `hasInvEntry_removeRedundant` — hence the dedup fixpoint `removeRedundantEntryDS`
   preserves it (strong induction on the trace length through the WF recursion).
3. `capacitySegmentDupPermInv_of_inv_mem` — any inverse entry in the dedup'd trace fires
   `E_pinv`: its 5th disjunct allows `j' ≤ j` with the *answer*-capacity condition, which
   **self-matches at `j' = j`** (the answer's capacity equals itself).
4. `hasInvEntry_implies_E` — keystone: an inverse entry anywhere in the *raw* trace fires the
   combined bad event `E`. Contrapositive: `¬E(tr)` ⟹ the raw trace has **no** `p⁻¹ entries.
5. `lemma5_12_honest` — `E_inv_honest` exhibits a `p⁻¹` entry at a raw-trace index
   (`tr[·]? = some ⟨.inr (.inr _), _⟩`); contradiction with the keystone.

NOTE on strength: step 3 leans on the in-tree `capacitySegmentDupPermInv` being
self-firing on every inverse entry (its `j' ≤ j` answer-side disjunct). This is the
*in-tree* CO25 Eq. 39 rendering that the residual is stated against; the discharge is
therefore exact for the in-tree statement.
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

namespace DuplexSpongeFS.Sponge316

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- The trace contains an inverse-permutation (`p⁻¹`) entry. -/
def HasInvEntry (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ sOut sIn : CanonicalSpongeState U,
    (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
      (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
        (duplexSpongeChallengeOracle StmtIn U).Range t) ∈ tr

/-- Membership from an `getElem?`-hit. -/
private lemma mem_of_getElem?' {α : Type _} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hlt

omit [SpongeSize] in
private lemma get_eraseIdx_before {α : Type _} (l : List α) (idx k : Fin l.length)
    (h : k.val < idx.val) :
    (l.eraseIdx idx.val).get ⟨k.val, by
      have hlen := List.length_eraseIdx_add_one idx.isLt
      omega⟩ = l.get k := by
  have hkeep : (l.eraseIdx idx.val)[k.val]? = l[k.val]? :=
    List.getElem?_eraseIdx_of_lt h
  have hnew : (l.eraseIdx idx.val)[k.val]? =
      some ((l.eraseIdx idx.val).get ⟨k.val, by
        have hlen := List.length_eraseIdx_add_one idx.isLt
        omega⟩) := by
    exact List.getElem?_eq_getElem (l := l.eraseIdx idx.val) (i := k.val) (by
      have hlen := List.length_eraseIdx_add_one idx.isLt
      omega)
  have hold : l[k.val]? = some l[k] := by
    simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := l) k.isLt
  rw [hnew, hold] at hkeep
  exact Option.some.inj hkeep

omit [SpongeSize] in
private lemma get_eraseIdx_after {α : Type _} (l : List α) (idx k : Fin l.length)
    (h : idx.val < k.val) :
    (l.eraseIdx idx.val).get ⟨k.val - 1, by
      have hlen := List.length_eraseIdx_add_one idx.isLt
      omega⟩ = l.get k := by
  have hkeep : (l.eraseIdx idx.val)[k.val - 1]? = l[(k.val - 1) + 1]? :=
    List.getElem?_eraseIdx_of_ge (l := l) (i := idx.val) (j := k.val - 1) (by omega)
  have hnew : (l.eraseIdx idx.val)[k.val - 1]? =
      some ((l.eraseIdx idx.val).get ⟨k.val - 1, by
        have hlen := List.length_eraseIdx_add_one idx.isLt
        omega⟩) := by
    exact List.getElem?_eq_getElem (l := l.eraseIdx idx.val) (i := k.val - 1) (by
      have hlen := List.length_eraseIdx_add_one idx.isLt
      omega)
  have hold : l[(k.val - 1) + 1]? = some l[k] := by
    have hk : k.val - 1 + 1 = k.val := by omega
    rw [hk]
    simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := l) k.isLt
  rw [hnew, hold] at hkeep
  exact Option.some.inj hkeep

/-- The trace contains a concrete hash entry. -/
def HasHashEntry (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  (⟨Sum.inl stmt, capSeg⟩ :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) ∈ tr

/-- The trace contains a hash entry with a strictly earlier forward permutation entry sharing the
hash capacity on either the forward output or forward input side. This is the concrete collision
shape used by `capacitySegmentDupHash`. -/
def HasForwardCapacityBeforeHash
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  ∃ jHash : Fin tr.length,
    tr[jHash] =
      (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
    ∃ jPerm : Fin tr.length, jPerm < jHash ∧
      ∃ stateIn stateOut : CanonicalSpongeState U,
        tr[jPerm] =
          (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
            OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
        (stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg)

/-- The trace contains a forward permutation entry whose output capacity matches the input
capacity of a strictly earlier forward permutation entry. This is the base-trace collision shape
for the permutation-ordering half of M2c. -/
def HasInputCapacityBeforeForwardOutput
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ jCur : Fin tr.length,
    ∃ stateIn stateOut : CanonicalSpongeState U,
      tr[jCur] =
        (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      ∃ jPrev : Fin tr.length, jPrev < jCur ∧
        ∃ prevIn prevOut : CanonicalSpongeState U,
          tr[jPrev] =
            (⟨Sum.inr (Sum.inl prevIn), prevOut⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
          prevIn.capacitySegment = stateOut.capacitySegment

/-- The trace contains a forward permutation entry whose output capacity matches either side of a
strictly earlier forward permutation entry. This is the preservation-friendly base-trace shape for
the permutation-ordering half of M2c: if a redundant earlier forward entry is replaced by a
reversed forward witness, the matching capacity can move from input side to output side. -/
def HasForwardCapacityBeforeForwardOutput
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ jCur : Fin tr.length,
    ∃ stateIn stateOut : CanonicalSpongeState U,
      tr[jCur] =
        (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      ∃ jPrev : Fin tr.length, jPrev < jCur ∧
        ∃ prevIn prevOut : CanonicalSpongeState U,
          tr[jPrev] =
            (⟨Sum.inr (Sum.inl prevIn), prevOut⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
          (prevOut.capacitySegment = stateOut.capacitySegment ∨
            prevIn.capacitySegment = stateOut.capacitySegment)

/-- The input-side-only permutation-ordering shape is a special case of the broader
preservation-friendly shape. -/
theorem hasForwardCapacityBeforeForwardOutput_of_input
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasInputCapacityBeforeForwardOutput tr) :
    HasForwardCapacityBeforeForwardOutput tr := by
  obtain ⟨jCur, stateIn, stateOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  exact ⟨jCur, stateIn, stateOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, Or.inr hcap⟩

/-- Strengthened raw collision shape: the hash entry is the first occurrence of its concrete hash
anchor, and a strictly earlier forward entry shares the hash capacity. This is the preservation
shape needed for `removeRedundantEntryDS`. -/
def HasFirstHashForwardCapacityBeforeHash
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  ∃ jHash : Fin tr.length,
    tr[jHash] =
      (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
    (∀ j : Fin tr.length, j.val < jHash.val →
      tr[j] ≠
        (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
    ∃ jPerm : Fin tr.length, jPerm < jHash ∧
      ∃ stateIn stateOut : CanonicalSpongeState U,
        tr[jPerm] =
          (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
            OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
        (stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg)

/-- Forgetting the first-occurrence guard leaves the ordinary forward-before-hash capacity shape. -/
theorem hasForwardCapacityBeforeHash_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    HasForwardCapacityBeforeHash tr stmt capSeg := by
  obtain ⟨jHash, hhash, _hfirst, jPerm, hlt, stateIn, stateOut, hperm, hcap⟩ := h
  exact ⟨jHash, hhash, jPerm, hlt, stateIn, stateOut, hperm, hcap⟩

/-- Inversion of `redundantEntryDS` at a forward-permutation slot: the redundancy certificate
is an earlier forward entry with either the same state pair or the reversed state pair. -/
private lemma redundantEntryDS_forward_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stateIn stateOut : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inl stateOut), stateIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- A redundant forward entry that shares a target capacity has an earlier forward replacement
that still shares that capacity, possibly on the opposite side after the state pair is reversed. -/
theorem redundant_forward_capacity_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {capSeg : Vector U SpongeSize.C} {stateIn stateOut : CanonicalSpongeState U}
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hred : tr.redundantEntryDS idx)
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    ∃ j' : Fin tr.length, j' < idx ∧
      ∃ stateIn' stateOut' : CanonicalSpongeState U,
        tr[j'] =
          (⟨Sum.inr (Sum.inl stateIn'), stateOut'⟩ :
            OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
        (stateOut'.capacitySegment = capSeg ∨ stateIn'.capacitySegment = capSeg) := by
  obtain ⟨j', hj', hcase⟩ :=
    redundantEntryDS_forward_inversion tr idx stateIn stateOut hval hred
  refine ⟨j', hj', ?_⟩
  rcases hcase with hsame | hrev
  · exact ⟨stateIn, stateOut, hsame, hcap⟩
  · rcases hcap with hout | hin
    · exact ⟨stateOut, stateIn, hrev, Or.inr hout⟩
    · exact ⟨stateOut, stateIn, hrev, Or.inl hin⟩

/-- Inversion of `redundantEntryDS` at a hash slot: the redundancy certificate is an earlier
copy of the same hash entry. -/
private lemma redundantEntryDS_hash_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
    (hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      tr[j'] = (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- **One-step preservation**: erasing a redundant entry preserves a concrete hash entry. -/
private lemma hasHashEntry_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hP : HasHashEntry tr stmt capSeg) :
    HasHashEntry (tr.eraseIdx idx.val) stmt capSeg := by
  classical
  unfold HasHashEntry at hP ⊢
  by_cases hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)
  · obtain ⟨j', hj', hentry⟩ :=
      redundantEntryDS_hash_inversion tr idx stmt capSeg hval hred
    have hj'idx : j'.val < idx.val := hj'
    have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
      List.getElem?_eraseIdx_of_lt hj'idx
    have hhit : tr[j'.val]? = some tr[j'] := by
      simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := tr) j'.isLt
    exact mem_of_getElem?' (by rw [hkeep, hhit, hentry])
  · rw [List.mem_iff_getElem] at hP
    obtain ⟨p, hp, hpe⟩ := hP
    have hpne : p ≠ idx.val := by
      intro hcontr
      apply hval
      calc tr[idx] = tr[p]'hp := by
            subst hcontr; rfl
        _ = _ := hpe
    have hp? : tr[p]? = some
        (⟨Sum.inl stmt, capSeg⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) := by
      rw [List.getElem?_eq_getElem hp, hpe]
    rcases Nat.lt_or_ge p idx.val with hlt | hge
    · exact mem_of_getElem?' (i := p) (by rw [List.getElem?_eraseIdx_of_lt hlt, hp?])
    · have hgt : idx.val < p := lt_of_le_of_ne hge (Ne.symm hpne)
      exact mem_of_getElem?' (i := p - 1) (by
        rw [List.getElem?_eraseIdx_of_ge (by omega), show p - 1 + 1 = p by omega, hp?])

/-- **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete
hash entries. -/
private lemma hasHashEntry_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {stmt : StmtIn} {capSeg : Vector U SpongeSize.C},
        HasHashEntry tr stmt capSeg → HasHashEntry (removeRedundantEntryDS tr).1 stmt capSeg := by
  intro N
  induction N with
  | zero =>
      intro tr hlen stmt capSeg hP
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hP
      simp [HasHashEntry] at hP
  | succ N ih =>
      intro tr hlen stmt capSeg hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (hasHashEntry_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the
deduplicated trace still contains that same hash entry. -/
theorem hasHashEntry_removeRedundant_of_mem
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasHashEntry tr stmt capSeg) :
    HasHashEntry (removeRedundantEntryDS tr).1 stmt capSeg :=
  hasHashEntry_removeRedundant tr.length tr le_rfl h

/-- Private shorthand for a concrete hash query-answer entry. -/
private def hashEntry (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inl stmt, capSeg⟩

/-- Private shorthand for a concrete forward permutation query-answer entry. -/
private def forwardEntry (stateIn stateOut : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inl stateIn), stateOut⟩

/-- Natural-index form of `HasFirstHashForwardCapacityBeforeHash`, used for the recursive
`eraseIdx` proof where indices may shift left. -/
private def HasFirstHashForwardCapacityBeforeHashNat
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  ∃ iHash iPerm : ℕ, ∃ stateIn stateOut : CanonicalSpongeState U,
    iPerm < iHash ∧
      tr[iHash]? = some (hashEntry stmt capSeg) ∧
      tr[iPerm]? = some (forwardEntry stateIn stateOut) ∧
      (stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) ∧
      ∀ j, j < iHash → tr[j]? ≠ some (hashEntry stmt capSeg)

/-- Convert the public finite-index first-hash witness into the private natural-index form. -/
private lemma firstNat_of_first
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    HasFirstHashForwardCapacityBeforeHashNat tr stmt capSeg := by
  obtain ⟨jHash, hhash, hfirst, jPerm, hlt, stateIn, stateOut, hperm, hcap⟩ := h
  have hhash? : tr[jHash.val]? = some (hashEntry stmt capSeg) := by
    rw [List.getElem?_eq_getElem jHash.isLt]
    simpa [hashEntry] using congrArg some hhash
  have hperm? : tr[jPerm.val]? = some (forwardEntry stateIn stateOut) := by
    rw [List.getElem?_eq_getElem jPerm.isLt]
    simpa [forwardEntry] using congrArg some hperm
  have hfirstNat : ∀ j, j < jHash.val → tr[j]? ≠ some (hashEntry stmt capSeg) := by
    intro j hj hsome
    have hjlen : j < tr.length := lt_trans hj jHash.isLt
    have hraw : tr.get ⟨j, hjlen⟩ =
        (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
      rw [List.getElem?_eq_getElem hjlen] at hsome
      exact Option.some.inj hsome
    exact hfirst ⟨j, hjlen⟩ hj hraw
  exact ⟨jHash.val, jPerm.val, stateIn, stateOut, hlt, hhash?, hperm?, hcap, hfirstNat⟩

/-- Convert the private natural-index witness back to the public base-trace collision shape. -/
private lemma hasForwardCapacityBeforeHash_of_firstNat
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHashNat tr stmt capSeg) :
    HasForwardCapacityBeforeHash tr stmt capSeg := by
  obtain ⟨iHash, iPerm, stateIn, stateOut, hlt, hhash, hperm, hcap, _hfirst⟩ := h
  obtain ⟨hHashLt, hHashEq⟩ := List.getElem?_eq_some_iff.mp hhash
  obtain ⟨hPermLt, hPermEq⟩ := List.getElem?_eq_some_iff.mp hperm
  refine ⟨⟨iHash, hHashLt⟩, ?_, ⟨iPerm, hPermLt⟩, hlt,
    stateIn, stateOut, ?_, hcap⟩
  · simpa [hashEntry] using hHashEq
  · simpa [forwardEntry] using hPermEq

/-- Hash-slot inversion for the private `hashEntry` shorthand. -/
private lemma redundantEntryDS_hashEntry_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
    (hval : tr[idx] = hashEntry stmt capSeg)
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧ tr[j'] = hashEntry stmt capSeg := by
  unfold hashEntry at hval ⊢
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- **One-step preservation**: erasing one redundant entry preserves the strengthened
forward-before-first-hash shape. -/
private lemma firstNat_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hP : HasFirstHashForwardCapacityBeforeHashNat tr stmt capSeg) :
    HasFirstHashForwardCapacityBeforeHashNat (tr.eraseIdx idx.val) stmt capSeg := by
  classical
  obtain ⟨iHash, iPerm, stateIn, stateOut, hlt, hhash, hperm, hcap, hfirst⟩ := hP
  by_cases hEraseHash : idx.val = iHash
  · have hidx? : tr[idx.val]? = some (hashEntry stmt capSeg) := by
      simpa [hEraseHash] using hhash
    have hidxVal : tr[idx] = hashEntry stmt capSeg := by
      rw [List.getElem?_eq_getElem idx.isLt] at hidx?
      exact Option.some.inj hidx?
    obtain ⟨j', hj', hjeq⟩ :=
      redundantEntryDS_hashEntry_inversion tr idx stmt capSeg hidxVal hred
    have hprior? : tr[j'.val]? = some (hashEntry stmt capSeg) := by
      rw [List.getElem?_eq_getElem j'.isLt]
      simpa only [List.get_eq_getElem] using congrArg some hjeq
    exact False.elim (hfirst j'.val (by omega) hprior?)
  · let iHash' := if idx.val < iHash then iHash - 1 else iHash
    have hhash' : (tr.eraseIdx idx.val)[iHash']? = some (hashEntry stmt capSeg) := by
      by_cases hidxHash : idx.val < iHash
      · have hge : idx.val ≤ iHash - 1 := by omega
        simp only [iHash', hidxHash, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_ge hge, show iHash - 1 + 1 = iHash by omega, hhash]
      · have hHashIdx : iHash < idx.val := by omega
        simp only [iHash', hidxHash, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_lt hHashIdx, hhash]
    have hfirst' : ∀ j, j < iHash' →
        (tr.eraseIdx idx.val)[j]? ≠ some (hashEntry stmt capSeg) := by
      intro j hj hsome
      by_cases hidxHash : idx.val < iHash
      · by_cases hjIdx : j < idx.val
        · have hraw : tr[j]? = some (hashEntry stmt capSeg) := by
            rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
            exact hsome
          exact hfirst j (by simp [iHash', hidxHash] at hj; omega) hraw
        · have hraw : tr[j + 1]? = some (hashEntry stmt capSeg) := by
            have hge : idx.val ≤ j := by omega
            rw [List.getElem?_eraseIdx_of_ge hge] at hsome
            exact hsome
          exact hfirst (j + 1) (by simp [iHash', hidxHash] at hj; omega) hraw
      · have hHashIdx : iHash < idx.val := by omega
        have hjIdx : j < idx.val := by simp [iHash', hidxHash] at hj; omega
        have hraw : tr[j]? = some (hashEntry stmt capSeg) := by
          rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
          exact hsome
        exact hfirst j (by simpa [iHash', hidxHash] using hj) hraw
    by_cases hErasePerm : idx.val = iPerm
    · have hidx? : tr[idx.val]? = some (forwardEntry stateIn stateOut) := by
        simpa [hErasePerm] using hperm
      have hidxVal : tr[idx] = forwardEntry stateIn stateOut := by
        rw [List.getElem?_eq_getElem idx.isLt] at hidx?
        exact Option.some.inj hidx?
      obtain ⟨j', hj', stateIn', stateOut', hentry, hcap'⟩ :=
        redundant_forward_capacity_prior
          (tr := tr) (idx := idx) (capSeg := capSeg)
          (stateIn := stateIn) (stateOut := stateOut)
          (by simpa [forwardEntry] using hidxVal) hred hcap
      have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
        List.getElem?_eraseIdx_of_lt (by exact hj')
      have hperm' : (tr.eraseIdx idx.val)[j'.val]? =
          some (forwardEntry stateIn' stateOut') := by
        rw [hkeep, List.getElem?_eq_getElem j'.isLt]
        simpa [forwardEntry, List.get_eq_getElem] using congrArg some hentry
      refine ⟨iHash', j'.val, stateIn', stateOut', ?_, hhash', hperm', hcap', hfirst'⟩
      by_cases hidxHash : idx.val < iHash
      · simp [iHash', hidxHash]; omega
      · omega
    · let iPerm' := if idx.val < iPerm then iPerm - 1 else iPerm
      have hperm' : (tr.eraseIdx idx.val)[iPerm']? = some (forwardEntry stateIn stateOut) := by
        by_cases hidxPerm : idx.val < iPerm
        · have hge : idx.val ≤ iPerm - 1 := by omega
          simp only [iPerm', hidxPerm, ↓reduceIte]
          rw [List.getElem?_eraseIdx_of_ge hge, show iPerm - 1 + 1 = iPerm by omega, hperm]
        · have hPermIdx : iPerm < idx.val := by omega
          simp only [iPerm', hidxPerm, ↓reduceIte]
          rw [List.getElem?_eraseIdx_of_lt hPermIdx, hperm]
      have hlt' : iPerm' < iHash' := by
        by_cases hidxHash : idx.val < iHash
        · by_cases hidxPerm : idx.val < iPerm
          · simp [iHash', iPerm', hidxHash, hidxPerm]; omega
          · simp [iHash', iPerm', hidxHash, hidxPerm]; omega
        · have hHashIdx : iHash < idx.val := by omega
          have hidxPerm : ¬ idx.val < iPerm := by omega
          simp [iHash', iPerm', hidxHash, hidxPerm]; omega
      exact ⟨iHash', iPerm', stateIn, stateOut, hlt', hhash', hperm', hcap, hfirst'⟩

/-- **Fixpoint preservation**: dedup preserves the first-hash forward-capacity collision shape
as the base-trace shape used by `capacitySegmentDupHash`. -/
private lemma firstNat_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {stmt : StmtIn} {capSeg : Vector U SpongeSize.C},
        HasFirstHashForwardCapacityBeforeHashNat tr stmt capSeg →
          HasForwardCapacityBeforeHash (removeRedundantEntryDS tr).1 stmt capSeg := by
  intro N
  induction N with
  | zero =>
      intro tr hlen stmt capSeg hP
      obtain ⟨iHash, _iPerm, _stateIn, _stateOut, _hlt, hhash, _hperm, _hcap, _hfirst⟩ := hP
      have hlen0 : tr.length = 0 := Nat.le_zero.mp hlen
      rw [List.length_eq_zero_iff.mp hlen0] at hhash
      simp [hashEntry] at hhash
  | succ N ih =>
      intro tr hlen stmt capSeg hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (firstNat_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hasForwardCapacityBeforeHash_of_firstNat hP

/-- Public dedup bridge for the M2c hash-timing path: the strengthened raw first-hash witness
survives `removeRedundantEntryDS` as the base-trace `HasForwardCapacityBeforeHash` shape. -/
theorem hasForwardCapacityBeforeHash_removeRedundant_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    HasForwardCapacityBeforeHash (removeRedundantEntryDS tr).1 stmt capSeg :=
  firstNat_removeRedundant tr.length tr le_rfl (firstNat_of_first h)

/-- Strengthened permutation-ordering collision shape: the later forward permutation entry is
the first occurrence of its concrete forward pair up to the same-direction reversal that
`redundantEntryDS` uses for forward slots, and a strictly earlier forward entry shares the later
entry's output capacity on either side. -/
def HasFirstForwardCapacityBeforeForwardOutput
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ jCur : Fin tr.length,
    ∃ stateIn stateOut : CanonicalSpongeState U,
      tr[jCur] = forwardEntry stateIn stateOut ∧
      (∀ j : Fin tr.length, j.val < jCur.val →
        tr[j] ≠ forwardEntry stateIn stateOut ∧
          tr[j] ≠ forwardEntry stateOut stateIn) ∧
      ∃ jPrev : Fin tr.length, jPrev < jCur ∧
        ∃ prevIn prevOut : CanonicalSpongeState U,
          tr[jPrev] = forwardEntry prevIn prevOut ∧
          (prevOut.capacitySegment = stateOut.capacitySegment ∨
            prevIn.capacitySegment = stateOut.capacitySegment)

/-- Forgetting the first-occurrence guard leaves the broad forward-before-forward-output shape. -/
theorem hasForwardCapacityBeforeForwardOutput_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstForwardCapacityBeforeForwardOutput tr) :
    HasForwardCapacityBeforeForwardOutput tr := by
  obtain ⟨jCur, stateIn, stateOut, hcur, _hfirst,
    jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  exact ⟨jCur, stateIn, stateOut, by simpa [forwardEntry] using hcur,
    jPrev, hlt, prevIn, prevOut, by simpa [forwardEntry] using hprev, hcap⟩

/-- A forward slot with no earlier same-or-reversed forward entry is not redundant under the
duplex-sponge dedup predicate. -/
theorem not_redundantEntryDS_forward_of_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {stateIn stateOut : CanonicalSpongeState U}
    (hidx : tr[idx] = forwardEntry stateIn stateOut)
    (hfirst : ∀ j : Fin tr.length, j.val < idx.val →
      tr[j] ≠ forwardEntry stateIn stateOut ∧
        tr[j] ≠ forwardEntry stateOut stateIn) :
    ¬ tr.redundantEntryDS idx := by
  intro hred
  unfold redundantEntryDS at hred
  rw [hidx] at hred
  obtain ⟨j, hjlt, hcase⟩ := hred
  rcases hcase with hsame | hrev
  · exact (hfirst j hjlt).1 hsame
  · exact (hfirst j hjlt).2 hrev

/-- The strong permutation-ordering predicate carries the nonredundancy proof needed for its
later forward anchor. -/
theorem hasFirstForwardCapacityBeforeForwardOutput_current_not_redundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstForwardCapacityBeforeForwardOutput tr) :
    ∃ jCur : Fin tr.length,
      ∃ stateIn stateOut : CanonicalSpongeState U,
        tr[jCur] = forwardEntry stateIn stateOut ∧
        ¬ tr.redundantEntryDS jCur := by
  obtain ⟨jCur, stateIn, stateOut, hcur, hfirst,
    _jPrev, _hlt, _prevIn, _prevOut, _hprev, _hcap⟩ := h
  exact ⟨jCur, stateIn, stateOut, hcur,
    not_redundantEntryDS_forward_of_no_prior tr jCur hcur hfirst⟩

/-- Natural-index form of `HasFirstForwardCapacityBeforeForwardOutput`, used for the recursive
`eraseIdx` proof where indices may shift left. -/
private def HasFirstForwardCapacityBeforeForwardOutputNat
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ iCur iPrev : ℕ,
    ∃ curIn curOut prevIn prevOut : CanonicalSpongeState U,
      iPrev < iCur ∧
      tr[iCur]? = some (forwardEntry curIn curOut) ∧
      tr[iPrev]? = some (forwardEntry prevIn prevOut) ∧
      (prevOut.capacitySegment = curOut.capacitySegment ∨
        prevIn.capacitySegment = curOut.capacitySegment) ∧
      ∀ j, j < iCur →
        tr[j]? ≠ some (forwardEntry curIn curOut) ∧
          tr[j]? ≠ some (forwardEntry curOut curIn)

/-- Convert the public finite-index first-forward witness into the private natural-index form. -/
private lemma firstForwardNat_of_first
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : HasFirstForwardCapacityBeforeForwardOutput tr) :
    HasFirstForwardCapacityBeforeForwardOutputNat tr := by
  obtain ⟨jCur, curIn, curOut, hcur, hfirst,
    jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  have hcur? : tr[jCur.val]? = some (forwardEntry curIn curOut) := by
    rw [List.getElem?_eq_getElem jCur.isLt]
    simpa only [List.get_eq_getElem] using congrArg some hcur
  have hprev? : tr[jPrev.val]? = some (forwardEntry prevIn prevOut) := by
    rw [List.getElem?_eq_getElem jPrev.isLt]
    simpa only [List.get_eq_getElem] using congrArg some hprev
  have hfirstNat : ∀ j, j < jCur.val →
      tr[j]? ≠ some (forwardEntry curIn curOut) ∧
        tr[j]? ≠ some (forwardEntry curOut curIn) := by
    intro j hj
    have hjlen : j < tr.length := lt_trans hj jCur.isLt
    constructor
    · intro hsome
      have hraw : tr.get ⟨j, hjlen⟩ = forwardEntry curIn curOut := by
        rw [List.getElem?_eq_getElem hjlen] at hsome
        exact Option.some.inj hsome
      exact (hfirst ⟨j, hjlen⟩ hj).1 hraw
    · intro hsome
      have hraw : tr.get ⟨j, hjlen⟩ = forwardEntry curOut curIn := by
        rw [List.getElem?_eq_getElem hjlen] at hsome
        exact Option.some.inj hsome
      exact (hfirst ⟨j, hjlen⟩ hj).2 hraw
  exact ⟨jCur.val, jPrev.val, curIn, curOut, prevIn, prevOut, hlt,
    hcur?, hprev?, hcap, hfirstNat⟩

/-- Convert the private natural-index witness back to the public broad base-trace shape. -/
private lemma hasForwardCapacityBeforeForwardOutput_of_firstForwardNat
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : HasFirstForwardCapacityBeforeForwardOutputNat tr) :
    HasForwardCapacityBeforeForwardOutput tr := by
  obtain ⟨iCur, iPrev, curIn, curOut, prevIn, prevOut,
    hlt, hcur, hprev, hcap, _hfirst⟩ := h
  obtain ⟨hCurLt, hCurEq⟩ := List.getElem?_eq_some_iff.mp hcur
  obtain ⟨hPrevLt, hPrevEq⟩ := List.getElem?_eq_some_iff.mp hprev
  refine ⟨⟨iCur, hCurLt⟩, curIn, curOut, ?_,
    ⟨iPrev, hPrevLt⟩, hlt, prevIn, prevOut, ?_, hcap⟩
  · simpa [forwardEntry] using hCurEq
  · simpa [forwardEntry] using hPrevEq

/-- **One-step preservation**: erasing one redundant entry preserves the strengthened
forward-before-first-forward-output shape. -/
private lemma firstForwardNat_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    (hP : HasFirstForwardCapacityBeforeForwardOutputNat tr) :
    HasFirstForwardCapacityBeforeForwardOutputNat (tr.eraseIdx idx.val) := by
  classical
  obtain ⟨iCur, iPrev, curIn, curOut, prevIn, prevOut,
    hlt, hcur, hprev, hcap, hfirst⟩ := hP
  by_cases hEraseCur : idx.val = iCur
  · have hidx? : tr[idx.val]? = some (forwardEntry curIn curOut) := by
      simpa [hEraseCur] using hcur
    have hidxVal : tr[idx] = forwardEntry curIn curOut := by
      rw [List.getElem?_eq_getElem idx.isLt] at hidx?
      exact Option.some.inj hidx?
    have hred' :
        ∃ j' : Fin tr.length, j' < idx ∧
          (tr[j'] = forwardEntry curIn curOut ∨
            tr[j'] = forwardEntry curOut curIn) := by
      unfold redundantEntryDS at hred
      rw [hidxVal] at hred
      simpa [forwardEntry] using hred
    obtain ⟨j', hj', hcase⟩ := hred'
    have hjCur : j'.val < iCur := by omega
    rcases hcase with hsame | hrev
    · have hsome : tr[j'.val]? = some (forwardEntry curIn curOut) := by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hsame
      exact False.elim ((hfirst j'.val hjCur).1 hsome)
    · have hsome : tr[j'.val]? = some (forwardEntry curOut curIn) := by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hrev
      exact False.elim ((hfirst j'.val hjCur).2 hsome)
  · let iCur' := if idx.val < iCur then iCur - 1 else iCur
    have hcur' : (tr.eraseIdx idx.val)[iCur']? = some (forwardEntry curIn curOut) := by
      by_cases hidxCur : idx.val < iCur
      · have hge : idx.val ≤ iCur - 1 := by omega
        simp only [iCur', hidxCur, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_ge hge, show iCur - 1 + 1 = iCur by omega, hcur]
      · have hCurIdx : iCur < idx.val := by omega
        simp only [iCur', hidxCur, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_lt hCurIdx, hcur]
    have hfirst' : ∀ j, j < iCur' →
        (tr.eraseIdx idx.val)[j]? ≠ some (forwardEntry curIn curOut) ∧
          (tr.eraseIdx idx.val)[j]? ≠ some (forwardEntry curOut curIn) := by
      intro j hj
      constructor
      · intro hsome
        by_cases hidxCur : idx.val < iCur
        · by_cases hjIdx : j < idx.val
          · have hraw : tr[j]? = some (forwardEntry curIn curOut) := by
              rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
              exact hsome
            exact (hfirst j (by simp [iCur', hidxCur] at hj; omega)).1 hraw
          · have hraw : tr[j + 1]? = some (forwardEntry curIn curOut) := by
              have hge : idx.val ≤ j := by omega
              rw [List.getElem?_eraseIdx_of_ge hge] at hsome
              exact hsome
            exact (hfirst (j + 1) (by simp [iCur', hidxCur] at hj; omega)).1 hraw
        · have hCurIdx : iCur < idx.val := by omega
          have hjIdx : j < idx.val := by simp [iCur', hidxCur] at hj; omega
          have hraw : tr[j]? = some (forwardEntry curIn curOut) := by
            rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
            exact hsome
          exact (hfirst j (by simpa [iCur', hidxCur] using hj)).1 hraw
      · intro hsome
        by_cases hidxCur : idx.val < iCur
        · by_cases hjIdx : j < idx.val
          · have hraw : tr[j]? = some (forwardEntry curOut curIn) := by
              rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
              exact hsome
            exact (hfirst j (by simp [iCur', hidxCur] at hj; omega)).2 hraw
          · have hraw : tr[j + 1]? = some (forwardEntry curOut curIn) := by
              have hge : idx.val ≤ j := by omega
              rw [List.getElem?_eraseIdx_of_ge hge] at hsome
              exact hsome
            exact (hfirst (j + 1) (by simp [iCur', hidxCur] at hj; omega)).2 hraw
        · have hCurIdx : iCur < idx.val := by omega
          have hjIdx : j < idx.val := by simp [iCur', hidxCur] at hj; omega
          have hraw : tr[j]? = some (forwardEntry curOut curIn) := by
            rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
            exact hsome
          exact (hfirst j (by simpa [iCur', hidxCur] using hj)).2 hraw
    by_cases hErasePrev : idx.val = iPrev
    · have hidx? : tr[idx.val]? = some (forwardEntry prevIn prevOut) := by
        simpa [hErasePrev] using hprev
      have hidxVal : tr[idx] = forwardEntry prevIn prevOut := by
        rw [List.getElem?_eq_getElem idx.isLt] at hidx?
        exact Option.some.inj hidx?
      obtain ⟨j', hj', stateIn', stateOut', hentry, hcap'⟩ :=
        redundant_forward_capacity_prior
          (tr := tr) (idx := idx) (capSeg := curOut.capacitySegment)
          (stateIn := prevIn) (stateOut := prevOut)
          (by simpa [forwardEntry] using hidxVal) hred hcap
      have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
        List.getElem?_eraseIdx_of_lt (by exact hj')
      have hprev' : (tr.eraseIdx idx.val)[j'.val]? =
          some (forwardEntry stateIn' stateOut') := by
        rw [hkeep, List.getElem?_eq_getElem j'.isLt]
        simpa [forwardEntry, List.get_eq_getElem] using congrArg some hentry
      refine ⟨iCur', j'.val, curIn, curOut, stateIn', stateOut',
        ?_, hcur', hprev', hcap', hfirst'⟩
      by_cases hidxCur : idx.val < iCur
      · simp [iCur', hidxCur]
        omega
      · simp [iCur', hidxCur]
        omega
    · let iPrev' := if idx.val < iPrev then iPrev - 1 else iPrev
      have hprev' : (tr.eraseIdx idx.val)[iPrev']? = some (forwardEntry prevIn prevOut) := by
        by_cases hidxPrev : idx.val < iPrev
        · have hge : idx.val ≤ iPrev - 1 := by omega
          simp only [iPrev', hidxPrev, ↓reduceIte]
          rw [List.getElem?_eraseIdx_of_ge hge, show iPrev - 1 + 1 = iPrev by omega, hprev]
        · have hPrevIdx : iPrev < idx.val := by omega
          simp only [iPrev', hidxPrev, ↓reduceIte]
          rw [List.getElem?_eraseIdx_of_lt hPrevIdx, hprev]
      have hlt' : iPrev' < iCur' := by
        by_cases hidxCur : idx.val < iCur
        · by_cases hidxPrev : idx.val < iPrev
          · simp [iCur', iPrev', hidxCur, hidxPrev]
            omega
          · simp [iCur', iPrev', hidxCur, hidxPrev]
            omega
        · have hidxPrev : ¬ idx.val < iPrev := by omega
          simp [iCur', iPrev', hidxCur, hidxPrev]
          omega
      exact ⟨iCur', iPrev', curIn, curOut, prevIn, prevOut,
        hlt', hcur', hprev', hcap, hfirst'⟩

/-- **Fixpoint preservation**: dedup preserves the first-forward output-capacity collision shape
as the broad base-trace shape used by `capacitySegmentDupPerm`. -/
private lemma firstForwardNat_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      HasFirstForwardCapacityBeforeForwardOutputNat tr →
        HasForwardCapacityBeforeForwardOutput (removeRedundantEntryDS tr).1 := by
  intro N
  induction N with
  | zero =>
      intro tr hlen hP
      obtain ⟨iCur, _iPrev, _curIn, _curOut, _prevIn, _prevOut,
        _hlt, hcur, _hprev, _hcap, _hfirst⟩ := hP
      have hlen0 : tr.length = 0 := Nat.le_zero.mp hlen
      rw [List.length_eq_zero_iff.mp hlen0] at hcur
      simp [forwardEntry] at hcur
  | succ N ih =>
      intro tr hlen hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (firstForwardNat_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hasForwardCapacityBeforeForwardOutput_of_firstForwardNat hP

/-- Public dedup bridge for the M2c permutation-timing path: the strengthened raw
first-forward witness survives `removeRedundantEntryDS` as the broad base-trace
`HasForwardCapacityBeforeForwardOutput` shape. -/
theorem hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstForwardCapacityBeforeForwardOutput tr) :
    HasForwardCapacityBeforeForwardOutput (removeRedundantEntryDS tr).1 :=
  firstForwardNat_removeRedundant tr.length tr le_rfl (firstForwardNat_of_first h)

/-- Inversion of `redundantEntryDS` at an inverse-permutation slot: the redundancy
certificate is an earlier inverse entry (same or reversed). -/
private lemma redundantEntryDS_inv_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (sOut sIn : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inr sIn), sOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- **One-step preservation**: erasing a redundant entry preserves `HasInvEntry`. -/
private lemma hasInvEntry_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    (hP : HasInvEntry tr) :
    HasInvEntry (tr.eraseIdx idx.val) := by
  classical
  obtain ⟨sOut, sIn, hmem⟩ := hP
  by_cases hval : tr[idx] =
      (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)
  · -- the erased slot is (a copy of) the witness: redundancy yields an earlier inverse twin
    obtain ⟨j', hj', hcase⟩ := redundantEntryDS_inv_inversion tr idx sOut sIn hval hred
    have hj'idx : j'.val < idx.val := hj'
    have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
      List.getElem?_eraseIdx_of_lt hj'idx
    have hhit : tr[j'.val]? = some tr[j'] := by
      simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := tr) j'.isLt
    rcases hcase with hc | hc
    · exact ⟨sOut, sIn, mem_of_getElem?' (by rw [hkeep, hhit, hc])⟩
    · exact ⟨sIn, sOut, mem_of_getElem?' (by rw [hkeep, hhit, hc])⟩
  · -- some other occurrence carries the witness; it survives the erasure
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have hpne : p ≠ idx.val := by
      intro hcontr
      apply hval
      calc tr[idx] = tr[p]'hp := by
            subst hcontr; rfl
        _ = _ := hpe
    have hp? : tr[p]? = some
        (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) := by
      rw [List.getElem?_eq_getElem hp, hpe]
    rcases Nat.lt_or_ge p idx.val with hlt | hge
    · refine ⟨sOut, sIn, mem_of_getElem?' (i := p) ?_⟩
      rw [List.getElem?_eraseIdx_of_lt hlt, hp?]
    · have hgt : idx.val < p := lt_of_le_of_ne hge (Ne.symm hpne)
      refine ⟨sOut, sIn, mem_of_getElem?' (i := p - 1) ?_⟩
      rw [List.getElem?_eraseIdx_of_ge (by omega), show p - 1 + 1 = p by omega, hp?]

/-- **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves
`HasInvEntry` (strong induction on the trace length). -/
private lemma hasInvEntry_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      HasInvEntry tr → HasInvEntry (removeRedundantEntryDS tr).1 := by
  intro N
  induction N with
  | zero =>
      intro tr hlen hP
      obtain ⟨sOut, sIn, hmem⟩ := hP
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hmem
      simp at hmem
  | succ N ih =>
      intro tr hlen hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (hasInvEntry_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Any inverse-permutation entry in the dedup'd trace fires `E_pinv`
(`capacitySegmentDupPermInv`): the left conjunct is the entry itself, and the right
disjunction is satisfied by its **5th disjunct at `j' = j`** (the inverse-answer capacity
trivially equals itself). -/
private lemma capacitySegmentDupPermInv_of_inv_mem
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasInvEntry (removeRedundantEntryDS tr).1) :
    capacitySegmentDupPermInv tr := by
  obtain ⟨sOut, sIn, hmem⟩ := h
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, hje⟩ := hmem
  unfold capacitySegmentDupPermInv
  exact ⟨⟨j, hj⟩, sIn.capacitySegment, ⟨sOut, sIn, hje, rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨j, hj⟩, le_refl _, sIn, sOut, hje, rfl⟩)))⟩

/-- **Keystone**: an inverse-permutation entry anywhere in the *raw* trace fires the
combined bad event `E`. Contrapositive: off `E`, the trace contains no `p⁻¹` entries at
all — the reusable engine behind the honest Lemmas 5.12/5.14/5.16 analyses. -/
theorem hasInvEntry_implies_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : HasInvEntry tr) :
    BadEventDS.E tr :=
  Or.inl (Or.inr (Or.inr (capacitySegmentDupPermInv_of_inv_mem tr
    (hasInvEntry_removeRedundant tr.length tr le_rfl h))))

/-- Contrapositive form of the keystone. -/
theorem not_hasInvEntry_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr) :
    ¬ HasInvEntry tr :=
  fun hinv => h (hasInvEntry_implies_E tr hinv)

/-- Index form of `not_hasInvEntry_of_not_E`: off `E`, no trace slot can be an inverse
permutation entry. This is the form consumed by the `J_BT` first-occurrence payloads in the
honest backtrack timing/fork analyses. -/
theorem not_inv_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    {i : ℕ} {sOut sIn : CanonicalSpongeState U}
    (hentry : tr[i]? =
      some (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)) :
    False :=
  not_hasInvEntry_of_not_E tr h ⟨sOut, sIn, mem_of_getElem?' hentry⟩

/-- Off `E`, a trace slot known to be either the forward or inverse entry for one sponge step
must be the forward entry. This is the local eliminator for `firstOccurrenceOfEither`. -/
theorem forward_getElem?_of_not_E_of_perm_or_inv
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    {i : ℕ} {sIn sOut : CanonicalSpongeState U}
    (hentry :
      tr[i]? =
        some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
      tr[i]? =
        some (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) :
    tr[i]? =
      some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  rcases hentry with hforward | hinv
  · exact hforward
  · exact False.elim (not_inv_getElem?_of_not_E tr h hinv)

/-- `J_BT` hash-index payloads point to the recorded hash query for their sequence. -/
theorem jbt_hash_getElem?
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S) :
    GetElem?.getElem? tr p.2.1.val =
      some (⟨Sum.inl p.1.stmt,
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_getElem?
    (trace := tr) (state := state) (seq := seq)

/-- A `J_BT` hash-index payload is the first occurrence of its hash anchor: no strictly earlier
raw trace slot contains the same hash entry. -/
theorem jbt_hash_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (j : Fin tr.length) (hj : j.val < p.2.1.val) :
    tr.get j ≠
      (⟨Sum.inl p.1.stmt,
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_no_prior
    (trace := tr) (state := state) (seq := seq) (j := j) hj

/-- A hash trace slot with no earlier copy of the same hash entry is not redundant under the
duplex-sponge dedup predicate. -/
theorem not_redundantEntryDS_hash_of_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hidx : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hfirst : ∀ j : Fin tr.length, j.val < idx.val →
      tr[j] ≠
        (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) :
    ¬ tr.redundantEntryDS idx := by
  intro hred
  unfold redundantEntryDS at hred
  rw [hidx] at hred
  obtain ⟨j, hjlt, hj⟩ := hred
  exact hfirst j hjlt hj

/-- The strong forward-before-hash predicate carries exactly the nonredundancy proof needed for
its hash anchor: the anchor is a hash entry and no earlier slot contains the same hash entry. -/
theorem hasFirstHashForwardCapacityBeforeHash_hash_not_redundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasFirstHashForwardCapacityBeforeHash tr stmt capSeg) :
    ∃ jHash : Fin tr.length,
      tr[jHash] =
        (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      ¬ tr.redundantEntryDS jHash := by
  obtain ⟨jHash, hhash, hfirst, _jPerm, _hlt, _stateIn, _stateOut, _hperm, _hcap⟩ := h
  exact ⟨jHash, hhash,
    not_redundantEntryDS_hash_of_no_prior (tr := tr) (idx := jHash) hhash hfirst⟩

/-- The hash index carried by any `J_BT` payload is not itself removed by one step of the
duplex-sponge dedup predicate: it is the first occurrence of its concrete hash anchor. -/
theorem jbt_hash_not_redundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S) :
    ¬ tr.redundantEntryDS p.2.1 := by
  refine not_redundantEntryDS_hash_of_no_prior (tr := tr) (idx := p.2.1)
    (stmt := p.1.stmt)
    (capSeg := Vector.drop (p.1.inputState[0]'(by
      rw [p.1.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _)) SpongeSize.R) ?_ ?_
  · have hget := jbt_hash_getElem? tr state S p hp
    rw [List.getElem?_eq_getElem p.2.1.isLt] at hget
    exact Option.some.inj hget
  · intro j hj
    exact jbt_hash_no_prior tr state S p hp j hj

/-- If the deduplicated trace has a hash entry and a strictly earlier forward permutation entry
sharing the hash capacity on either side, then the combined bad event fires through
`capacitySegmentDupHash`. This packages the exact `E_h` constructor needed after the raw M2c
timing witness has been transported through dedup. -/
theorem E_of_base_hash_after_forward_capacity
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {jHash jPerm : Fin (removeRedundantEntryDS tr).1.length}
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    {stateIn stateOut : CanonicalSpongeState U}
    (hlt : jPerm < jHash)
    (hhash : (removeRedundantEntryDS tr).1[jHash] =
      (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hperm : (removeRedundantEntryDS tr).1[jPerm] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    BadEventDS.E tr := by
  left
  left
  unfold capacitySegmentDupHash
  rcases hcap with hOut | hIn
  · exact ⟨jHash, capSeg, stmt, hhash, jPerm, hlt, stmt,
      Or.inr (Or.inl ⟨stateIn, stateOut, hperm, hOut⟩)⟩
  · exact ⟨jHash, capSeg, stmt, hhash, jPerm, hlt, stmt,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨stateIn, stateOut, hperm, hIn⟩)))⟩

/-- Predicate form of `E_of_base_hash_after_forward_capacity`: once the deduplicated base trace
has the forward-before-hash capacity shape, the combined bad event fires. -/
theorem E_of_base_hasForwardCapacityBeforeHash
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h :
      HasForwardCapacityBeforeHash (removeRedundantEntryDS tr).1 stmt capSeg) :
    BadEventDS.E tr := by
  obtain ⟨jHash, hhash, jPerm, hlt, stateIn, stateOut, hperm, hcap⟩ := h
  exact E_of_base_hash_after_forward_capacity
    (tr := tr) (jHash := jHash) (jPerm := jPerm) hlt hhash hperm hcap

/-- If the deduplicated trace has the base permutation-ordering capacity shape, the combined bad
event fires through `capacitySegmentDupPerm`. -/
theorem E_of_base_hasInputCapacityBeforeForwardOutput
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasInputCapacityBeforeForwardOutput (removeRedundantEntryDS tr).1) :
    BadEventDS.E tr := by
  obtain ⟨jCur, stateIn, stateOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  left
  right
  left
  unfold capacitySegmentDupPerm
  exact ⟨jCur, stateOut.capacitySegment,
    ⟨stateIn, stateOut, hcur, rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inl
      ⟨jPrev, Nat.le_of_lt hlt, prevIn, prevOut, hprev, hcap⟩)))⟩

/-- If the deduplicated trace has the broader base permutation-ordering capacity shape, the
combined bad event fires through `capacitySegmentDupPerm`. -/
theorem E_of_base_hasForwardCapacityBeforeForwardOutput
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasForwardCapacityBeforeForwardOutput (removeRedundantEntryDS tr).1) :
    BadEventDS.E tr := by
  obtain ⟨jCur, stateIn, stateOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  left
  right
  left
  unfold capacitySegmentDupPerm
  rcases hcap with hOut | hIn
  · exact ⟨jCur, stateOut.capacitySegment,
      ⟨stateIn, stateOut, hcur, rfl⟩,
      Or.inr (Or.inl ⟨jPrev, hlt, prevIn, prevOut, hprev, hOut⟩)⟩
  · exact ⟨jCur, stateOut.capacitySegment,
      ⟨stateIn, stateOut, hcur, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inl
        ⟨jPrev, Nat.le_of_lt hlt, prevIn, prevOut, hprev, hIn⟩)))⟩

/-- Off `E`, a nonterminal `J_BT` permutation-index payload points to the forward
permutation query for that chain step. -/
theorem jbt_perm_forward_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length) :
    GetElem?.getElem? tr (p.2.2 pairIdx).val =
      some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
        p.1.outputState[pairIdx.val]'hpair⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using forward_getElem?_of_not_E_of_perm_or_inv (tr := tr) h
    (DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
      (trace := tr) (state := state) (seq := seq) (pairIdx := pairIdx) (hpair := hpair))

/-- A nonterminal `J_BT` permutation-index payload is the first occurrence of either recorded
permutation direction for that chain step: no strictly earlier raw trace slot contains the same
forward entry or the corresponding inverse entry. -/
theorem jbt_perm_no_prior_of_lt
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length)
    (j : Fin tr.length) (hj : j.val < (p.2.2 pairIdx).val) :
    tr.get j ≠
        (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      tr.get j ≠
        (⟨Sum.inr (Sum.inr (p.1.outputState[pairIdx.val]'hpair)),
          p.1.inputState[pairIdx]⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
    (trace := tr) (state := state) (seq := seq) (pairIdx := pairIdx) (hpair := hpair)
    (j := j) hj

/-- A `J_BT` payload witnessing the hash-after-first-permutation timing condition cannot be
the empty chain: in the empty case the first-chain index is the sentinel `tr.length`, while the
hash index is a genuine trace index. -/
theorem jbt_time_h_outputState_nonempty
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (hgt : p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val) :
    0 < p.1.outputState.length := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  by_contra hnot
  have hidx :
      ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨0, by
        have := seq.inputState_length_eq_outputState_length_succ
        omega⟩).val = tr.length := by
    dsimp [DuplexSpongeFS.Backtrack.BacktrackSequence.Index]
    simp [hnot]
  have hhash_lt : (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.val
      < tr.length :=
    (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.isLt
  have hgt' :
      (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.val >
        ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨0, by
          have := seq.inputState_length_eq_outputState_length_succ
          omega⟩).val := by
    simpa using hgt
  omega

/-- Off `E`, the first chain index in a hash-after-first-permutation `J_BT` payload is the
forward permutation query for the first chain step. -/
theorem jbt_time_h_first_perm_forward_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (hgt : p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val) :
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      pairIdx.val = 0 ∧
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  let pairIdx : Fin p.1.inputState.length := ⟨0, by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    exact Nat.succ_pos _⟩
  have hpair : pairIdx.val < p.1.outputState.length := by
    simpa [pairIdx] using jbt_time_h_outputState_nonempty tr state S p hp hgt
  refine ⟨pairIdx, hpair, rfl, ?_⟩
  simpa using jbt_perm_forward_getElem?_of_not_E
    (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
    (pairIdx := pairIdx) (hpair := hpair)

/-- In an `E_time_p_honest` witness, the successor pair index cannot be the terminal sentinel:
otherwise the current nonterminal permutation index would have to be after `tr.length`. -/
theorem jbt_time_p_next_outputState_bound
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (ix : Fin p.1.outputState.length)
    (hgt : (p.2.2 ⟨ix.val, by
        have := p.1.inputState_length_eq_outputState_length_succ
        omega⟩).val >
      (p.2.2 ⟨ix.val + 1, by
        have := p.1.inputState_length_eq_outputState_length_succ
        omega⟩).val) :
    ix.val + 1 < p.1.outputState.length := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  by_contra hnot
  let curIdx : Fin seq.inputState.length := ⟨ix.val, by
    rw [seq.inputState_length_eq_outputState_length_succ]
    exact Nat.lt_succ_of_lt ix.isLt⟩
  have hcurSome :=
    DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
      (trace := tr) (state := state) (seq := seq)
      (pairIdx := curIdx) (hpair := by simp [curIdx])
  have hcurLt : ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 curIdx).val
      < tr.length := by
    rcases hcurSome with hcurSome | hcurSome
    · exact (List.getElem?_eq_some_iff.mp hcurSome).1
    · exact (List.getElem?_eq_some_iff.mp hcurSome).1
  have hnext :
      ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨ix.val + 1, by
        rw [seq.inputState_length_eq_outputState_length_succ]
        exact Nat.succ_lt_succ ix.isLt⟩).val = tr.length := by
    dsimp [DuplexSpongeFS.Backtrack.BacktrackSequence.Index]
    simp [hnot]
  have hgt' :
      ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 curIdx).val >
        ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨ix.val + 1, by
          rw [seq.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_lt_succ ix.isLt⟩).val := by
    simpa [curIdx] using hgt
  omega

/-- Off `E`, an honest permutation-ordering witness gives adjacent raw forward permutation
entries: the successor chain step appears earlier in the raw trace. -/
theorem e_time_p_honest_raw_adjacent_forward_witness_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S) :
    ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (curIdx nextIdx : Fin p.1.inputState.length)
      (hcur : curIdx.val < p.1.outputState.length)
      (hnext : nextIdx.val < p.1.outputState.length),
      nextIdx.val = curIdx.val + 1 ∧
      (p.2.2 nextIdx).val < (p.2.2 curIdx).val ∧
      GetElem?.getElem? tr (p.2.2 curIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[curIdx]),
          p.1.outputState[curIdx.val]'hcur⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      GetElem?.getElem? tr (p.2.2 nextIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[nextIdx]),
          p.1.outputState[nextIdx.val]'hnext⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest at hTime
  obtain ⟨p, hp, ix, hgt⟩ := hTime
  have hnextBound :=
    jbt_time_p_next_outputState_bound (tr := tr) (state := state) (S := S)
      (p := p) hp ix hgt
  let curIdx : Fin p.1.inputState.length := ⟨ix.val, by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    exact Nat.lt_succ_of_lt ix.isLt⟩
  let nextIdx : Fin p.1.inputState.length := ⟨ix.val + 1, by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    exact Nat.lt_succ_of_lt hnextBound⟩
  have hcur : curIdx.val < p.1.outputState.length := by
    simp [curIdx]
  have hnext : nextIdx.val < p.1.outputState.length := by
    simpa [nextIdx] using hnextBound
  have hcurPerm :=
    jbt_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
      (pairIdx := curIdx) (hpair := hcur)
  have hnextPerm :=
    jbt_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
      (pairIdx := nextIdx) (hpair := hnext)
  refine ⟨p, hp, curIdx, nextIdx, hcur, hnext, ?_, ?_, hcurPerm, hnextPerm⟩
  · simp [curIdx, nextIdx]
  · simpa [curIdx, nextIdx] using hgt

/-- Off `E`, an honest permutation-ordering witness gives the raw adjacent-forward capacity
shape before any dedup transport: the earlier successor input capacity equals the later current
output capacity. -/
theorem e_time_p_honest_raw_forward_capacity_witness_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S) :
    ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (curIdx nextIdx : Fin p.1.inputState.length)
      (hcur : curIdx.val < p.1.outputState.length)
      (hnext : nextIdx.val < p.1.outputState.length),
      nextIdx.val = curIdx.val + 1 ∧
      (p.2.2 nextIdx).val < (p.2.2 curIdx).val ∧
      GetElem?.getElem? tr (p.2.2 curIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[curIdx]),
          p.1.outputState[curIdx.val]'hcur⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      GetElem?.getElem? tr (p.2.2 nextIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[nextIdx]),
          p.1.outputState[nextIdx.val]'hnext⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      (p.1.outputState[curIdx.val]'hcur).capacitySegment =
        p.1.inputState[nextIdx].capacitySegment := by
  obtain ⟨p, hp, curIdx, nextIdx, hcur, hnext, hsucc, hlt, hcurPerm, hnextPerm⟩ :=
    e_time_p_honest_raw_adjacent_forward_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  refine ⟨p, hp, curIdx, nextIdx, hcur, hnext, hsucc, hlt, hcurPerm, hnextPerm, ?_⟩
  let outIdx : Fin p.1.outputState.length := ⟨curIdx.val, hcur⟩
  have hcap := p.1.capacitySegment_output_eq_input outIdx
  have houtNext : outIdx.val + 1 < p.1.outputState.length := by
    simpa [outIdx, hsucc] using hnext
  have hnextEq :
      nextIdx = ⟨outIdx.val + 1, by
        rw [p.1.inputState_length_eq_outputState_length_succ]
        exact Nat.lt_succ_of_lt houtNext⟩ := by
    apply Fin.ext
    simpa [outIdx] using hsucc
  simpa [outIdx, hnextEq] using hcap

/-- Predicate form of the raw permutation-timing witness: off `E`, `E_time_p_honest`
produces a concrete input-capacity-before-forward-output shape in the raw trace. -/
theorem e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S) :
    HasInputCapacityBeforeForwardOutput tr := by
  obtain ⟨p, _hp, curIdx, nextIdx, hcur, hnext, _hsucc, hlt, hcurPerm, hnextPerm, hcap⟩ :=
    e_time_p_honest_raw_forward_capacity_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  have hcurLt : (p.2.2 curIdx).val < tr.length :=
    (List.getElem?_eq_some_iff.mp hcurPerm).1
  have hnextLt : (p.2.2 nextIdx).val < tr.length :=
    (List.getElem?_eq_some_iff.mp hnextPerm).1
  let jCur : Fin tr.length := ⟨(p.2.2 curIdx).val, hcurLt⟩
  let jPrev : Fin tr.length := ⟨(p.2.2 nextIdx).val, hnextLt⟩
  have hcurGet : tr[jCur] =
      (⟨Sum.inr (Sum.inl p.1.inputState[curIdx]),
        p.1.outputState[curIdx.val]'hcur⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hcurPerm
    rw [List.getElem?_eq_getElem jCur.isLt] at hget
    exact Option.some.inj hget
  have hprevGet : tr[jPrev] =
      (⟨Sum.inr (Sum.inl p.1.inputState[nextIdx]),
        p.1.outputState[nextIdx.val]'hnext⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hnextPerm
    rw [List.getElem?_eq_getElem jPrev.isLt] at hget
    exact Option.some.inj hget
  refine ⟨jCur, p.1.inputState[curIdx], p.1.outputState[curIdx.val]'hcur, hcurGet,
    jPrev, ?_, p.1.inputState[nextIdx], p.1.outputState[nextIdx.val]'hnext,
    hprevGet, hcap.symm⟩
  exact hlt

/-- Broad predicate form of the raw permutation-timing witness, aligned with the
preservation-friendly base endpoint. -/
theorem e_time_p_honest_raw_hasForwardCapacityBeforeForwardOutput_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S) :
    HasForwardCapacityBeforeForwardOutput tr :=
  hasForwardCapacityBeforeForwardOutput_of_input tr
    (e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E
      (tr := tr) h (state := state) (S := S) hTime)

/-- A raw obstruction to the first-forward transport guard: a `J_BT` permutation anchor has a
strictly earlier same-direction reversed forward entry. This is exactly the shape that can make
the later forward anchor redundant under the in-tree `redundantEntryDS` definition while escaping
the existing `J_BT` forward-or-inverse first-occurrence lemma. -/
def HasPriorReversedForwardAnchor
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state) : Prop :=
  ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      ∃ j : Fin tr.length, j.val < (p.2.2 pairIdx).val ∧
        tr[j] = forwardEntry (p.1.outputState[pairIdx.val]'hpair) (p.1.inputState[pairIdx])

/-- A `J_BT` nonterminal forward anchor is redundant under the in-tree `redundantEntryDS`
predicate. Off `E`, this is equivalent to the prior same-direction reversed-forward obstruction
above: the same-forward case is excluded by the `J_BT` first-occurrence lemma, and inverse entries
are excluded by M2a. -/
def HasRedundantForwardAnchor
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state) : Prop :=
  ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (pairIdx : Fin p.1.inputState.length) (_hpair : pairIdx.val < p.1.outputState.length),
      ∃ hidx : (p.2.2 pairIdx).val < tr.length,
        tr.redundantEntryDS ⟨(p.2.2 pairIdx).val, hidx⟩

/-- A prior same-direction reversed-forward entry makes the corresponding `J_BT` forward anchor
redundant under the current dedup predicate. -/
theorem hasRedundantForwardAnchor_of_prior_reverse
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hrev : HasPriorReversedForwardAnchor tr state S) :
    HasRedundantForwardAnchor tr state S := by
  obtain ⟨p, hp, pairIdx, hpair, j, hj, hentry⟩ := hrev
  have hperm :=
    jbt_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
      (pairIdx := pairIdx) (hpair := hpair)
  have hidx : (p.2.2 pairIdx).val < tr.length :=
    (List.getElem?_eq_some_iff.mp hperm).1
  let idx : Fin tr.length := ⟨(p.2.2 pairIdx).val, hidx⟩
  have hcur : tr[idx] =
      forwardEntry (p.1.inputState[pairIdx]) (p.1.outputState[pairIdx.val]'hpair) := by
    have hget := hperm
    rw [List.getElem?_eq_getElem idx.isLt] at hget
    simpa [idx, forwardEntry] using Option.some.inj hget
  refine ⟨p, hp, pairIdx, hpair, hidx, ?_⟩
  unfold redundantEntryDS
  rw [hcur]
  exact ⟨j, by simpa [idx] using hj, Or.inr hentry⟩

/-- Conversely, off `E`, every redundant `J_BT` forward anchor is redundant for the only reason
not already ruled out by the `J_BT` first-occurrence lemma: a prior same-direction reversed-forward
entry. -/
theorem prior_reverse_of_hasRedundantForwardAnchor_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hredAnchor : HasRedundantForwardAnchor tr state S) :
    HasPriorReversedForwardAnchor tr state S := by
  obtain ⟨p, hp, pairIdx, hpair, hidx, hred⟩ := hredAnchor
  let idx : Fin tr.length := ⟨(p.2.2 pairIdx).val, hidx⟩
  have hperm :=
    jbt_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
      (pairIdx := pairIdx) (hpair := hpair)
  have hcur : tr[idx] =
      forwardEntry (p.1.inputState[pairIdx]) (p.1.outputState[pairIdx.val]'hpair) := by
    have hget := hperm
    rw [List.getElem?_eq_getElem idx.isLt] at hget
    simpa [idx, forwardEntry] using Option.some.inj hget
  obtain ⟨j, hj, hcase⟩ :=
    redundantEntryDS_forward_inversion tr idx
      (p.1.inputState[pairIdx]) (p.1.outputState[pairIdx.val]'hpair) hcur hred
  rcases hcase with hsame | hreverse
  · have hno := jbt_perm_no_prior_of_lt
      (tr := tr) (state := state) (S := S) (p := p) hp
      (pairIdx := pairIdx) (hpair := hpair) j (by simpa [idx] using hj)
    exact False.elim ((hno.1) (by simpa [forwardEntry] using hsame))
  · exact ⟨p, hp, pairIdx, hpair, j, by simpa [idx] using hj, hreverse⟩

/-- Off `E`, the prior-reversed-forward obstruction is exactly the statement that some
nonterminal `J_BT` forward anchor is redundant under `redundantEntryDS`. -/
theorem hasPriorReversedForwardAnchor_iff_hasRedundantForwardAnchor_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state) :
    HasPriorReversedForwardAnchor tr state S ↔ HasRedundantForwardAnchor tr state S := by
  constructor
  · exact hasRedundantForwardAnchor_of_prior_reverse (tr := tr) h (state := state) (S := S)
  · exact prior_reverse_of_hasRedundantForwardAnchor_of_not_E
      (tr := tr) h (state := state) (S := S)

/-- Off `E`, an honest permutation-ordering witness either gives the strengthened raw
first-forward predicate needed by the dedup transport, or it exhibits the precise prior reversed
forward obstruction not covered by `jbt_perm_no_prior_of_lt`. -/
theorem e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S) :
    HasFirstForwardCapacityBeforeForwardOutput tr ∨
      HasPriorReversedForwardAnchor tr state S := by
  obtain ⟨p, hp, curIdx, nextIdx, hcur, hnext, hsucc, hlt,
    hcurPerm, hnextPerm, hcap⟩ :=
    e_time_p_honest_raw_forward_capacity_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  by_cases hrev :
      ∃ j : Fin tr.length, j.val < (p.2.2 curIdx).val ∧
        tr[j] = forwardEntry (p.1.outputState[curIdx.val]'hcur) (p.1.inputState[curIdx])
  · right
    obtain ⟨j, hj, hentry⟩ := hrev
    exact ⟨p, hp, curIdx, hcur, j, hj, hentry⟩
  · left
    have hcurLt : (p.2.2 curIdx).val < tr.length :=
      (List.getElem?_eq_some_iff.mp hcurPerm).1
    have hnextLt : (p.2.2 nextIdx).val < tr.length :=
      (List.getElem?_eq_some_iff.mp hnextPerm).1
    let jCur : Fin tr.length := ⟨(p.2.2 curIdx).val, hcurLt⟩
    let jPrev : Fin tr.length := ⟨(p.2.2 nextIdx).val, hnextLt⟩
    have hcurGet : tr[jCur] =
        forwardEntry (p.1.inputState[curIdx]) (p.1.outputState[curIdx.val]'hcur) := by
      have hget := hcurPerm
      rw [List.getElem?_eq_getElem jCur.isLt] at hget
      simpa [forwardEntry] using Option.some.inj hget
    have hprevGet : tr[jPrev] =
        forwardEntry (p.1.inputState[nextIdx]) (p.1.outputState[nextIdx.val]'hnext) := by
      have hget := hnextPerm
      rw [List.getElem?_eq_getElem jPrev.isLt] at hget
      simpa [forwardEntry] using Option.some.inj hget
    have hfirst : ∀ j : Fin tr.length, j.val < jCur.val →
        tr[j] ≠ forwardEntry (p.1.inputState[curIdx]) (p.1.outputState[curIdx.val]'hcur) ∧
          tr[j] ≠ forwardEntry (p.1.outputState[curIdx.val]'hcur) (p.1.inputState[curIdx]) := by
      intro j hj
      constructor
      · have hno := jbt_perm_no_prior_of_lt
          (tr := tr) (state := state) (S := S) (p := p) hp
          (pairIdx := curIdx) (hpair := hcur) j (by simpa [jCur] using hj)
        simpa [forwardEntry] using hno.1
      · intro hentry
        exact hrev ⟨j, by simpa [jCur] using hj, hentry⟩
    exact ⟨jCur, p.1.inputState[curIdx], p.1.outputState[curIdx.val]'hcur,
      hcurGet, hfirst, jPrev, hlt, p.1.inputState[nextIdx],
      p.1.outputState[nextIdx.val]'hnext, hprevGet, Or.inr hcap.symm⟩

/-- Conditional permutation-timing half of M2c: after excluding the explicit prior reversed
forward obstruction, the honest permutation-ordering event cannot occur off the combined bad
event. -/
theorem not_e_time_p_honest_of_not_E_of_no_prior_reverse
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hNoRev : ¬ HasPriorReversedForwardAnchor tr state S) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S := by
  intro hTime
  obtain hfirst | hrev :=
    e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  · exact h (E_of_base_hasForwardCapacityBeforeForwardOutput (tr := tr)
      (hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first tr hfirst))
  · exact hNoRev hrev

/-- Equivalent conditional permutation-timing half of M2c, phrased directly as the missing
dedup invariant: no nonterminal `J_BT` forward anchor may be redundant. -/
theorem not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hNoRed : ¬ HasRedundantForwardAnchor tr state S) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S :=
  not_e_time_p_honest_of_not_E_of_no_prior_reverse (tr := tr) h (state := state) (S := S)
    (fun hrev => hNoRed
      (hasRedundantForwardAnchor_of_prior_reverse (tr := tr) h (state := state) (S := S) hrev))

/-- A deduplicated trace has no redundant nonterminal `J_BT` forward anchors. -/
theorem no_redundant_forward_anchor_of_noRedundantEntryDS
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hNoRed : tr.NoRedundantEntryDS) :
    ¬ HasRedundantForwardAnchor tr state S := by
  rintro ⟨p, _hp, pairIdx, _hpair, hidx, hred⟩
  exact hNoRed ⟨(p.2.2 pairIdx).val, hidx⟩ hred

/-- Permutation-timing closure for traces already satisfying `NoRedundantEntryDS`. -/
theorem not_e_time_p_honest_of_not_E_of_noRedundantEntryDS
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hNoRed : tr.NoRedundantEntryDS) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_p_honest tr state S :=
  not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor
    (tr := tr) h (state := state) (S := S)
    (no_redundant_forward_anchor_of_noRedundantEntryDS tr state S hNoRed)

/-- Off `E`, an honest hash-ordering witness gives concrete raw trace entries: the anchoring
hash query and the first forward permutation query, with the permutation entry earlier in the
trace. This is the raw-trace payload needed before the dedup collision step of M2c. -/
theorem e_time_h_honest_raw_forward_witness_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      pairIdx.val = 0 ∧
      (p.2.2 pairIdx).val < p.2.1.val ∧
      GetElem?.getElem? tr p.2.1.val =
        some (⟨Sum.inl p.1.stmt,
          Vector.drop (p.1.inputState[0]'(by
            rw [p.1.inputState_length_eq_outputState_length_succ]
            exact Nat.succ_pos _)) SpongeSize.R⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest at hTime
  obtain ⟨p, hp, hgt⟩ := hTime
  obtain ⟨pairIdx, hpair, hidx0, hperm⟩ :=
    jbt_time_h_first_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp) hgt
  refine ⟨p, hp, pairIdx, hpair, hidx0, ?_, jbt_hash_getElem? tr state S p hp, hperm⟩
  have hpairIdx :
      pairIdx = ⟨0, by
        have := p.1.inputState_length_eq_outputState_length_succ
        omega⟩ := Fin.ext hidx0
  rw [hpairIdx]
  omega

/-- Off `E`, an honest hash-ordering witness gives the raw collision shape before dedup: the
earlier forward permutation query has input capacity equal to the anchoring hash capacity. -/
theorem e_time_h_honest_raw_forward_capacity_witness_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      pairIdx.val = 0 ∧
      (p.2.2 pairIdx).val < p.2.1.val ∧
      GetElem?.getElem? tr p.2.1.val =
        some (⟨Sum.inl p.1.stmt,
          Vector.drop (p.1.inputState[0]'(by
            rw [p.1.inputState_length_eq_outputState_length_succ]
            exact Nat.succ_pos _)) SpongeSize.R⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      p.1.inputState[pairIdx].capacitySegment =
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R := by
  obtain ⟨p, hp, pairIdx, hpair, hidx0, hlt, hhash, hperm⟩ :=
    e_time_h_honest_raw_forward_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  refine ⟨p, hp, pairIdx, hpair, hidx0, hlt, hhash, hperm, ?_⟩
  cases pairIdx with
  | mk val hval =>
      dsimp at hidx0 ⊢
      subst val
      rfl

/-- Predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a concrete
forward-before-hash capacity collision shape in the raw trace. -/
theorem e_time_h_honest_raw_hasForwardCapacityBeforeHash_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ stmt capSeg, HasForwardCapacityBeforeHash tr stmt capSeg := by
  obtain ⟨p, _hp, pairIdx, hpair, _hidx0, hlt, hhash, hperm, hcap⟩ :=
    e_time_h_honest_raw_forward_capacity_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  let capSeg : Vector U SpongeSize.C :=
    Vector.drop (p.1.inputState[0]'(by
      rw [p.1.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _)) SpongeSize.R
  let jPerm : Fin tr.length := ⟨(p.2.2 pairIdx).val, lt_trans hlt p.2.1.isLt⟩
  have hhash_get : tr[p.2.1] =
      (⟨Sum.inl p.1.stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hhash
    rw [List.getElem?_eq_getElem p.2.1.isLt] at hget
    exact Option.some.inj hget
  have hperm_get : tr[jPerm] =
      (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
        p.1.outputState[pairIdx.val]'hpair⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hperm
    rw [List.getElem?_eq_getElem jPerm.isLt] at hget
    exact Option.some.inj hget
  refine ⟨p.1.stmt, capSeg, p.2.1, hhash_get, jPerm, hlt,
    p.1.inputState[pairIdx], p.1.outputState[pairIdx.val]'hpair, hperm_get, Or.inr hcap⟩

/-- Strong predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a
forward-before-hash capacity shape whose hash anchor is the first occurrence of that hash entry. -/
theorem e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ stmt capSeg, HasFirstHashForwardCapacityBeforeHash tr stmt capSeg := by
  obtain ⟨p, hp, pairIdx, hpair, _hidx0, hlt, hhash, hperm, hcap⟩ :=
    e_time_h_honest_raw_forward_capacity_witness_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  let capSeg : Vector U SpongeSize.C :=
    Vector.drop (p.1.inputState[0]'(by
      rw [p.1.inputState_length_eq_outputState_length_succ]
      exact Nat.succ_pos _)) SpongeSize.R
  let jPerm : Fin tr.length := ⟨(p.2.2 pairIdx).val, lt_trans hlt p.2.1.isLt⟩
  have hhash_get : tr[p.2.1] =
      (⟨Sum.inl p.1.stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hhash
    rw [List.getElem?_eq_getElem p.2.1.isLt] at hget
    exact Option.some.inj hget
  have hperm_get : tr[jPerm] =
      (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
        p.1.outputState[pairIdx.val]'hpair⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    have hget := hperm
    rw [List.getElem?_eq_getElem jPerm.isLt] at hget
    exact Option.some.inj hget
  have hfirst : ∀ j : Fin tr.length, j.val < p.2.1.val →
      tr[j] ≠
        (⟨Sum.inl p.1.stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    intro j hj
    exact jbt_hash_no_prior tr state S p hp j hj
  refine ⟨p.1.stmt, capSeg, p.2.1, hhash_get, hfirst, jPerm, hlt,
    p.1.inputState[pairIdx], p.1.outputState[pairIdx.val]'hpair, hperm_get, Or.inr hcap⟩

/-- Off `E`, the raw first-hash timing witness transports through DSFS dedup to a base-trace
`HasForwardCapacityBeforeHash` witness. -/
theorem e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ stmt capSeg, HasForwardCapacityBeforeHash (removeRedundantEntryDS tr).1 stmt capSeg := by
  obtain ⟨stmt, capSeg, hfirst⟩ :=
    e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  exact ⟨stmt, capSeg, hasForwardCapacityBeforeHash_removeRedundant_of_first tr hfirst⟩

/-- Hash-timing half of M2c: off the combined bad event `E`, the honest hash out-of-order event
cannot occur. The remaining `E_time_p_honest` half is separate. -/
theorem not_e_time_h_honest_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S := by
  intro hTime
  obtain ⟨stmt, capSeg, hbase⟩ :=
    e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E
      (tr := tr) h (state := state) (S := S) hTime
  exact h (E_of_base_hasForwardCapacityBeforeHash
    (tr := tr) (stmt := stmt) (capSeg := capSeg) hbase)

/-- Full timing closure for a fixed trace that is already deduplicated. -/
theorem not_e_time_honest_of_not_E_of_noRedundantEntryDS
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hNoRed : tr.NoRedundantEntryDS) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_honest tr state S := by
  intro hTime
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_honest at hTime
  rcases hTime with hHash | hPerm
  · exact not_e_time_h_honest_of_not_E tr h state S hHash
  · exact not_e_time_p_honest_of_not_E_of_noRedundantEntryDS tr h state S hNoRed hPerm

/-- Full timing closure on the deduplicated base trace produced by `removeRedundantEntryDS`. -/
theorem not_e_time_honest_removeRedundantEntryDS_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U)
    (S : DuplexSpongeFS.Backtrack.S_BT (removeRedundantEntryDS tr).1 state)
    (h : ¬ BadEventDS.E (removeRedundantEntryDS tr).1) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_honest
      (removeRedundantEntryDS tr).1 state S :=
  not_e_time_honest_of_not_E_of_noRedundantEntryDS
    (tr := (removeRedundantEntryDS tr).1) h state S (removeRedundantEntryDS tr).2

/-- Full timing closure on the deduplicated base trace, discharged from the raw-trace
`¬ E tr` hypothesis because `E` itself is defined over the same deduplicated base trace. -/
theorem not_e_time_honest_removeRedundantEntryDS_of_not_E_raw
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U)
    (S : DuplexSpongeFS.Backtrack.S_BT (removeRedundantEntryDS tr).1 state)
    (h : ¬ BadEventDS.E tr) :
    ¬ DuplexSpongeFS.KeyLemmaFoundations.E_time_honest
      (removeRedundantEntryDS tr).1 state S :=
  not_e_time_honest_removeRedundantEntryDS_of_not_E tr state S
    (fun hE => h ((BadEventDS.E_removeRedundantEntryDS_iff tr).mp hE))

/-- Conditional full M2c assembly: a global exclusion of the prior reversed-forward obstruction
is enough to discharge `Lemma5_16HonestFalseAsStated`. -/
theorem lemma5_16_honest_of_no_prior_reverse
    (hNoRev :
      ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
        (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state),
        ¬ BadEventDS.E tr → ¬ HasPriorReversedForwardAnchor tr state S) :
    DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated StmtIn U := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated
  intro tr state S hE hTime
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_honest at hTime
  rcases hTime with hHash | hPerm
  · exact not_e_time_h_honest_of_not_E tr hE state S hHash
  · exact not_e_time_p_honest_of_not_E_of_no_prior_reverse
      tr hE state S (hNoRev tr state S hE) hPerm

/-- Conditional full M2c assembly, phrased at the stronger dedup-invariant boundary: excluding
redundant nonterminal `J_BT` forward anchors is enough to discharge `Lemma5_16HonestFalseAsStated`. -/
theorem lemma5_16_honest_of_no_redundant_forward_anchor
    (hNoRed :
      ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
        (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state),
        ¬ BadEventDS.E tr → ¬ HasRedundantForwardAnchor tr state S) :
    DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated StmtIn U := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated
  intro tr state S hE hTime
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_honest at hTime
  rcases hTime with hHash | hPerm
  · exact not_e_time_h_honest_of_not_E tr hE state S hHash
  · exact not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor
      tr hE state S (hNoRed tr state S hE) hPerm

/-- Conditional full M2c assembly for traces that are already deduplicated. This is the direct
target if the residual is routed over `removeRedundantEntryDS tr` rather than the raw trace. -/
theorem lemma5_16_honest_of_noRedundantEntryDS
    (hNoRed :
      ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)),
        ¬ BadEventDS.E tr → tr.NoRedundantEntryDS) :
    DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated StmtIn U := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.Lemma5_16HonestFalseAsStated
  intro tr state S hE hTime
  exact not_e_time_honest_of_not_E_of_noRedundantEntryDS tr hE state S (hNoRed tr hE) hTime

/-- **M2a discharged** — `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual`
holds: off the combined bad event `E`, no BackTrack chain step is anchored by an
inverse-permutation entry (CO25 Lemma 5.12, honest form over `Backtrack.S_BT`). -/
theorem lemma5_12_honest :
    DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual StmtIn U := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual
  intro tr state S hE hInv
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_inv_honest at hInv
  obtain ⟨p, _hpJ, ιx, sOut, sIn, hentry⟩ := hInv
  exact hE (hasInvEntry_implies_E tr ⟨sOut, sIn, mem_of_getElem?' hentry⟩)

end DuplexSpongeFS.Sponge316

#print axioms DuplexSpongeFS.Sponge316.redundant_forward_capacity_prior
#print axioms DuplexSpongeFS.Sponge316.hasInvEntry_implies_E
#print axioms DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem
#print axioms DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_removeRedundant_of_first
#print axioms DuplexSpongeFS.Sponge316.not_inv_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.forward_getElem?_of_not_E_of_perm_or_inv
#print axioms DuplexSpongeFS.Sponge316.jbt_hash_getElem?
#print axioms DuplexSpongeFS.Sponge316.jbt_hash_no_prior
#print axioms DuplexSpongeFS.Sponge316.hasFirstHashForwardCapacityBeforeHash_hash_not_redundant
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.hasFirstForwardCapacityBeforeForwardOutput_current_not_redundant
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first
#print axioms DuplexSpongeFS.Sponge316.jbt_hash_not_redundant
#print axioms DuplexSpongeFS.Sponge316.E_of_base_hash_after_forward_capacity
#print axioms DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeHash
#print axioms DuplexSpongeFS.Sponge316.E_of_base_hasInputCapacityBeforeForwardOutput
#print axioms DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeForwardOutput
#print axioms DuplexSpongeFS.Sponge316.jbt_perm_forward_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.jbt_perm_no_prior_of_lt
#print axioms DuplexSpongeFS.Sponge316.jbt_time_h_outputState_nonempty
#print axioms DuplexSpongeFS.Sponge316.jbt_time_h_first_perm_forward_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.jbt_time_p_next_outputState_bound
#print axioms DuplexSpongeFS.Sponge316.e_time_p_honest_raw_adjacent_forward_witness_of_not_E
#print axioms DuplexSpongeFS.Sponge316.e_time_p_honest_raw_forward_capacity_witness_of_not_E
#print axioms
  DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E
#print axioms
  DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasForwardCapacityBeforeForwardOutput_of_not_E
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.hasRedundantForwardAnchor_of_prior_reverse
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.prior_reverse_of_hasRedundantForwardAnchor_of_not_E
set_option linter.style.longLine false in
#print axioms
  DuplexSpongeFS.Sponge316.hasPriorReversedForwardAnchor_iff_hasRedundantForwardAnchor_of_not_E
set_option linter.style.longLine false in
#print axioms
  DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_prior_reverse
set_option linter.style.longLine false in
#print axioms
  DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.no_redundant_forward_anchor_of_noRedundantEntryDS
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_noRedundantEntryDS
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.not_e_time_honest_of_not_E_of_noRedundantEntryDS
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E
set_option linter.style.longLine false in
#print axioms DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E_raw
#print axioms DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_witness_of_not_E
#print axioms DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_capacity_witness_of_not_E
#print axioms DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasForwardCapacityBeforeHash_of_not_E

namespace DuplexSpongeFS.Sponge316
#print axioms e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E
#print axioms e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E
#print axioms not_e_time_h_honest_of_not_E
#print axioms lemma5_16_honest_of_no_prior_reverse
set_option linter.style.longLine false in
#print axioms lemma5_16_honest_of_no_redundant_forward_anchor
set_option linter.style.longLine false in
#print axioms lemma5_16_honest_of_noRedundantEntryDS
end DuplexSpongeFS.Sponge316

#print axioms DuplexSpongeFS.Sponge316.lemma5_12_honest
