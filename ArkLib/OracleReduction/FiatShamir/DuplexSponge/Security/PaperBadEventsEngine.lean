/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 M2 ENGINE — transport bricks + coincidence lemmas + paper-faithful Lemmas 5.12/5.14/5.16
statements over `EPaper` (CO25 §5.6, Defs 5.3-5.16).

Layer plan (on top of `EPaper.lean`):

* **Mirror classes**: `mirrorOf` packages the CO25 Def 5.4/5.5 partner payload (hash entries
  are self-mirrors; permutation entries swap direction and query/answer).
  `redundantEntryDSPaper_iff` repackages paper-redundancy as "some strictly earlier slot
  carries the same or mirror payload".

* **T1 transport**: `dedup_invariant` runs any erasure-stable predicate through the
  `removeRedundantEntryDSPaper` recursion. The two instances used downstream:
  - `dedup_getElem_of_firstOfClassAt` (T1b): the first occurrence of a mirror class
    survives paper-dedup verbatim;
  - `dedup_pair_of_firstOfClassAt` (T1a/T2): two first occurrences survive *in raw order*.

* **C1/C2 coincidence lemmas**: `ePaper_of_answerCap_coincidence` (two distinct
  first-of-class slots with equal answer-side capacities) and
  `ePaper_of_queryCap_coincidence` (query-side slot at `i ≤ j` hitting the answer-side
  capacity of slot `j`) fire `EPaper` through the surviving dedup entries.

* **J_BT bricks + M2 statements**: first-of-class facts for the CO25 Def 5.4 index list,
  and `lemma512Paper` / `lemma514Paper` / `lemma516Paper`.
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## Mirror classes (CO25 Defs 5.4/5.5 partner payloads) -/

/-- Mirror payload (CO25 Def 5.4/5.5): hash entries are their own mirror; permutation entries
swap direction and query/answer. -/
def mirrorOf (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  match e with
  | ⟨.inl stmt, cap⟩ => ⟨.inl stmt, cap⟩
  | ⟨.inr (.inl sIn), sOut⟩ => ⟨.inr (.inr sOut), sIn⟩
  | ⟨.inr (.inr sOut), sIn⟩ => ⟨.inr (.inl sIn), sOut⟩

@[simp] lemma mirrorOf_hash (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    mirrorOf (⟨.inl stmt, cap⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = ⟨.inl stmt, cap⟩ := rfl

@[simp] lemma mirrorOf_fwd (sIn sOut : CanonicalSpongeState U) :
    mirrorOf (⟨.inr (.inl sIn), sOut⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = ⟨.inr (.inr sOut), sIn⟩ := rfl

@[simp] lemma mirrorOf_inv (sOut sIn : CanonicalSpongeState U) :
    mirrorOf (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = ⟨.inr (.inl sIn), sOut⟩ := rfl

/-- The answer-side capacity segment of a trace entry (hash output / `p` output / `p⁻¹`
output capacity). -/
def answerCap (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Vector U SpongeSize.C :=
  match e with
  | ⟨.inl _, cap⟩ => cap
  | ⟨.inr (.inl _), sOut⟩ => sOut.capacitySegment
  | ⟨.inr (.inr _), sIn⟩ => sIn.capacitySegment

/-- The query-side capacity segment (permutation entries only). -/
def queryCap? (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (Vector U SpongeSize.C) :=
  match e with
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl sIn), _⟩ => some sIn.capacitySegment
  | ⟨.inr (.inr sOut), _⟩ => some sOut.capacitySegment

@[simp] lemma answerCap_hash (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    answerCap (⟨.inl stmt, cap⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = cap := rfl

@[simp] lemma answerCap_fwd (sIn sOut : CanonicalSpongeState U) :
    answerCap (⟨.inr (.inl sIn), sOut⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = sOut.capacitySegment := rfl

@[simp] lemma answerCap_inv (sOut sIn : CanonicalSpongeState U) :
    answerCap (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = sIn.capacitySegment := rfl

@[simp] lemma queryCap?_hash (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    queryCap? (⟨.inl stmt, cap⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = none := rfl

@[simp] lemma queryCap?_fwd (sIn sOut : CanonicalSpongeState U) :
    queryCap? (⟨.inr (.inl sIn), sOut⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = some sIn.capacitySegment := rfl

@[simp] lemma queryCap?_inv (sOut sIn : CanonicalSpongeState U) :
    queryCap? (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
      = some sOut.capacitySegment := rfl

/-- The paper redundancy predicate, repackaged through `mirrorOf` (CO25 Def 5.5). -/
theorem redundantEntryDSPaper_iff (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) :
    redundantEntryDSPaper log idx ↔
      ∃ j' < idx, log[j'] = log[idx] ∨ log[j'] = mirrorOf log[idx] := by
  unfold redundantEntryDSPaper mirrorOf
  rcases hE : log[idx] with ⟨q, a⟩
  rcases q with s | sIn | sOut
  · constructor
    · rintro ⟨j', hj', h⟩
      exact ⟨j', hj', Or.inl h⟩
    · rintro ⟨j', hj', h | h⟩ <;> exact ⟨j', hj', h⟩
  · exact Iff.rfl
  · exact Iff.rfl

/-! ## Generic list bricks -/

private lemma mem_take_iff_getElem_lt {α : Type _} {l : List α} {k : ℕ} {a : α} :
    a ∈ l.take k ↔ ∃ i : Fin l.length, i.val < k ∧ l[i] = a := by
  constructor
  · intro h
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp h
    have hi' : i < k ∧ i < l.length := by
      rw [List.length_take] at hi
      omega
    refine ⟨⟨i, hi'.2⟩, hi'.1, ?_⟩
    rw [← hgi, Fin.getElem_fin, List.getElem_take]
  · rintro ⟨i, hik, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨i.val, ?_, ?_⟩
    · rw [List.length_take]; omega
    · rw [Fin.getElem_fin, List.getElem_take]

private lemma take_decomp {α : Type _} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  conv_lhs => rw [← List.take_append_drop j l]
  rw [List.drop_eq_getElem_cons hj]

private lemma take_split {α : Type _} (l : List α) {i w : ℕ} (hi : i < l.length) (hiw : i < w) :
    l.take w = l.take i ++ l[i] :: (l.drop (i + 1)).take (w - i - 1) := by
  have hw : w = i + (1 + (w - i - 1)) := by omega
  conv_lhs => rw [hw, List.take_add]
  congr 1
  rw [List.drop_eq_getElem_cons hi,
    show 1 + (w - i - 1) = (w - i - 1) + 1 from by omega, List.take_succ_cons]

/-! ## Class-redundancy and the erasure-stable survivor invariants -/

/-- Slot `k` is class-redundant: some strictly earlier slot carries the same or the mirror
payload. Equivalent to `redundantEntryDSPaper` (see `classRedAt_iff_redundant`). -/
def ClassRedAt (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (k : ℕ)
    (hk : k < log.length) : Prop :=
  log[k]'hk ∈ log.take k ∨ mirrorOf (log[k]'hk) ∈ log.take k

theorem classRedAt_iff_redundant (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) :
    ClassRedAt log idx.val idx.isLt ↔ redundantEntryDSPaper log idx := by
  rw [redundantEntryDSPaper_iff]
  unfold ClassRedAt
  constructor
  · rintro (h | h) <;> obtain ⟨i, hik, hgi⟩ := mem_take_iff_getElem_lt.mp h
    · exact ⟨i, Fin.lt_def.mpr hik, Or.inl hgi⟩
    · exact ⟨i, Fin.lt_def.mpr hik, Or.inr hgi⟩
  · rintro ⟨j', hj', h | h⟩
    · exact Or.inl (mem_take_iff_getElem_lt.mpr ⟨j', Fin.lt_def.mp hj', h⟩)
    · exact Or.inr (mem_take_iff_getElem_lt.mpr ⟨j', Fin.lt_def.mp hj', h⟩)

private lemma classRedAt_append_left
    {l l' : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {k : ℕ}
    (hk : k < l.length) (hk' : k < (l ++ l').length)
    (h : ClassRedAt (l ++ l') k hk') : ClassRedAt l k hk := by
  unfold ClassRedAt at h ⊢
  rw [List.getElem_append_left hk, List.take_append_of_le_length (Nat.le_of_lt hk)] at h
  exact h

/-- `e` occurs in `log` and its first occurrence has no earlier same- or mirror-payload slot. -/
def HeadOfClass (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) : Prop :=
  ∃ l₁ l₂, log = l₁ ++ e :: l₂ ∧ e ∉ l₁ ∧ mirrorOf e ∉ l₁

/-- `e₁` and `e₂` are both class-first occurrences, with `e₁`'s occurrence strictly before
`e₂`'s. -/
def FirstPair (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (e₁ e₂ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) : Prop :=
  ∃ P l₃, log = P ++ e₂ :: l₃ ∧ e₂ ∉ P ∧ mirrorOf e₂ ∉ P ∧ HeadOfClass P e₁

/-- One-erasure stability of `HeadOfClass` (the first occurrence of a class is never the
erased redundant slot). -/
theorem HeadOfClass.eraseIdx {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {k : ℕ} (hk : k < log.length) (hred : ClassRedAt log k hk)
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)} (h : HeadOfClass log e) :
    HeadOfClass (log.eraseIdx k) e := by
  obtain ⟨l₁, l₂, rfl, he, hme⟩ := h
  rcases Nat.lt_trichotomy k l₁.length with hk1 | hk1 | hk1
  · refine ⟨l₁.eraseIdx k, l₂, ?_, fun hm => he (List.mem_of_mem_eraseIdx hm),
      fun hm => hme (List.mem_of_mem_eraseIdx hm)⟩
    rw [List.eraseIdx_append_of_lt_length hk1]
  · exfalso
    subst hk1
    unfold ClassRedAt at hred
    have hg : (l₁ ++ e :: l₂)[l₁.length]'hk = e := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    rw [hg, List.take_left] at hred
    rcases hred with hm | hm
    · exact he hm
    · exact hme hm
  · refine ⟨l₁, l₂.eraseIdx (k - l₁.length - 1), ?_, he, hme⟩
    rw [List.eraseIdx_append_of_length_le (Nat.le_of_lt hk1),
      show k - l₁.length = (k - l₁.length - 1) + 1 from by omega, List.eraseIdx_cons_succ]
    simp

/-- One-erasure stability of `FirstPair`. -/
theorem FirstPair.eraseIdx {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {k : ℕ} (hk : k < log.length) (hred : ClassRedAt log k hk)
    {e₁ e₂ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    (h : FirstPair log e₁ e₂) : FirstPair (log.eraseIdx k) e₁ e₂ := by
  obtain ⟨P, l₃, rfl, h2, h3, hHead⟩ := h
  rcases Nat.lt_trichotomy k P.length with hkP | hkP | hkP
  · refine ⟨P.eraseIdx k, l₃, ?_, fun hm => h2 (List.mem_of_mem_eraseIdx hm),
      fun hm => h3 (List.mem_of_mem_eraseIdx hm),
      HeadOfClass.eraseIdx hkP (classRedAt_append_left hkP hk hred) hHead⟩
    rw [List.eraseIdx_append_of_lt_length hkP]
  · exfalso
    subst hkP
    unfold ClassRedAt at hred
    have hg : (P ++ e₂ :: l₃)[P.length]'hk = e₂ := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    rw [hg, List.take_left] at hred
    rcases hred with hm | hm
    · exact h2 hm
    · exact h3 hm
  · refine ⟨P, l₃.eraseIdx (k - P.length - 1), ?_, h2, h3, hHead⟩
    rw [List.eraseIdx_append_of_length_le (Nat.le_of_lt hkP),
      show k - P.length = (k - P.length - 1) + 1 from by omega, List.eraseIdx_cons_succ]
    simp

/-! ## The dedup transport engine -/

/-- One-step unfolding of the paper dedup recursion in the redundant case. -/
theorem removeRedundantEntryDSPaper_step (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx) :
    removeRedundantEntryDSPaper log
      = removeRedundantEntryDSPaper (log.eraseIdx (Classical.choose h).val) := by
  rw [removeRedundantEntryDSPaper]
  simp [h]

private theorem dedup_invariant_aux
    (P : QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop)
    (hstep : ∀ (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (k : ℕ)
      (hk : k < log.length), ClassRedAt log k hk → P log → P (log.eraseIdx k)) :
    ∀ (n : ℕ) (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)),
      log.length ≤ n → P log → P (removeRedundantEntryDSPaper log).1 := by
  intro n
  induction n with
  | zero =>
      intro log hlen hP
      have hlog : log = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hlog
      have hnr : NoRedundantEntryDSPaper
          ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
        fun idx => absurd idx.isLt (by simp)
      rw [removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper _ hnr]
      exact hP
  | succ n ih =>
      intro log hlen hP
      by_cases hex : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
      · rw [removeRedundantEntryDSPaper_step log hex]
        have hk := (Classical.choose hex).isLt
        refine ih (log.eraseIdx (Classical.choose hex).val) ?_
          (hstep log (Classical.choose hex).val hk
            ((classRedAt_iff_redundant log (Classical.choose hex)).mpr
              (Classical.choose_spec hex)) hP)
        have := List.length_eraseIdx_add_one hk
        omega
      · rw [removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper _
          (fun idx => not_exists.mp hex idx)]
        exact hP

/-- **Transport engine**: any predicate stable under single redundant-slot erasure transports
from the raw trace to its paper dedup. -/
theorem dedup_invariant
    (P : QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop)
    (hstep : ∀ (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (k : ℕ)
      (hk : k < log.length), ClassRedAt log k hk → P log → P (log.eraseIdx k))
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (hP : P log) :
    P (removeRedundantEntryDSPaper log).1 :=
  dedup_invariant_aux P hstep log.length log le_rfl hP

/-- T1 (one-sided): paper dedup only deletes entries — the result is a sublist. -/
theorem dedup_sublist (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    List.Sublist (removeRedundantEntryDSPaper log).1 log :=
  dedup_invariant (List.Sublist · log)
    (fun L k _ _ hP => (List.eraseIdx_sublist L k).trans hP) log (List.Sublist.refl log)

theorem headOfClass_dedup {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)} (h : HeadOfClass log e) :
    HeadOfClass (removeRedundantEntryDSPaper log).1 e :=
  dedup_invariant (HeadOfClass · e)
    (fun _ _ hk hred hP => HeadOfClass.eraseIdx hk hred hP) log h

theorem firstPair_dedup {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e₁ e₂ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    (h : FirstPair log e₁ e₂) : FirstPair (removeRedundantEntryDSPaper log).1 e₁ e₂ :=
  dedup_invariant (FirstPair · e₁ e₂)
    (fun _ _ hk hred hP => FirstPair.eraseIdx hk hred hP) log h

/-! ## Raw first-of-class slots and their dedup images -/

/-- Slot `j` is the first occurrence of its mirror class in `log` (CO25 Def 5.4 index
condition). -/
def FirstOfClassAt (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : Fin log.length) : Prop :=
  ∀ j' : Fin log.length, j' < j → log[j'] ≠ log[j] ∧ log[j'] ≠ mirrorOf log[j]

private lemma not_mem_take_of_firstOfClassAt
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : Fin log.length} (h : FirstOfClassAt log j) {w : ℕ} (hw : w ≤ j.val) :
    log[j] ∉ log.take w ∧ mirrorOf log[j] ∉ log.take w := by
  constructor <;> intro hm <;> obtain ⟨i, hik, hgi⟩ := mem_take_iff_getElem_lt.mp hm
  · exact (h i (Fin.lt_def.mpr (by omega))).1 hgi
  · exact (h i (Fin.lt_def.mpr (by omega))).2 hgi

theorem headOfClass_of_firstOfClassAt {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : Fin log.length} (hj : FirstOfClassAt log j) : HeadOfClass log log[j] :=
  ⟨log.take j.val, log.drop (j.val + 1), take_decomp log j.val j.isLt,
    (not_mem_take_of_firstOfClassAt hj le_rfl).1,
    (not_mem_take_of_firstOfClassAt hj le_rfl).2⟩

theorem firstPair_of_firstOfClassAt {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin log.length} (hij : i < j)
    (hi : FirstOfClassAt log i) (hj : FirstOfClassAt log j) :
    FirstPair log log[i] log[j] := by
  refine ⟨log.take j.val, log.drop (j.val + 1), take_decomp log j.val j.isLt,
    (not_mem_take_of_firstOfClassAt hj le_rfl).1,
    (not_mem_take_of_firstOfClassAt hj le_rfl).2,
    log.take i.val, (log.drop (i.val + 1)).take (j.val - i.val - 1),
    take_split log i.isLt (Fin.lt_def.mp hij), ?_, ?_⟩
  · intro hm
    exact (not_mem_take_of_firstOfClassAt hi le_rfl).1
      (mem_take_iff_getElem_lt.mpr
        (by
          obtain ⟨w, hwk, hwe⟩ := mem_take_iff_getElem_lt.mp hm
          exact ⟨w, by omega, hwe⟩))
  · intro hm
    exact (not_mem_take_of_firstOfClassAt hi le_rfl).2
      (mem_take_iff_getElem_lt.mpr
        (by
          obtain ⟨w, hwk, hwe⟩ := mem_take_iff_getElem_lt.mp hm
          exact ⟨w, by omega, hwe⟩))

theorem HeadOfClass.exists_fin {L : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)} (h : HeadOfClass L e) :
    ∃ j : Fin L.length, L[j] = e := by
  obtain ⟨l₁, l₂, rfl, -, -⟩ := h
  have hb : l₁.length < (l₁ ++ e :: l₂).length := by
    simp only [List.length_append, List.length_cons]; omega
  refine ⟨⟨l₁.length, hb⟩, ?_⟩
  show (l₁ ++ e :: l₂)[l₁.length]'hb = e
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

theorem FirstPair.exists_fin {L : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e₁ e₂ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    (h : FirstPair L e₁ e₂) :
    ∃ i j : Fin L.length, i < j ∧ L[i] = e₁ ∧ L[j] = e₂ := by
  obtain ⟨P, l₃, rfl, -, -, hHead⟩ := h
  obtain ⟨l₁, l₂, rfl, -, -⟩ := hHead
  have hi : l₁.length < ((l₁ ++ e₁ :: l₂) ++ e₂ :: l₃).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hj : (l₁ ++ e₁ :: l₂).length < ((l₁ ++ e₁ :: l₂) ++ e₂ :: l₃).length := by
    simp only [List.length_append, List.length_cons]; omega
  refine ⟨⟨l₁.length, hi⟩, ⟨(l₁ ++ e₁ :: l₂).length, hj⟩, ?_, ?_, ?_⟩
  · rw [Fin.lt_def]
    simp only [List.length_append, List.length_cons]
    omega
  · show ((l₁ ++ e₁ :: l₂) ++ e₂ :: l₃)[l₁.length]'hi = e₁
    rw [List.getElem_append_left (by simp only [List.length_append, List.length_cons]; omega),
      List.getElem_append_right (Nat.le_refl _)]
    simp
  · show ((l₁ ++ e₁ :: l₂) ++ e₂ :: l₃)[(l₁ ++ e₁ :: l₂).length]'hj = e₂
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp

/-- **T1b**: the entry of a first-of-class slot survives paper-dedup verbatim. -/
theorem dedup_getElem_of_firstOfClassAt {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : Fin tr.length} (hj : FirstOfClassAt tr j) :
    ∃ j' : Fin (removeRedundantEntryDSPaper tr).1.length,
      (removeRedundantEntryDSPaper tr).1[j'] = tr[j] :=
  (headOfClass_dedup (headOfClass_of_firstOfClassAt hj)).exists_fin

/-- **T1a/T2**: two first-of-class slots survive paper-dedup in their raw relative order. -/
theorem dedup_pair_of_firstOfClassAt {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin tr.length} (hij : i < j)
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j) :
    ∃ i' j' : Fin (removeRedundantEntryDSPaper tr).1.length, i' < j' ∧
      (removeRedundantEntryDSPaper tr).1[i'] = tr[i] ∧
      (removeRedundantEntryDSPaper tr).1[j'] = tr[j] :=
  (firstPair_dedup (firstPair_of_firstOfClassAt hij hi hj)).exists_fin

end DuplexSpongeFS.Paper
