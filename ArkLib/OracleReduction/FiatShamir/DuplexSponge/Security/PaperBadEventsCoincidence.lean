/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 M2 COINCIDENCE LAYER (C1/C2) — fires `EPaper` from capacity coincidences between
first-of-mirror-class slots of the *raw* trace, via the M2Engine dedup transport.

Built on:
* `EPaper.lean`  — paper-faithful CO25 §5.6 bad event (`EPaper`, arms `E_h`/`E_p`/`E_pinv`).
* `M2Engine.lean` — `mirrorOf`, `answerCap`, `queryCap?`, `FirstOfClassAt`,
  `dedup_getElem_of_firstOfClassAt` (T1b), `dedup_pair_of_firstOfClassAt` (T1a/T2).

Contents (all sorry-free):
* `capacitySegmentDup{Hash,Perm,PermInv}Paper_def` — `Iff.rfl` unfoldings of the three
  `EPaper` capacity arms over `(removeRedundantEntryDSPaper tr).1`.
* `mirrorOf_mirrorOf` — `mirrorOf` is an involution.
* `answerCap_mirrorOf_of_queryCap` / `queryCap?_mirrorOf_of_queryCap` — a mirror swap
  exchanges the answer and query capacities (the C1 ↔ C2 flip from CO25 Def 5.5).
* `ePaper_of_dedup_answerCap_lt` / `ePaper_of_dedup_queryCap_le` — dedup-level workers:
  capacity coincidences between surviving dedup slots fire the matching `EPaper` disjunct.
* **C1** `ePaper_of_answerCap_pair` — two first-of-class raw slots `i < j` with equal
  answer-side capacities fire `EPaper` (all nine kind pairs).
* **C2** `ePaper_of_queryCap_hit` — a perm first-of-class slot `i ≤ j` whose *query*-side
  capacity hits the answer-side capacity of first-of-class slot `j` fires `EPaper`
  (`E_p`/`E_pinv` disjuncts 4–5, with the Eq. 26 repair); when `tr[j]` is a hash entry the
  guard `hhash` demands `i < j` since all `E_h` disjuncts are strict.
  Corollaries: `_lt` (strict, guard-free), `_self` (`i = j` no-loop violation),
  `_permTarget` (`tr[j]` a perm entry, guard-free).
* glue `mem_to_firstOfClass` — every trace entry has a first-of-mirror-class slot carrying
  it or its mirror (the anchor brick for chain entries).
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## `Iff.rfl` unfoldings of the `EPaper` capacity arms -/

/-- The `E_h` arm of `EPaper` as a plain statement about the dedup'd trace. -/
theorem capacitySegmentDupHashPaper_def
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    capacitySegmentDupHashPaper trace ↔
      ∃ j : Fin (removeRedundantEntryDSPaper trace).1.length, ∃ capSeg : Vector U SpongeSize.C,
        ∃ stmt : StmtIn, (removeRedundantEntryDSPaper trace).1[j] = ⟨.inl stmt, capSeg⟩ ∧
          ∃ j' < j,
            ∃ stmt', (removeRedundantEntryDSPaper trace).1[j'] = ⟨.inl stmt', capSeg⟩ ∨
            (∃ stateIn1 stateOut1, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn1, stateOut1⟩
              ∧ stateOut1.capacitySegment = capSeg) ∨
            (∃ stateOut2 stateIn2, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr stateOut2, stateIn2⟩
              ∧ stateIn2.capacitySegment = capSeg) ∨
            (∃ stateIn3 stateOut3, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn3, stateOut3⟩
              ∧ stateIn3.capacitySegment = capSeg) ∨
            (∃ stateOut4 stateIn4, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr stateOut4, stateIn4⟩
              ∧ stateOut4.capacitySegment = capSeg) :=
  Iff.rfl

/-- The `E_p` arm of `EPaper` as a plain statement about the dedup'd trace. -/
theorem capacitySegmentDupPermPaper_def
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    capacitySegmentDupPermPaper trace ↔
      ∃ j : Fin (removeRedundantEntryDSPaper trace).1.length, ∃ capSeg : Vector U SpongeSize.C,
        (∃ stateIn stateOut, (removeRedundantEntryDSPaper trace).1[j]
            = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
          stateOut.capacitySegment = capSeg) ∧
          (
            (∃ j' < j, ∃ stmt', (removeRedundantEntryDSPaper trace).1[j'] = ⟨.inl stmt', capSeg⟩) ∨
            (∃ j' < j, ∃ stateIn1 stateOut1, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
              stateOut1.capacitySegment = capSeg) ∨
            (∃ j' ≤ j, ∃ stateOut2 stateIn2, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
              stateIn2.capacitySegment = capSeg) ∨
            (∃ j' ≤ j, ∃ stateIn3 stateOut3, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
              stateIn3.capacitySegment = capSeg) ∨
            (∃ j' ≤ j, ∃ stateOut4 stateIn4, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
              stateOut4.capacitySegment = capSeg)
          ) :=
  Iff.rfl

/-- The `E_pinv` arm of `EPaper` (with the Eq. 26 repair in disjunct 5) as a plain statement
about the dedup'd trace. -/
theorem capacitySegmentDupPermInvPaper_def
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    capacitySegmentDupPermInvPaper trace ↔
      ∃ j : Fin (removeRedundantEntryDSPaper trace).1.length, ∃ capSeg : Vector U SpongeSize.C,
        (∃ stateOut stateIn, (removeRedundantEntryDSPaper trace).1[j]
            = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
          stateIn.capacitySegment = capSeg) ∧
          (
            (∃ j' < j, ∃ stmt', (removeRedundantEntryDSPaper trace).1[j'] = ⟨.inl stmt', capSeg⟩) ∨
            (∃ j' < j, ∃ stateIn1 stateOut1, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
              stateOut1.capacitySegment = capSeg) ∨
            (∃ j' < j, ∃ stateIn2 stateOut2, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
              CanonicalSpongeState.capacitySegment stateIn2 = capSeg) ∨
            (∃ j' ≤ j, ∃ stateIn3 stateOut3, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
              stateIn3.capacitySegment = capSeg) ∨
            (∃ j' ≤ j, ∃ q a, (removeRedundantEntryDSPaper trace).1[j']
              = ⟨.inr <|.inr q, a⟩ ∧
              CanonicalSpongeState.capacitySegment q = capSeg)
          ) :=
  Iff.rfl

/-! ## Mirror flip bricks -/

/-- `mirrorOf` is an involution. -/
@[simp] theorem mirrorOf_mirrorOf (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    mirrorOf (mirrorOf e) = e := by
  rcases e with ⟨q, a⟩
  rcases q with s | sIn | sOut <;> rfl

/-- A mirror swap turns the query-side capacity into the answer-side capacity
(CO25 Def 5.5: the partner entry of `(p, s_in, s_out)` is `(p⁻¹, s_out, s_in)`). -/
theorem answerCap_mirrorOf_of_queryCap
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    {c : Vector U SpongeSize.C} (h : queryCap? e = some c) :
    answerCap (mirrorOf e) = c := by
  rcases e with ⟨q, a⟩
  rcases q with s | sIn | sOut
  · rw [queryCap?_hash] at h
    simp at h
  · rw [queryCap?_fwd, Option.some.injEq] at h
    rw [mirrorOf_fwd, answerCap_inv]
    exact h
  · rw [queryCap?_inv, Option.some.injEq] at h
    rw [mirrorOf_inv, answerCap_fwd]
    exact h

/-- A mirror swap turns the answer-side capacity into the query-side capacity (for
permutation entries; hash entries are self-mirrors with no query side). -/
theorem queryCap?_mirrorOf_of_queryCap
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    {c : Vector U SpongeSize.C} (h : queryCap? e = some c) :
    queryCap? (mirrorOf e) = some (answerCap e) := by
  rcases e with ⟨q, a⟩
  rcases q with s | sIn | sOut
  · rw [queryCap?_hash] at h
    simp at h
  · rw [mirrorOf_fwd, queryCap?_inv, answerCap_fwd]
  · rw [mirrorOf_inv, queryCap?_fwd, answerCap_inv]

/-! ## Dedup-level workers -/

/-- **W1 (answer–answer, strict)**: two surviving dedup slots `i' < j'` with equal
answer-side capacities fire `EPaper` — the arm is selected by the kind of the *later*
entry (`E_h`/`E_p`/`E_pinv`), the disjunct by the kind of the earlier one. -/
theorem ePaper_of_dedup_answerCap_lt
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i' j' : Fin (removeRedundantEntryDSPaper tr).1.length} (hij : i' < j')
    (hcap : answerCap ((removeRedundantEntryDSPaper tr).1[i'])
      = answerCap ((removeRedundantEntryDSPaper tr).1[j'])) :
    EPaper tr := by
  rcases hEj : (removeRedundantEntryDSPaper tr).1[j'] with ⟨qj, aj⟩
  rcases hEi : (removeRedundantEntryDSPaper tr).1[i'] with ⟨qi, ai⟩
  rw [hEi, hEj] at hcap
  rcases qj with stmtj | sInj | sOutj
  · -- later entry is a hash entry: fire `E_h` (all disjuncts strict, `i' < j'`)
    refine Or.inl (Or.inl ((capacitySegmentDupHashPaper_def tr).mpr
      ⟨j', aj, stmtj, hEj, i', hij, ?_⟩))
    rcases qi with stmti | sIni | sOuti
    · simp only [answerCap_hash] at hcap
      exact ⟨stmti, Or.inl (by rw [hEi, hcap])⟩
    · simp only [answerCap_fwd, answerCap_hash] at hcap
      exact ⟨stmtj, Or.inr (Or.inl ⟨sIni, ai, hEi, hcap⟩)⟩
    · simp only [answerCap_inv, answerCap_hash] at hcap
      exact ⟨stmtj, Or.inr (Or.inr (Or.inl ⟨sOuti, ai, hEi, hcap⟩))⟩
  · -- later entry is a forward entry: fire `E_p`
    refine Or.inl (Or.inr (Or.inl ((capacitySegmentDupPermPaper_def tr).mpr
      ⟨j', CanonicalSpongeState.capacitySegment aj, ⟨sInj, aj, hEj, rfl⟩, ?_⟩)))
    rcases qi with stmti | sIni | sOuti
    · simp only [answerCap_hash, answerCap_fwd] at hcap
      exact Or.inl ⟨i', hij, stmti, by rw [hEi, hcap]⟩
    · simp only [answerCap_fwd] at hcap
      exact Or.inr (Or.inl ⟨i', hij, sIni, ai, hEi, hcap⟩)
    · simp only [answerCap_inv, answerCap_fwd] at hcap
      exact Or.inr (Or.inr (Or.inl ⟨i', le_of_lt hij, sOuti, ai, hEi, hcap⟩))
  · -- later entry is an inverse entry: fire `E_pinv`
    refine Or.inl (Or.inr (Or.inr ((capacitySegmentDupPermInvPaper_def tr).mpr
      ⟨j', CanonicalSpongeState.capacitySegment aj, ⟨sOutj, aj, hEj, rfl⟩, ?_⟩)))
    rcases qi with stmti | sIni | sOuti
    · simp only [answerCap_hash, answerCap_inv] at hcap
      exact Or.inl ⟨i', hij, stmti, by rw [hEi, hcap]⟩
    · simp only [answerCap_fwd, answerCap_inv] at hcap
      exact Or.inr (Or.inl ⟨i', hij, sIni, ai, hEi, hcap⟩)
    · simp only [answerCap_inv] at hcap
      exact Or.inr (Or.inr (Or.inl ⟨i', hij, ai, sOuti, hEi, hcap⟩))

/-- **W2 (query–answer, `≤`)**: a surviving dedup perm slot `i' ≤ j'` whose query-side
capacity equals the answer-side capacity of slot `j'` fires `EPaper` through the `≤`-side
disjuncts 4–5 of `E_p`/`E_pinv` (with the Eq. 26 repair); when the later entry is a hash
entry the guard `hhash` supplies the strictness `E_h` requires. -/
theorem ePaper_of_dedup_queryCap_le
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i' j' : Fin (removeRedundantEntryDSPaper tr).1.length} {c : Vector U SpongeSize.C}
    (hij : i' ≤ j')
    (hq : queryCap? ((removeRedundantEntryDSPaper tr).1[i']) = some c)
    (ha : answerCap ((removeRedundantEntryDSPaper tr).1[j']) = c)
    (hhash : (∃ stmt cap, (removeRedundantEntryDSPaper tr).1[j'] = ⟨.inl stmt, cap⟩)
      → i' < j') :
    EPaper tr := by
  rcases hEj : (removeRedundantEntryDSPaper tr).1[j'] with ⟨qj, aj⟩
  rcases hEi : (removeRedundantEntryDSPaper tr).1[i'] with ⟨qi, ai⟩
  rw [hEj] at ha
  rw [hEi] at hq
  rcases qj with stmtj | sInj | sOutj
  · -- later entry is a hash entry: fire `E_h` via the query-side disjuncts 4–5 (strict)
    have hlt : i' < j' := hhash ⟨stmtj, aj, hEj⟩
    rw [answerCap_hash] at ha
    subst ha
    refine Or.inl (Or.inl ((capacitySegmentDupHashPaper_def tr).mpr
      ⟨j', aj, stmtj, hEj, i', hlt, ?_⟩))
    rcases qi with stmti | sIni | sOuti
    · rw [queryCap?_hash] at hq
      simp at hq
    · rw [queryCap?_fwd, Option.some.injEq] at hq
      exact ⟨stmtj, Or.inr (Or.inr (Or.inr (Or.inl ⟨sIni, ai, hEi, hq⟩)))⟩
    · rw [queryCap?_inv, Option.some.injEq] at hq
      exact ⟨stmtj, Or.inr (Or.inr (Or.inr (Or.inr ⟨sOuti, ai, hEi, hq⟩)))⟩
  · -- later entry is a forward entry: fire `E_p` disjuncts 4–5 (`≤`)
    rw [answerCap_fwd] at ha
    refine Or.inl (Or.inr (Or.inl ((capacitySegmentDupPermPaper_def tr).mpr
      ⟨j', c, ⟨sInj, aj, hEj, ha⟩, ?_⟩)))
    rcases qi with stmti | sIni | sOuti
    · rw [queryCap?_hash] at hq
      simp at hq
    · rw [queryCap?_fwd, Option.some.injEq] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i', hij, sIni, ai, hEi, hq⟩)))
    · rw [queryCap?_inv, Option.some.injEq] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i', hij, sOuti, ai, hEi, hq⟩)))
  · -- later entry is an inverse entry: fire `E_pinv` disjuncts 4–5 (`≤`, Eq. 26 repair)
    rw [answerCap_inv] at ha
    refine Or.inl (Or.inr (Or.inr ((capacitySegmentDupPermInvPaper_def tr).mpr
      ⟨j', c, ⟨sOutj, aj, hEj, ha⟩, ?_⟩)))
    rcases qi with stmti | sIni | sOuti
    · rw [queryCap?_hash] at hq
      simp at hq
    · rw [queryCap?_fwd, Option.some.injEq] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i', hij, sIni, ai, hEi, hq⟩)))
    · rw [queryCap?_inv, Option.some.injEq] at hq
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i', hij, sOuti, ai, hEi, hq⟩)))

/-! ## C1/C2 — raw-trace coincidence lemmas -/

/-- **C1**: two first-of-mirror-class raw slots `i < j` with equal *answer*-side capacities
fire `EPaper`. (The distinctness hypothesis `_hne` is recorded for interface fidelity with
CO25 §5.6 but is derivable from `hj i hij` and not needed by the proof.) -/
theorem ePaper_of_answerCap_pair
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i j : Fin tr.length} (hij : i < j)
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j)
    (_hne : tr[i] ≠ tr[j])
    (hcap : answerCap tr[i] = answerCap tr[j]) :
    EPaper tr := by
  obtain ⟨i', j', hij', hEi, hEj⟩ := dedup_pair_of_firstOfClassAt hij hi hj
  exact ePaper_of_dedup_answerCap_lt tr hij' (by rw [hEi, hEj]; exact hcap)

/-- **C2**: a first-of-mirror-class perm slot `i ≤ j` whose *query*-side capacity equals the
*answer*-side capacity of first-of-class slot `j` fires `EPaper` (the `≤`-side `E_p`/`E_pinv`
disjuncts 4–5, Eq. 26 repair included; `i = j` is the no-loop self-hit). When `tr[j]` is a
hash entry, `E_h` only has strict disjuncts, so the guard `hhash` demands `i < j` there. -/
theorem ePaper_of_queryCap_hit
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i j : Fin tr.length} {c : Vector U SpongeSize.C} (hij : i ≤ j)
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j)
    (hq : queryCap? tr[i] = some c) (ha : answerCap tr[j] = c)
    (hhash : queryCap? tr[j] = none → i < j) :
    EPaper tr := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · obtain ⟨i', j', hij', hEi, hEj⟩ := dedup_pair_of_firstOfClassAt hlt hi hj
    exact ePaper_of_dedup_queryCap_le tr (le_of_lt hij') (by rw [hEi]; exact hq)
      (by rw [hEj]; exact ha) (fun _ => hij')
  · subst heq
    obtain ⟨j', hEj⟩ := dedup_getElem_of_firstOfClassAt hj
    refine ePaper_of_dedup_queryCap_le tr le_rfl (by rw [hEj]; exact hq)
      (by rw [hEj]; exact ha) ?_
    rintro ⟨stmt, cap, hh⟩
    rw [hEj.symm.trans hh, queryCap?_hash] at hq
    simp at hq

/-- **C2, strict form**: with `i < j` the hash guard is automatic. -/
theorem ePaper_of_queryCap_hit_lt
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i j : Fin tr.length} {c : Vector U SpongeSize.C} (hij : i < j)
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j)
    (hq : queryCap? tr[i] = some c) (ha : answerCap tr[j] = c) :
    EPaper tr :=
  ePaper_of_queryCap_hit tr (le_of_lt hij) hi hj hq ha fun _ => hij

/-- **C2, self-hit form**: a single first-of-class perm slot whose query capacity equals its
own answer capacity (a no-loop violation) fires `EPaper` by itself. -/
theorem ePaper_of_queryCap_hit_self
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {j : Fin tr.length} {c : Vector U SpongeSize.C}
    (hj : FirstOfClassAt tr j)
    (hq : queryCap? tr[j] = some c) (ha : answerCap tr[j] = c) :
    EPaper tr :=
  ePaper_of_queryCap_hit tr le_rfl hj hj hq ha (by
    intro hnone
    rw [hnone] at hq
    simp at hq)

/-- **C2, perm-target form**: when `tr[j]` is itself a permutation entry the hash guard is
automatic. -/
theorem ePaper_of_queryCap_hit_permTarget
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i j : Fin tr.length} {c c' : Vector U SpongeSize.C} (hij : i ≤ j)
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j)
    (hq : queryCap? tr[i] = some c) (ha : answerCap tr[j] = c)
    (hperm : queryCap? tr[j] = some c') :
    EPaper tr :=
  ePaper_of_queryCap_hit tr hij hi hj hq ha (by
    intro hnone
    rw [hnone] at hperm
    simp at hperm)

/-! ## Glue: anchoring chain entries at first-of-class slots -/

/-- **Glue brick**: every entry occurring in the trace has a first-of-mirror-class slot
carrying either the entry itself or its mirror (CO25 Def 5.4 first-occurrence convention).
The chain provers use this to anchor `BacktrackSequence` entries at `FirstOfClassAt` slots
before invoking C1/C2. -/
theorem mem_to_firstOfClass
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)} (he : e ∈ tr) :
    ∃ k : Fin tr.length, FirstOfClassAt tr k ∧ (tr[k] = e ∨ tr[k] = mirrorOf e) := by
  classical
  have hex : ∃ n, ∃ hn : n < tr.length, tr[n]'hn = e ∨ tr[n]'hn = mirrorOf e := by
    obtain ⟨w, hw, hwe⟩ := List.mem_iff_getElem.mp he
    exact ⟨w, hw, Or.inl hwe⟩
  obtain ⟨hk, hke⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, hk⟩, ?_, hke⟩
  intro j' hj'
  have hmin : ¬ ∃ hn : j'.val < tr.length, tr[j'.val]'hn = e ∨ tr[j'.val]'hn = mirrorOf e :=
    Nat.find_min hex hj'
  have hne : ¬ (tr[j'.val]'j'.isLt = e ∨ tr[j'.val]'j'.isLt = mirrorOf e) :=
    fun h => hmin ⟨j'.isLt, h⟩
  constructor
  · intro hEq
    rcases hke with h1 | h1
    · exact hne (Or.inl (hEq.trans h1))
    · exact hne (Or.inr (hEq.trans h1))
  · intro hEq
    rcases hke with h1 | h1
    · exact hne (Or.inr (hEq.trans (congrArg mirrorOf h1)))
    · exact hne (Or.inl ((hEq.trans (congrArg mirrorOf h1)).trans (mirrorOf_mirrorOf e)))

/-! ## Axiom audit -/

#print axioms capacitySegmentDupHashPaper_def
#print axioms capacitySegmentDupPermPaper_def
#print axioms capacitySegmentDupPermInvPaper_def
#print axioms mirrorOf_mirrorOf
#print axioms answerCap_mirrorOf_of_queryCap
#print axioms queryCap?_mirrorOf_of_queryCap
#print axioms ePaper_of_dedup_answerCap_lt
#print axioms ePaper_of_dedup_queryCap_le
#print axioms ePaper_of_answerCap_pair
#print axioms ePaper_of_queryCap_hit
#print axioms ePaper_of_queryCap_hit_lt
#print axioms ePaper_of_queryCap_hit_self
#print axioms ePaper_of_queryCap_hit_permTarget
#print axioms mem_to_firstOfClass

end DuplexSpongeFS.Paper
