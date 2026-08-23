/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512HonestPaper

/-!
# CO25 Lemmas 5.12 and 5.16 under paper semantics — DISCHARGED

[CO25] (ePrint 2025/536) *states* Lemmas 5.12 and 5.16 in §5.6 without proof. This file
constructs the proofs against the paper-faithful dedup semantics (`redundantEntryDSPaper`,
`BadEventDSPaper.E`), discharging the named residuals `Lemma5_12HonestResidualPaper` and
`Lemma5_16HonestResidualPaper`. (The legacy forms of both were REFUTED by machine-checked
countermodels exploiting the legacy dedup's same-direction-swapped certificates.)

The mathematical core is an **inverse-cascade strong induction**
(`index_entry_forward_of_not_E`): off the combined paper bad event, every chain index of a
backtrack sequence points at a **forward** permutation entry. If the entry at chain step `n`
were inverse, its *answer* is the step's input state, whose capacity segment is pinned by the
chain link to the previous step's output (or, at `n = 0`, to the anchoring hash answer). The
pinning partner sits at a different trace index; whichever of the two entries is recorded
later, its freshly-sampled answer capacity coincides with an earlier recorded state — one of
the `E_dup` capacity-collision disjuncts. The cascade terminates because the previous chain
entry is forward by the induction hypothesis (or is the hash anchor).

* Lemma 5.12 is the cascade's conclusion verbatim: no chain step is anchored by an inverse
  entry (`lemma5_12_paper`).
* Lemma 5.16's `E_{time,p}` half then only has the all-forward case: an out-of-order pair of
  forward chain entries is a forward-answer capacity collision, absorbed by the landed
  forward-anchored keystone (`lemma5_16_paper_time_p_half`). Combined with the landed hash
  half this discharges the full residual (`lemma5_16HonestResidualPaper_holds`).

The new collision machinery here is the **inverse-anchored** mirror of the landed
forward-anchored keystone: a first-occurrence inverse entry whose answer capacity has a prior
**first-occurrence** hash or forward-answer witness survives paper dedup into
`capacitySegmentDupPermInv`. Carrying first-occurrence guards on the witnesses makes them
erasure-proof (a first occurrence is never paper-redundant — the paper certificates demand an
earlier copy of the same pair), so the dedup transport needs no re-anchoring at all; the
cascade supplies exactly such witnesses (the hash anchor and the chain's first-occurrence
indices).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

set_option linter.unusedSectionVars false

namespace DuplexSpongeFS.Sponge316

open OracleSpec OracleSpec.QueryLog

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

private def hashEntryC (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inl stmt, capSeg⟩

private def forwardEntryC (stateIn stateOut : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inl stateIn), stateOut⟩

private def inverseEntryC (stateOut stateIn : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inr stateOut), stateIn⟩

/-! ## The inverse-anchored collision machinery -/

/-- Shifting a "no prior occurrence below `i`" guard through `eraseIdx`. -/
private lemma firstGuard_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (P : Option ((t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) → Prop)
    (i : ℕ) (hfirst : ∀ k, k < i → P tr[k]?) :
    ∀ k, k < (if idx.val < i then i - 1 else i) → P ((tr.eraseIdx idx.val)[k]?) := by
  intro k hk
  by_cases hidxI : idx.val < i
  · simp only [hidxI, ↓reduceIte] at hk
    by_cases hkIdx : k < idx.val
    · rw [List.getElem?_eraseIdx_of_lt hkIdx]
      exact hfirst k (by omega)
    · rw [List.getElem?_eraseIdx_of_ge (by omega)]
      exact hfirst (k + 1) (by omega)
  · simp only [hidxI, ↓reduceIte] at hk
    rw [List.getElem?_eraseIdx_of_lt (by omega)]
    exact hfirst k (by omega)

/-- Shifting a tracked slot through `eraseIdx` of a different index. -/
private lemma getElem?_eraseIdx_shift
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (i : ℕ) (hne : idx.val ≠ i) :
    (tr.eraseIdx idx.val)[if idx.val < i then i - 1 else i]? = tr[i]? := by
  by_cases hidxI : idx.val < i
  · simp only [hidxI, ↓reduceIte]
    rw [List.getElem?_eraseIdx_of_ge (by omega), show i - 1 + 1 = i by omega]
  · simp only [hidxI, ↓reduceIte]
    rw [List.getElem?_eraseIdx_of_lt (by omega)]

/-- Prior-witness class for the inverse-anchored collision shape: an earlier hash entry whose
answer **is** the capacity segment, or a forward entry whose **answer** capacity matches — each
carrying its own first-occurrence guard. The guards make the witness erasure-proof under paper
dedup (a first occurrence is never paper-redundant), which is what the cascade supplies anyway:
its witnesses are the hash anchor and the chain's first-occurrence indices. -/
private def priorCapWitnessC (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (i : ℕ) (capSeg : Vector U SpongeSize.C) : Prop :=
  (∃ stmt' : StmtIn, tr[i]? = some (hashEntryC stmt' capSeg) ∧
    ∀ k, k < i → tr[k]? ≠ some (hashEntryC stmt' capSeg)) ∨
  (∃ pIn pOut : CanonicalSpongeState U,
    tr[i]? = some (forwardEntryC pIn pOut) ∧ pOut.capacitySegment = capSeg ∧
    ∀ k, k < i →
      tr[k]? ≠ some (forwardEntryC pIn pOut) ∧
        tr[k]? ≠ some (inverseEntryC pOut pIn))

/-- First-occurrence inverse-anchored collision shape (paper semantics, ℕ-indexed): an inverse
entry with no prior copy of its pair in either direction, whose **answer** capacity segment has
a strictly earlier first-occurrence witness from the closed class. -/
def HasFirstCapBeforeInverseAnswerPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ iCur : ℕ, ∃ aOut aIn : CanonicalSpongeState U,
    tr[iCur]? = some (inverseEntryC aOut aIn) ∧
    (∀ j, j < iCur →
      tr[j]? ≠ some (forwardEntryC aIn aOut) ∧
        tr[j]? ≠ some (inverseEntryC aOut aIn)) ∧
    ∃ iPrev, iPrev < iCur ∧ priorCapWitnessC tr iPrev aIn.capacitySegment

/-- Broad (guard-free) inverse-anchored collision shape, for the dedup'd base trace. -/
def HasCapBeforeInverseAnswerPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ iCur : ℕ, ∃ aOut aIn : CanonicalSpongeState U,
    tr[iCur]? = some (inverseEntryC aOut aIn) ∧
    ∃ iPrev, iPrev < iCur ∧
      ((∃ stmt' : StmtIn, tr[iPrev]? = some (hashEntryC stmt' aIn.capacitySegment)) ∨
        (∃ pIn pOut : CanonicalSpongeState U,
          tr[iPrev]? = some (forwardEntryC pIn pOut) ∧
            pOut.capacitySegment = aIn.capacitySegment))

private lemma hasCapBeforeInverseAnswerPaper_of_first
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : HasFirstCapBeforeInverseAnswerPaper tr) :
    HasCapBeforeInverseAnswerPaper tr := by
  obtain ⟨iCur, aOut, aIn, hcur, _hfirst, iPrev, hlt, hwit⟩ := h
  refine ⟨iCur, aOut, aIn, hcur, iPrev, hlt, ?_⟩
  rcases hwit with ⟨stmt', hh, _⟩ | ⟨pIn, pOut, hf, hcap, _⟩
  · exact Or.inl ⟨stmt', hh⟩
  · exact Or.inr ⟨pIn, pOut, hf, hcap⟩

/-- **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves
the first-occurrence inverse-anchored shape. Erasing the anchor or the witness is impossible
(their first-occurrence guards defeat every paper certificate); all other erasures shift. -/
private lemma firstInvNatPaper_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDSPaper idx)
    (hP : HasFirstCapBeforeInverseAnswerPaper tr) :
    HasFirstCapBeforeInverseAnswerPaper (tr.eraseIdx idx.val) := by
  classical
  obtain ⟨iCur, aOut, aIn, hcur, hfirst, iPrev, hlt, hwit⟩ := hP
  by_cases hEraseCur : idx.val = iCur
  · -- the anchor is first-occurrence-of-either, hence not paper-redundant: contradiction
    exfalso
    have hidx? : tr[idx.val]? = some (inverseEntryC aOut aIn) := by
      simpa [hEraseCur] using hcur
    have hidxVal : tr[idx] = inverseEntryC aOut aIn := by
      rw [List.getElem?_eq_getElem idx.isLt] at hidx?
      exact Option.some.inj hidx?
    obtain ⟨j', hj', hcase⟩ :=
      redundantEntryDSPaper_inverse_inversion tr idx aOut aIn
        (by simpa [inverseEntryC] using hidxVal) hred
    have hjCur : j'.val < iCur := by omega
    rcases hcase with hsameI | hsameF
    · exact (hfirst j'.val hjCur).2 (by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa [inverseEntryC, List.get_eq_getElem] using congrArg some hsameI)
    · exact (hfirst j'.val hjCur).1 (by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa [forwardEntryC, List.get_eq_getElem] using congrArg some hsameF)
  · by_cases hErasePrev : idx.val = iPrev
    · -- the witness is first-occurrence, hence not paper-redundant: contradiction
      exfalso
      rcases hwit with ⟨stmt', hh, hhFirst⟩ | ⟨pIn, pOut, hf, _hcap, hfFirst⟩
      · have hidxVal : tr[idx] = hashEntryC stmt' aIn.capacitySegment := by
          have : tr[idx.val]? = some (hashEntryC stmt' aIn.capacitySegment) := by
            simpa [hErasePrev] using hh
          rw [List.getElem?_eq_getElem idx.isLt] at this
          exact Option.some.inj this
        obtain ⟨j', hj', hentry⟩ :=
          redundantEntryDSPaper_hash_inversion tr idx stmt' aIn.capacitySegment
            (by simpa [hashEntryC] using hidxVal) hred
        exact hhFirst j'.val (by omega) (by
          rw [List.getElem?_eq_getElem j'.isLt]
          simpa [hashEntryC, List.get_eq_getElem] using congrArg some hentry)
      · have hidxVal : tr[idx] = forwardEntryC pIn pOut := by
          have : tr[idx.val]? = some (forwardEntryC pIn pOut) := by
            simpa [hErasePrev] using hf
          rw [List.getElem?_eq_getElem idx.isLt] at this
          exact Option.some.inj this
        obtain ⟨j', hj', hcase⟩ :=
          redundantEntryDSPaper_forward_inversion tr idx pIn pOut
            (by simpa [forwardEntryC] using hidxVal) hred
        rcases hcase with hsameF | hflipI
        · exact (hfFirst j'.val (by omega)).1 (by
            rw [List.getElem?_eq_getElem j'.isLt]
            simpa [forwardEntryC, List.get_eq_getElem] using congrArg some hsameF)
        · exact (hfFirst j'.val (by omega)).2 (by
            rw [List.getElem?_eq_getElem j'.isLt]
            simpa [inverseEntryC, List.get_eq_getElem] using congrArg some hflipI)
    · -- the erased entry is neither anchor nor witness: shift both tracked slots
      refine ⟨if idx.val < iCur then iCur - 1 else iCur, aOut, aIn, ?_, ?_,
        if idx.val < iPrev then iPrev - 1 else iPrev, ?_, ?_⟩
      · rw [getElem?_eraseIdx_shift tr idx iCur hEraseCur]
        exact hcur
      · exact firstGuard_eraseIdx tr idx
          (fun o => o ≠ some (forwardEntryC aIn aOut) ∧ o ≠ some (inverseEntryC aOut aIn))
          iCur hfirst
      · by_cases hidxCur : idx.val < iCur
        · by_cases hidxPrev : idx.val < iPrev
          · simp only [hidxCur, hidxPrev, ↓reduceIte]
            omega
          · simp only [hidxCur, hidxPrev, ↓reduceIte]
            omega
        · have hidxPrev : ¬ idx.val < iPrev := by omega
          simp only [hidxCur, hidxPrev, ↓reduceIte]
          omega
      · rcases hwit with ⟨stmt', hh, hhFirst⟩ | ⟨pIn, pOut, hf, hcap, hfFirst⟩
        · exact Or.inl ⟨stmt', by
            rw [getElem?_eraseIdx_shift tr idx iPrev hErasePrev]; exact hh,
            firstGuard_eraseIdx tr idx
              (fun o => o ≠ some (hashEntryC stmt' aIn.capacitySegment)) iPrev hhFirst⟩
        · exact Or.inr ⟨pIn, pOut, by
            rw [getElem?_eraseIdx_shift tr idx iPrev hErasePrev]; exact hf, hcap,
            firstGuard_eraseIdx tr idx
              (fun o => o ≠ some (forwardEntryC pIn pOut) ∧
                o ≠ some (inverseEntryC pOut pIn)) iPrev hfFirst⟩

/-- **Fixpoint preservation (paper semantics)**: dedup preserves the inverse-anchored shape. -/
private lemma firstInvNatPaper_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      HasFirstCapBeforeInverseAnswerPaper tr →
        HasCapBeforeInverseAnswerPaper (removeRedundantEntryDSPaper tr).1 := by
  intro N
  induction N with
  | zero =>
      intro tr hlen hP
      obtain ⟨iCur, _aO, _aI, hcur, _⟩ := hP
      have hlen0 : tr.length = 0 := Nat.le_zero.mp hlen
      rw [List.length_eq_zero_iff.mp hlen0] at hcur
      simp at hcur
  | succ N ih =>
      intro tr hlen hP
      rw [removeRedundantEntryDSPaper]
      split
      · rename_i hex
        refine ih _ ?_ (firstInvNatPaper_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hasCapBeforeInverseAnswerPaper_of_first hP

/-- **The inverse-anchored keystone (paper semantics)**: a raw first-occurrence inverse entry
whose answer capacity has a prior first-occurrence hash or forward-answer witness forces
`capacitySegmentDupPermInv` on the dedup'd base trace. -/
theorem e_pinv_of_hasFirstCapBeforeInverseAnswerPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstCapBeforeInverseAnswerPaper tr) :
    BadEventDSPaper.E_pinv tr := by
  have hbase := firstInvNatPaper_removeRedundant tr.length tr le_rfl h
  obtain ⟨iCur, aOut, aIn, hcur, iPrev, hlt, hwit⟩ := hbase
  obtain ⟨hCurLt, hCurEq⟩ := List.getElem?_eq_some_iff.mp hcur
  unfold BadEventDSPaper.E_pinv BadEventDSPaper.capacitySegmentDupPermInv
  refine ⟨⟨iCur, hCurLt⟩, aIn.capacitySegment, ⟨aOut, aIn, hCurEq, rfl⟩, ?_⟩
  rcases hwit with ⟨stmt', hh⟩ | ⟨pIn, pOut, hf, hcap⟩
  · obtain ⟨hPL, hPE⟩ := List.getElem?_eq_some_iff.mp hh
    exact Or.inl ⟨⟨iPrev, hPL⟩, Fin.mk_lt_mk.mpr hlt, stmt', hPE⟩
  · obtain ⟨hPL, hPE⟩ := List.getElem?_eq_some_iff.mp hf
    exact Or.inr (Or.inl ⟨⟨iPrev, hPL⟩, Fin.mk_lt_mk.mpr hlt, pIn, pOut, hPE, hcap⟩)

/-- The inverse-anchored keystone, composed into the combined paper bad event `E`. -/
theorem e_of_hasFirstCapBeforeInverseAnswerPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstCapBeforeInverseAnswerPaper tr) :
    BadEventDSPaper.E tr :=
  Or.inl (Or.inr (Or.inr (e_pinv_of_hasFirstCapBeforeInverseAnswerPaper tr h)))

/-! ## The inverse cascade — CO25 Lemma 5.12 -/

/-- **The cascade (the mathematical core of CO25 Lemmas 5.12/5.16)**: off the combined paper
bad event, every nonterminal chain index of a backtrack sequence points at the **forward**
recording of its step. Strong induction: an inverse recording's answer capacity is pinned by
the chain link to the previous step's forward answer (IH) or to the hash anchor (base case);
whichever pinning partner is recorded on the other side of the inverse entry, the coincidence
lands in a capacity-collision keystone. -/
theorem index_entry_forward_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)
    (seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state)
    (hE : ¬ BadEventDSPaper.E tr) :
    ∀ (n : ℕ) (hn : n < seq.outputState.length),
      tr[((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
          ⟨n, by rw [seq.inputState_length_eq_outputState_length_succ]; omega⟩).val]? =
        some (forwardEntryC
          (seq.inputState[n]'(by
            rw [seq.inputState_length_eq_outputState_length_succ]; omega))
          (seq.outputState[n]'hn)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn' : n < seq.inputState.length := by
      rw [seq.inputState_length_eq_outputState_length_succ]; omega
    have hperm :=
      DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
        tr state seq ⟨n, hn'⟩ hn
    rcases hperm with hfwd | hinv
    · exact hfwd
    · -- the inverse case is excluded by a capacity collision
      exfalso
      set sIn : CanonicalSpongeState U := seq.inputState[n]'hn' with hsIn
      set sOut : CanonicalSpongeState U := seq.outputState[n]'hn with hsOut
      obtain ⟨haLt, _⟩ := List.getElem?_eq_some_iff.mp hinv
      have hguard : ∀ k,
          k < ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨n, hn'⟩).val →
          tr[k]? ≠ some (forwardEntryC sIn sOut) ∧
            tr[k]? ≠ some (inverseEntryC sOut sIn) := by
        intro k hk
        have hkLen : k < tr.length := lt_trans hk haLt
        have hnp :=
          DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
            tr state seq ⟨n, hn'⟩ hn ⟨k, hkLen⟩ hk
        constructor
        · intro hsome
          exact hnp.1 (by
            rw [List.getElem?_eq_getElem hkLen] at hsome
            exact Option.some.inj hsome)
        · intro hsome
          exact hnp.2 (by
            rw [List.getElem?_eq_getElem hkLen] at hsome
            exact Option.some.inj hsome)
      rcases n with _ | m
      · -- base case: the answer capacity is pinned to the hash anchor
        have hhash :=
          DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_getElem? tr state seq
        have hhash' : tr[((DuplexSpongeFS.Backtrack.BacktrackSequence.Index
            tr state seq).1).val]? =
            some (hashEntryC seq.stmt sIn.capacitySegment) := hhash
        have hhashFirst : ∀ k,
            k < ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1).val →
            tr[k]? ≠ some (hashEntryC seq.stmt sIn.capacitySegment) := by
          intro k hk hbad
          have hkLen : k < tr.length :=
            lt_trans hk
              ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1).isLt
          rw [List.getElem?_eq_getElem hkLen] at hbad
          exact DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_no_prior
            tr state seq ⟨k, hkLen⟩ hk (Option.some.inj hbad)
        rcases lt_trichotomy
          ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1).val
          ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨0, hn'⟩).val with hlt | heq | hgt
        · -- hash strictly earlier: inverse-anchored keystone, hash witness
          exact hE (e_of_hasFirstCapBeforeInverseAnswerPaper tr
            ⟨_, sOut, sIn, hinv, hguard, _, hlt, Or.inl ⟨seq.stmt, hhash', hhashFirst⟩⟩)
        · -- equal indices: a hash entry cannot be a permutation entry
          rw [heq] at hhash'
          have hcontra := hhash'.symm.trans hinv
          simp [hashEntryC] at hcontra
        · -- hash strictly later: the landed hash-anchored keystone
          exact hE (e_of_hasFirstHashPermCapNatPaper tr
            ⟨_, _, hgt, hhash', hhashFirst, sIn, sOut, Or.inr hinv, Or.inr rfl⟩)
      · -- inductive step: the answer capacity is pinned to the previous forward answer
        have hm : m < seq.outputState.length := by omega
        have hm' : m < seq.inputState.length := by
          rw [seq.inputState_length_eq_outputState_length_succ]; omega
        have hfwdm := ih m (Nat.lt_succ_self m) hm
        obtain ⟨hbLt, hbEq⟩ := List.getElem?_eq_some_iff.mp hfwdm
        have hlink : (seq.outputState[m]'hm).capacitySegment = sIn.capacitySegment :=
          seq.capacitySegment_output_eq_input ⟨m, hm⟩
        have hprevFirst : ∀ k,
            k < ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
              ⟨m, hm'⟩).val →
            tr[k]? ≠ some (forwardEntryC (seq.inputState[m]'hm') (seq.outputState[m]'hm)) ∧
              tr[k]? ≠ some (inverseEntryC (seq.outputState[m]'hm) (seq.inputState[m]'hm')) := by
          intro k hk
          have hkLen : k < tr.length := lt_trans hk hbLt
          have hnp :=
            DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
              tr state seq ⟨m, hm'⟩ hm ⟨k, hkLen⟩ hk
          constructor
          · intro hsome
            exact hnp.1 (by
              rw [List.getElem?_eq_getElem hkLen] at hsome
              exact Option.some.inj hsome)
          · intro hsome
            exact hnp.2 (by
              rw [List.getElem?_eq_getElem hkLen] at hsome
              exact Option.some.inj hsome)
        rcases lt_trichotomy
          ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨m, hm'⟩).val
          ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨m + 1, hn'⟩).val with hlt | heq | hgt
        · -- previous step strictly earlier: inverse-anchored keystone, forward-answer witness
          exact hE (e_of_hasFirstCapBeforeInverseAnswerPaper tr
            ⟨_, sOut, sIn, hinv, hguard, _, hlt,
              Or.inr ⟨seq.inputState[m]'hm', seq.outputState[m]'hm, hfwdm, hlink, hprevFirst⟩⟩)
        · -- equal indices: a forward entry cannot be an inverse entry
          rw [heq] at hfwdm
          have hcontra := hfwdm.symm.trans hinv
          simp [forwardEntryC] at hcontra
        · -- previous step strictly later: the landed forward-anchored keystone
          refine hE (e_of_hasFirstPermCapacityBeforeForwardOutputPaper tr
            ⟨⟨_, hbLt⟩, seq.inputState[m]'hm', seq.outputState[m]'hm, hbEq, ?_,
              ⟨_, haLt⟩, Fin.mk_lt_mk.mpr hgt, sIn, sOut, Or.inr ?_, Or.inr hlink.symm⟩)
          · intro j hj
            have hnp :=
              DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
                tr state seq ⟨m, hm'⟩ hm j hj
            exact ⟨hnp.1, hnp.2⟩
          · rw [List.getElem?_eq_getElem haLt] at hinv
            exact Option.some.inj hinv

/-! ## CO25 Lemma 5.12, paper semantics — DISCHARGED -/

open DuplexSpongeFS.KeyLemmaFoundations in
/-- **CO25 Lemma 5.12, paper semantics — DISCHARGED**: off the paper combined bad event, no
BackTrack chain step is anchored by an inverse-permutation entry. -/
theorem lemma5_12_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr) :
    ¬ E_inv_honest tr state S := by
  classical
  intro hInv
  obtain ⟨p, hp, ιx, s_out, s_in, hentry⟩ := hInv
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, rfl⟩ := hp
  have hfwd := index_entry_forward_of_not_E tr state seq hE ιx.val ιx.isLt
  have hcontra := hfwd.symm.trans hentry
  simp [forwardEntryC] at hcontra

/-- The residual `Lemma5_12HonestResidualPaper`, discharged. -/
theorem lemma5_12HonestResidualPaper_holds :
    Lemma5_12HonestResidualPaper StmtIn U :=
  fun tr state S hE => lemma5_12_paper tr state S hE

/-! ## CO25 Lemma 5.16 `E_{time,p}` half, paper semantics — DISCHARGED -/

open DuplexSpongeFS.KeyLemmaFoundations in
/-- **CO25 Lemma 5.16, permutation half, paper semantics — DISCHARGED**: off the paper
combined bad event, no chain permutation query precedes its predecessor in the trace. By the
cascade both entries are forward; an out-of-order pair is then a forward-answer capacity
collision through the chain link, absorbed by the landed forward-anchored keystone. -/
theorem lemma5_16_paper_time_p_half
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr) :
    ¬ E_time_p_honest tr state S := by
  classical
  intro hTime
  obtain ⟨p, hp, ιx, hgt⟩ := hTime
  have hsuccFromTime :=
    DuplexSpongeFS.Sponge316.jbt_time_p_next_outputState_bound tr state S p hp ιx hgt
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, rfl⟩ := hp
  have hιx' : ιx.val < seq.inputState.length := by
    rw [seq.inputState_length_eq_outputState_length_succ]
    exact Nat.lt_succ_of_lt ιx.isLt
  have hfwd_x := index_entry_forward_of_not_E tr state seq hE ιx.val ιx.isLt
  obtain ⟨haLt, haEq⟩ := List.getElem?_eq_some_iff.mp hfwd_x
  have hsucc : ιx.val + 1 < seq.outputState.length := hsuccFromTime
  have hsucc' : ιx.val + 1 < seq.inputState.length := by
    rw [seq.inputState_length_eq_outputState_length_succ]
    exact Nat.lt_succ_of_lt hsucc
  have hfwd_s := index_entry_forward_of_not_E tr state seq hE (ιx.val + 1) hsucc
  obtain ⟨hbLt, hbEq⟩ := List.getElem?_eq_some_iff.mp hfwd_s
  have hlink : (seq.outputState[ιx.val]'ιx.isLt).capacitySegment =
      (seq.inputState[ιx.val + 1]'hsucc').capacitySegment :=
    seq.capacitySegment_output_eq_input ⟨ιx.val, ιx.isLt⟩
  have hgt' : ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
      ⟨ιx.val + 1, hsucc'⟩).val <
      ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2
        ⟨ιx.val, hιx'⟩).val := hgt
  refine hE (e_of_hasFirstPermCapacityBeforeForwardOutputPaper tr
    ⟨⟨_, haLt⟩, seq.inputState[ιx.val]'hιx', seq.outputState[ιx.val]'ιx.isLt, haEq, ?_,
      ⟨_, hbLt⟩, Fin.mk_lt_mk.mpr hgt',
      seq.inputState[ιx.val + 1]'hsucc', seq.outputState[ιx.val + 1]'hsucc,
      Or.inl hbEq, Or.inr hlink.symm⟩)
  · intro j hj
    have hnp :=
      DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
        tr state seq ⟨ιx.val, hιx'⟩ ιx.isLt j hj
    exact ⟨hnp.1, hnp.2⟩

open DuplexSpongeFS.KeyLemmaFoundations in
/-- **CO25 Lemma 5.16, paper semantics — DISCHARGED** (both halves): off the paper combined
bad event, all chain queries appear in trace order. -/
theorem lemma5_16_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr) :
    ¬ E_time_honest tr state S := by
  intro hTime
  rcases hTime with hH | hP
  · exact lemma5_16_paper_hash_half tr state S hE hH
  · exact lemma5_16_paper_time_p_half tr state S hE hP

/-- The residual `Lemma5_16HonestResidualPaper`, discharged. -/
theorem lemma5_16HonestResidualPaper_holds :
    Lemma5_16HonestResidualPaper StmtIn U :=
  fun tr state S hE => lemma5_16_paper tr state S hE

end DuplexSpongeFS.Sponge316

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Sponge316.e_of_hasFirstCapBeforeInverseAnswerPaper
#print axioms DuplexSpongeFS.Sponge316.index_entry_forward_of_not_E
#print axioms DuplexSpongeFS.Sponge316.lemma5_12HonestResidualPaper_holds
#print axioms DuplexSpongeFS.Sponge316.lemma5_16HonestResidualPaper_holds
