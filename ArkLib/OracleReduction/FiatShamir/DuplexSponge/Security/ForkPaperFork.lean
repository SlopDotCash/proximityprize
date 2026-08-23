/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ConsistencyPaperCascade

/-!
# CO25 Lemma 5.14 under paper semantics — DISCHARGED

[CO25] (ePrint 2025/536) states Lemma 5.14 (`E(tr) = 0 ⟹ E_fork(tr, s) = 0`) without a
standalone proof; the argument appears inside Claim 5.19's `S⁽¹⁾ = S⁽²⁾` analysis (p. 44).
This file formalizes it against the paper-faithful dedup semantics, discharging the named
residual `Lemma5_14HonestResidualPaper`. (The legacy form was REFUTED by a machine-checked
countermodel, `Lemma514ForkFalse.lean`.)

Structure of the proof, mirroring the paper:

1. The inverse cascade (`index_entry_forward_of_not_E`, landed) puts every chain entry of
   both sequences in **forward** recorded form, with first-occurrence-of-either guards.
2. **Backward agreement induction**: the two sequences share the end state; at each step
   backwards, the chain links pin the two outputs' capacity segments together, so off the
   capacity-collision events the inputs must be equal (`Efork,p`-style, absorbed by the
   landed forward-anchored keystone), and off the permutation-consistency event equal
   inputs force equal outputs (`Eprp`/`E_func`-style, the two-survivor transport below).
3. **Equal lengths**: a strict length difference pins the shorter sequence's hash answer to
   a chain output capacity of the longer one (`Efork,h,p`-style: the landed hash-anchored
   keystone in one order, the hash-witness survivor pair in the other).
4. **Equal statements**: two distinct hash entries sharing the answer capacity collide
   (`Efork,h`-style, the hash/hash survivor pair).
5. Equal data fields force equal `BacktrackSequence`s (proof fields are propositions), so
   the family has at most one element: `¬ E_fork_honest`.

The supporting machinery is a **generic two-survivor dedup transport**: two slots whose
entries carry their own first-occurrence guards are erasure-proof under paper dedup (a
first occurrence is never paper-redundant) and keep their relative order, so both survive
into the base trace where the relevant collision event fires.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

set_option linter.unusedSectionVars false

namespace DuplexSpongeFS.Sponge316

open OracleSpec OracleSpec.QueryLog

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

private def hashEntryD (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inl stmt, capSeg⟩

private def forwardEntryD (stateIn stateOut : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inl stateIn), stateOut⟩

private def inverseEntryD (stateOut stateIn : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inr stateOut), stateIn⟩

/-! ## Generic two-survivor dedup transport -/

/-- A tagged trace slot: either a hash entry or a forward permutation entry. The tag
determines the slot's certificate targets under `redundantEntryDSPaper`. -/
private inductive SlotKind (StmtIn U : Type) [SpongeUnit U] [SpongeSize] where
  | hash (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
  | fwd (stateIn stateOut : CanonicalSpongeState U)

private def SlotKind.entry : SlotKind StmtIn U →
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)
  | .hash stmt capSeg => hashEntryD stmt capSeg
  | .fwd stateIn stateOut => forwardEntryD stateIn stateOut

/-- The slot's first-occurrence guard: no strictly earlier slot holds any certificate
target for this entry (the entry itself; for forward entries also the direction-flipped
inverse, per the paper certificates). -/
private def SlotKind.guard (sk : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (i : ℕ) : Prop :=
  match sk with
  | .hash stmt capSeg => ∀ k, k < i → tr[k]? ≠ some (hashEntryD stmt capSeg)
  | .fwd stateIn stateOut => ∀ k, k < i →
      tr[k]? ≠ some (forwardEntryD stateIn stateOut) ∧
        tr[k]? ≠ some (inverseEntryD stateOut stateIn)

/-- A guarded slot: the entry sits at slot `i` and is the first occurrence of its
certificate class. -/
private def SlotKind.ok (sk : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (i : ℕ) : Prop :=
  tr[i]? = some sk.entry ∧ sk.guard tr i

/-- A guarded slot is never paper-redundant. -/
private lemma SlotKind.not_redundant (sk : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (hok : sk.ok tr idx.val) : ¬ tr.redundantEntryDSPaper idx := by
  obtain ⟨hentry, hguard⟩ := hok
  have hval : tr[idx] = sk.entry := by
    rw [List.getElem?_eq_getElem idx.isLt] at hentry
    exact Option.some.inj hentry
  cases sk with
  | hash stmt capSeg =>
      exact not_redundantEntryDSPaper_hash_of_no_prior tr idx
        (by simpa [SlotKind.entry, hashEntryD] using hval)
        (fun j hj hbad => hguard j.val hj (by
          rw [List.getElem?_eq_getElem j.isLt]
          simpa [hashEntryD, List.get_eq_getElem] using congrArg some hbad))
  | fwd stateIn stateOut =>
      exact not_redundantEntryDSPaper_forward_of_no_prior tr idx
        (by simpa [SlotKind.entry, forwardEntryD] using hval)
        (fun j hj => ⟨fun hbad => (hguard j.val hj).1 (by
            rw [List.getElem?_eq_getElem j.isLt]
            simpa [forwardEntryD, List.get_eq_getElem] using congrArg some hbad),
          fun hbad => (hguard j.val hj).2 (by
            rw [List.getElem?_eq_getElem j.isLt]
            simpa [inverseEntryD, List.get_eq_getElem] using congrArg some hbad)⟩)

/-- Shifting a "no prior occurrence below `i`" guard through `eraseIdx`. -/
private lemma firstGuardD_eraseIdx
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
private lemma getElem?_eraseIdxD_shift
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (i : ℕ) (hne : idx.val ≠ i) :
    (tr.eraseIdx idx.val)[if idx.val < i then i - 1 else i]? = tr[i]? := by
  by_cases hidxI : idx.val < i
  · simp only [hidxI, ↓reduceIte]
    rw [List.getElem?_eraseIdx_of_ge (by omega), show i - 1 + 1 = i by omega]
  · simp only [hidxI, ↓reduceIte]
    rw [List.getElem?_eraseIdx_of_lt (by omega)]

/-- A guarded slot shifts through `eraseIdx` of a different index. -/
private lemma SlotKind.ok_eraseIdx (sk : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (i : ℕ) (hne : idx.val ≠ i) (hok : sk.ok tr i) :
    sk.ok (tr.eraseIdx idx.val) (if idx.val < i then i - 1 else i) := by
  obtain ⟨hentry, hguard⟩ := hok
  refine ⟨by rw [getElem?_eraseIdxD_shift tr idx i hne]; exact hentry, ?_⟩
  cases sk with
  | hash stmt capSeg =>
      exact firstGuardD_eraseIdx tr idx
        (fun o => o ≠ some (hashEntryD stmt capSeg)) i hguard
  | fwd stateIn stateOut =>
      exact firstGuardD_eraseIdx tr idx
        (fun o => o ≠ some (forwardEntryD stateIn stateOut) ∧
          o ≠ some (inverseEntryD stateOut stateIn)) i hguard

/-- Two ordered guarded slots, the raw-trace shape of the two-survivor transport. -/
private def TwoSurvivors (sk₁ sk₂ : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ i₁ i₂ : ℕ, i₁ < i₂ ∧ sk₁.ok tr i₁ ∧ sk₂.ok tr i₂

/-- One-step preservation: erasing a paper-redundant entry preserves the two-survivor
shape (the guarded slots themselves are never the erased entry). -/
private lemma twoSurvivors_eraseIdx (sk₁ sk₂ : SlotKind StmtIn U)
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDSPaper idx)
    (hP : TwoSurvivors sk₁ sk₂ tr) : TwoSurvivors sk₁ sk₂ (tr.eraseIdx idx.val) := by
  obtain ⟨i₁, i₂, hlt, hok₁, hok₂⟩ := hP
  have hne₁ : idx.val ≠ i₁ := by
    intro heq
    exact sk₁.not_redundant tr idx (heq ▸ hok₁) hred
  have hne₂ : idx.val ≠ i₂ := by
    intro heq
    exact sk₂.not_redundant tr idx (heq ▸ hok₂) hred
  refine ⟨if idx.val < i₁ then i₁ - 1 else i₁, if idx.val < i₂ then i₂ - 1 else i₂, ?_,
    sk₁.ok_eraseIdx tr idx i₁ hne₁ hok₁, sk₂.ok_eraseIdx tr idx i₂ hne₂ hok₂⟩
  by_cases h₁ : idx.val < i₁
  · have h₂ : idx.val < i₂ := by omega
    simp only [h₁, h₂, ↓reduceIte]
    omega
  · by_cases h₂ : idx.val < i₂
    · simp only [h₁, h₂, ↓reduceIte]
      omega
    · simp only [h₁, h₂, ↓reduceIte]
      omega

/-- **Two-survivor dedup transport**: both guarded slots survive paper dedup, in order. -/
private lemma twoSurvivors_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {sk₁ sk₂ : SlotKind StmtIn U}, TwoSurvivors sk₁ sk₂ tr →
        ∃ j₁ j₂ : ℕ, j₁ < j₂ ∧
          (removeRedundantEntryDSPaper tr).1[j₁]? = some sk₁.entry ∧
          (removeRedundantEntryDSPaper tr).1[j₂]? = some sk₂.entry := by
  intro N
  induction N with
  | zero =>
      intro tr hlen sk₁ sk₂ hP
      obtain ⟨i₁, _i₂, _hlt, ⟨hentry, _⟩, _⟩ := hP
      have hlen0 : tr.length = 0 := Nat.le_zero.mp hlen
      rw [List.length_eq_zero_iff.mp hlen0] at hentry
      simp at hentry
  | succ N ih =>
      intro tr hlen sk₁ sk₂ hP
      rw [removeRedundantEntryDSPaper]
      split
      · rename_i hex
        refine ih _ ?_ (twoSurvivors_eraseIdx sk₁ sk₂ tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · obtain ⟨i₁, i₂, hlt, ⟨he₁, _⟩, ⟨he₂, _⟩⟩ := hP
        exact ⟨i₁, i₂, hlt, he₁, he₂⟩

/-! ## Event landings for the survivor pairs -/

/-- **`Eprp`/`E_func` landing**: two guarded forward slots with the same input force the
permutation-inconsistency event. -/
private lemma e_func_of_twoSurvivors_fwd_same_input
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {sIn out₁ out₂ : CanonicalSpongeState U}
    (h : TwoSurvivors (.fwd sIn out₁) (.fwd sIn out₂) tr) :
    BadEventDSPaper.E_func tr := by
  obtain ⟨j₁, j₂, hlt, he₁, he₂⟩ :=
    twoSurvivors_removeRedundant tr.length tr le_rfl h
  obtain ⟨hL₂, hE₂⟩ := List.getElem?_eq_some_iff.mp he₂
  obtain ⟨hL₁, hE₁⟩ := List.getElem?_eq_some_iff.mp he₁
  unfold BadEventDSPaper.E_func BadEventDSPaper.notFunction
  exact ⟨⟨j₂, hL₂⟩, sIn, out₂, hE₂,
    ⟨j₁, hL₁⟩, Fin.mk_lt_mk.mpr hlt, out₁, Or.inl hE₁⟩

/-- **`Efork,h,p` landing (permutation-late order)**: a guarded hash slot before a guarded
forward slot whose output capacity is the hash answer forces `capacitySegmentDupPerm`. -/
private lemma e_p_of_twoSurvivors_hash_fwd
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    {sIn sOut : CanonicalSpongeState U} (hcap : sOut.capacitySegment = capSeg)
    (h : TwoSurvivors (.hash stmt capSeg) (.fwd sIn sOut) tr) :
    BadEventDSPaper.E_p tr := by
  obtain ⟨j₁, j₂, hlt, he₁, he₂⟩ :=
    twoSurvivors_removeRedundant tr.length tr le_rfl h
  obtain ⟨hL₂, hE₂⟩ := List.getElem?_eq_some_iff.mp he₂
  obtain ⟨hL₁, hE₁⟩ := List.getElem?_eq_some_iff.mp he₁
  unfold BadEventDSPaper.E_p BadEventDSPaper.capacitySegmentDupPerm
  refine ⟨⟨j₂, hL₂⟩, capSeg, ⟨sIn, sOut, hE₂, hcap⟩, ?_⟩
  exact Or.inl ⟨⟨j₁, hL₁⟩, Fin.mk_lt_mk.mpr hlt, stmt, hE₁⟩

/-- **`Efork,h` landing**: two guarded hash slots sharing the answer capacity force
`capacitySegmentDupHash`. -/
private lemma e_h_of_twoSurvivors_hash_hash
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt₁ stmt₂ : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : TwoSurvivors (.hash stmt₁ capSeg) (.hash stmt₂ capSeg) tr) :
    BadEventDSPaper.E_h tr := by
  obtain ⟨j₁, j₂, hlt, he₁, he₂⟩ :=
    twoSurvivors_removeRedundant tr.length tr le_rfl h
  obtain ⟨hL₂, hE₂⟩ := List.getElem?_eq_some_iff.mp he₂
  obtain ⟨hL₁, hE₁⟩ := List.getElem?_eq_some_iff.mp he₁
  unfold BadEventDSPaper.E_h BadEventDSPaper.capacitySegmentDupHash
  exact ⟨⟨j₂, hL₂⟩, capSeg, stmt₂, hE₂, ⟨j₁, hL₁⟩, Fin.mk_lt_mk.mpr hlt,
    stmt₁, Or.inl hE₁⟩

/-! ## Fork uniqueness over the paper bad event -/

/-- Query-state extractor for forward-permutation entries. -/
private def fwdInStateD? (e : OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (CanonicalSpongeState U) :=
  match e with
  | ⟨.inr (.inl sIn), _⟩ => some sIn
  | _ => none

/-- Answer-state extractor for forward-permutation entries. -/
private def fwdOutStateD? (e : OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (CanonicalSpongeState U) :=
  match e with
  | ⟨.inr (.inl _), sOut⟩ => some sOut
  | _ => none

/-- Transport a `List.getElem` along a `Nat` index equality. -/
private lemma getElem_idx_congrD {α : Type _} (l : List α) {i j : ℕ} (h : i = j)
    (hi : i < l.length) : l[i]'hi = l[j]'(h ▸ hi) := by
  subst h
  rfl

/-- Transport a `List.getElem` along a list equality. -/
private lemma getElem_list_congrD {α : Type _} {l l' : List α} (h : l = l') {i : ℕ}
    (hi : i < l.length) : l[i]'hi = l'[i]'(h ▸ hi) := by
  subst h
  rfl

open DuplexSpongeFS.KeyLemmaFoundations in
/-- **Step determinism, paper event**: off `BadEventDSPaper.E`, two family chain steps whose
output capacity segments agree are the same `(input, output)` pair. -/
theorem step_determinism_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (a b : ℕ) (haO : a < p.1.outputState.length) (haI : a < p.1.inputState.length)
    (hbO : b < q.1.outputState.length) (hbI : b < q.1.inputState.length)
    (hcap : (p.1.outputState[a]'haO).capacitySegment =
      (q.1.outputState[b]'hbO).capacitySegment) :
    p.1.inputState[a]'haI = q.1.inputState[b]'hbI
      ∧ p.1.outputState[a]'haO = q.1.outputState[b]'hbO := by
  classical
  unfold Backtrack.J_BT at hp hq
  rw [Finset.mem_image] at hp hq
  obtain ⟨seqP, _hpS, rfl⟩ := hp
  obtain ⟨seqQ, _hqS, rfl⟩ := hq
  dsimp only at haO haI hbO hbI hcap ⊢
  set idxP := (Backtrack.BacktrackSequence.Index tr state seqP).2 ⟨a, haI⟩ with hidxP
  set idxQ := (Backtrack.BacktrackSequence.Index tr state seqQ).2 ⟨b, hbI⟩ with hidxQ
  have hfwdP0 := index_entry_forward_of_not_E tr state seqP hE a haO
  have hfwdQ0 := index_entry_forward_of_not_E tr state seqQ hE b hbO
  have hfwdP : tr[idxP.val]? =
      some (forwardEntryD (seqP.inputState[a]'haI) (seqP.outputState[a]'haO)) := by
    simpa [idxP, hidxP, forwardEntryD] using hfwdP0
  have hfwdQ : tr[idxQ.val]? =
      some (forwardEntryD (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := by
    simpa [idxQ, hidxQ, forwardEntryD] using hfwdQ0
  have hfirstP : ∀ j : Fin tr.length, j.val < idxP.val →
      tr[j] ≠ forwardEntryD (seqP.inputState[a]'haI) (seqP.outputState[a]'haO) ∧
        tr[j] ≠ inverseEntryD (seqP.outputState[a]'haO) (seqP.inputState[a]'haI) := by
    intro j hj
    have hnp :=
      Backtrack.BacktrackSequence.index_perm_no_prior_of_lt tr state seqP ⟨a, haI⟩ haO j
        (by simpa [idxP, hidxP] using hj)
    exact ⟨by simpa [forwardEntryD] using hnp.1, by simpa [inverseEntryD] using hnp.2⟩
  have hfirstQ : ∀ j : Fin tr.length, j.val < idxQ.val →
      tr[j] ≠ forwardEntryD (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO) ∧
        tr[j] ≠ inverseEntryD (seqQ.outputState[b]'hbO) (seqQ.inputState[b]'hbI) := by
    intro j hj
    have hnp :=
      Backtrack.BacktrackSequence.index_perm_no_prior_of_lt tr state seqQ ⟨b, hbI⟩ hbO j
        (by simpa [idxQ, hidxQ] using hj)
    exact ⟨by simpa [forwardEntryD] using hnp.1, by simpa [inverseEntryD] using hnp.2⟩
  by_cases hslot : idxP = idxQ
  · have hEq? :
        (some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqP.inputState[a]'haI) (seqP.outputState[a]'haO)) :
          Option (OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
        = some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := by
      calc
        (some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqP.inputState[a]'haI) (seqP.outputState[a]'haO)) :
          Option (OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
            = tr[idxP.val]? := hfwdP.symm
        _ = tr[idxQ.val]? := by simp [hslot]
        _ = some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := hfwdQ
    have hEq := Option.some.inj hEq?
    simpa [forwardEntryD] using hEq
  · exfalso
    obtain ⟨hPLt, hPEq⟩ := List.getElem?_eq_some_iff.mp hfwdP
    obtain ⟨hQLt, hQEq⟩ := List.getElem?_eq_some_iff.mp hfwdQ
    rcases lt_or_gt_of_ne hslot with hlt | hgt
    · refine hE (e_of_hasFirstPermCapacityBeforeForwardOutputPaper tr ?_)
      refine ⟨⟨idxQ.val, hQLt⟩, seqQ.inputState[b]'hbI, seqQ.outputState[b]'hbO,
        by simpa [forwardEntryD] using hQEq, ?_,
        ⟨idxP.val, hPLt⟩, Fin.mk_lt_mk.mpr (by simpa [idxP, idxQ, hidxP, hidxQ] using hlt),
        seqP.inputState[a]'haI, seqP.outputState[a]'haO, Or.inl ?_, Or.inl hcap⟩
      · intro j hj
        have hq := hfirstQ j (by simpa [idxQ, hidxQ] using hj)
        exact ⟨by simpa [forwardEntryD] using hq.1, by simpa [inverseEntryD] using hq.2⟩
      · simpa [forwardEntryD] using hPEq
    · refine hE (e_of_hasFirstPermCapacityBeforeForwardOutputPaper tr ?_)
      refine ⟨⟨idxP.val, hPLt⟩, seqP.inputState[a]'haI, seqP.outputState[a]'haO,
        by simpa [forwardEntryD] using hPEq, ?_,
        ⟨idxQ.val, hQLt⟩, Fin.mk_lt_mk.mpr (by simpa [idxP, idxQ, hidxP, hidxQ] using hgt),
        seqQ.inputState[b]'hbI, seqQ.outputState[b]'hbO, Or.inl ?_, Or.inl hcap.symm⟩
      · intro j hj
        have hp' := hfirstP j (by simpa [idxP, hidxP] using hj)
        exact ⟨by simpa [forwardEntryD] using hp'.1, by simpa [inverseEntryD] using hp'.2⟩
      · simpa [forwardEntryD] using hQEq

open DuplexSpongeFS.KeyLemmaFoundations in
/-- Off `BadEventDSPaper.E`, a hash anchor capacity cannot occur as the answer capacity of a
family chain step. -/
theorem hash_step_separation_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (b : ℕ) (hbO : b < q.1.outputState.length) (hbI : b < q.1.inputState.length)
    (hcap : Vector.drop (p.1.inputState[0]'(by
        rw [p.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R
      = (q.1.outputState[b]'hbO).capacitySegment) : False := by
  classical
  unfold Backtrack.J_BT at hp hq
  rw [Finset.mem_image] at hp hq
  obtain ⟨seqP, _hpS, rfl⟩ := hp
  obtain ⟨seqQ, _hqS, rfl⟩ := hq
  dsimp only at hbO hbI hcap ⊢
  set idxH := (Backtrack.BacktrackSequence.Index tr state seqP).1 with hidxH
  set idxQ := (Backtrack.BacktrackSequence.Index tr state seqQ).2 ⟨b, hbI⟩ with hidxQ
  have hHash0 := Backtrack.BacktrackSequence.index_hash_getElem? tr state seqP
  have hHash : tr[idxH.val]? =
      some (hashEntryD seqP.stmt (Vector.drop (seqP.inputState[0]'(by
        rw [seqP.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R)) := by
    simpa [idxH, hidxH, hashEntryD] using hHash0
  have hHashFirst : ∀ k,
      k < idxH.val →
      tr[k]? ≠ some (hashEntryD seqP.stmt (Vector.drop (seqP.inputState[0]'(by
        rw [seqP.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R)) := by
    intro k hk hbad
    have hkLen : k < tr.length := lt_trans hk idxH.isLt
    rw [List.getElem?_eq_getElem hkLen] at hbad
    exact Backtrack.BacktrackSequence.index_hash_no_prior tr state seqP ⟨k, hkLen⟩
      (by simpa [idxH, hidxH] using hk) (by simpa [hashEntryD] using Option.some.inj hbad)
  have hfwdQ0 := index_entry_forward_of_not_E tr state seqQ hE b hbO
  have hfwdQ : tr[idxQ.val]? =
      some (forwardEntryD (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := by
    simpa [idxQ, hidxQ, forwardEntryD] using hfwdQ0
  have hfirstQ : ∀ k,
      k < idxQ.val →
      tr[k]? ≠ some (forwardEntryD (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) ∧
        tr[k]? ≠ some (inverseEntryD (seqQ.outputState[b]'hbO) (seqQ.inputState[b]'hbI)) := by
    intro k hk
    obtain ⟨hQLt, _hQEq⟩ := List.getElem?_eq_some_iff.mp hfwdQ
    have hkLen : k < tr.length := lt_trans hk hQLt
    have hnp := Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
      tr state seqQ ⟨b, hbI⟩ hbO ⟨k, hkLen⟩ (by simpa [idxQ, hidxQ] using hk)
    constructor
    · intro hsome
      rw [List.getElem?_eq_getElem hkLen] at hsome
      exact hnp.1 (by simpa [forwardEntryD] using Option.some.inj hsome)
    · intro hsome
      rw [List.getElem?_eq_getElem hkLen] at hsome
      exact hnp.2 (by simpa [inverseEntryD] using Option.some.inj hsome)
  by_cases hslot : idxH.val = idxQ.val
  · have hEq? :
        (some (hashEntryD (StmtIn := StmtIn) (U := U) seqP.stmt
          (Vector.drop (seqP.inputState[0]'(by
            rw [seqP.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R)) :
          Option (OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
        = some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := by
      calc
        (some (hashEntryD (StmtIn := StmtIn) (U := U) seqP.stmt
          (Vector.drop (seqP.inputState[0]'(by
            rw [seqP.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R)) :
          Option (OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
            = tr[idxH.val]? := hHash.symm
        _ = tr[idxQ.val]? := by simp [hslot]
        _ = some (forwardEntryD (StmtIn := StmtIn) (U := U)
          (seqQ.inputState[b]'hbI) (seqQ.outputState[b]'hbO)) := hfwdQ
    have hEq := Option.some.inj hEq?
    simp [hashEntryD, forwardEntryD] at hEq
  · rcases lt_or_gt_of_ne hslot with hlt | hgt
    · exact hE (Or.inl (Or.inr (Or.inl
        (e_p_of_twoSurvivors_hash_fwd tr hcap.symm
          ⟨idxH.val, idxQ.val, hlt,
            ⟨hHash, hHashFirst⟩, ⟨hfwdQ, hfirstQ⟩⟩))))
    · exact hE (e_of_hasFirstHashPermCapNatPaper tr
        ⟨idxH.val, idxQ.val, hgt,
          hHash, hHashFirst, seqQ.inputState[b]'hbI, seqQ.outputState[b]'hbO,
          Or.inl hfwdQ, Or.inl hcap.symm⟩)

open DuplexSpongeFS.KeyLemmaFoundations in
/-- Off `BadEventDSPaper.E`, two hash anchors with equal answer capacities carry the same
statement. -/
theorem hash_anchor_unique_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (hcap : Vector.drop (p.1.inputState[0]'(by
        rw [p.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R
      = Vector.drop (q.1.inputState[0]'(by
        rw [q.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R) :
    p.1.stmt = q.1.stmt := by
  classical
  unfold Backtrack.J_BT at hp hq
  rw [Finset.mem_image] at hp hq
  obtain ⟨seqP, _hpS, rfl⟩ := hp
  obtain ⟨seqQ, _hqS, rfl⟩ := hq
  dsimp only at hcap ⊢
  set idxP := (Backtrack.BacktrackSequence.Index tr state seqP).1 with hidxP
  set idxQ := (Backtrack.BacktrackSequence.Index tr state seqQ).1 with hidxQ
  set capP := Vector.drop (seqP.inputState[0]'(by
    rw [seqP.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R with hcapP
  set capQ := Vector.drop (seqQ.inputState[0]'(by
    rw [seqQ.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R with hcapQ
  have hHashP0 := Backtrack.BacktrackSequence.index_hash_getElem? tr state seqP
  have hHashQ0 := Backtrack.BacktrackSequence.index_hash_getElem? tr state seqQ
  have hHashP : tr[idxP.val]? = some (hashEntryD seqP.stmt capP) := by
    simpa [idxP, hidxP, capP, hcapP, hashEntryD] using hHashP0
  have hHashQ : tr[idxQ.val]? = some (hashEntryD seqQ.stmt capQ) := by
    simpa [idxQ, hidxQ, capQ, hcapQ, hashEntryD] using hHashQ0
  have hFirstP : ∀ k, k < idxP.val → tr[k]? ≠ some (hashEntryD seqP.stmt capP) := by
    intro k hk hbad
    have hkLen : k < tr.length := lt_trans hk idxP.isLt
    rw [List.getElem?_eq_getElem hkLen] at hbad
    exact Backtrack.BacktrackSequence.index_hash_no_prior tr state seqP ⟨k, hkLen⟩
      (by simpa [idxP, hidxP] using hk)
      (by simpa [capP, hcapP, hashEntryD] using Option.some.inj hbad)
  have hFirstQ : ∀ k, k < idxQ.val → tr[k]? ≠ some (hashEntryD seqQ.stmt capQ) := by
    intro k hk hbad
    have hkLen : k < tr.length := lt_trans hk idxQ.isLt
    rw [List.getElem?_eq_getElem hkLen] at hbad
    exact Backtrack.BacktrackSequence.index_hash_no_prior tr state seqQ ⟨k, hkLen⟩
      (by simpa [idxQ, hidxQ] using hk)
      (by simpa [capQ, hcapQ, hashEntryD] using Option.some.inj hbad)
  by_cases hslot : idxP = idxQ
  · have hEq? : some (hashEntryD seqP.stmt capP) = some (hashEntryD seqQ.stmt capQ) := by
      rw [← hHashP, ← hHashQ]
      simp [hslot]
    have hEq := Option.some.inj hEq?
    simp only [hashEntryD, Sigma.mk.injEq, Sum.inl.injEq] at hEq
    exact hEq.1
  · exfalso
    have hcapPQ : capP = capQ := by
      simpa [capP, hcapP, capQ, hcapQ] using hcap
    rcases lt_or_gt_of_ne hslot with hlt | hgt
    · have hHashP' : tr[idxP.val]? = some (hashEntryD seqP.stmt capQ) := by
        simpa [hcapPQ] using hHashP
      have hFirstP' : ∀ k, k < idxP.val → tr[k]? ≠ some (hashEntryD seqP.stmt capQ) := by
        simpa [hcapPQ] using hFirstP
      exact hE (Or.inl (Or.inl (e_h_of_twoSurvivors_hash_hash tr
        ⟨idxP.val, idxQ.val, by simpa [idxP, idxQ, hidxP, hidxQ] using hlt,
          ⟨hHashP', hFirstP'⟩, ⟨hHashQ, hFirstQ⟩⟩)))
    · have hHashQ' : tr[idxQ.val]? = some (hashEntryD seqQ.stmt capP) := by
        simpa [hcapPQ] using hHashQ
      have hFirstQ' : ∀ k, k < idxQ.val → tr[k]? ≠ some (hashEntryD seqQ.stmt capP) := by
        simpa [hcapPQ] using hFirstQ
      exact hE (Or.inl (Or.inl (e_h_of_twoSurvivors_hash_hash tr
        ⟨idxQ.val, idxP.val, by simpa [idxP, idxQ, hidxP, hidxQ] using hgt,
          ⟨hHashQ', hFirstQ'⟩, ⟨hHashP, hFirstP⟩⟩)))

open DuplexSpongeFS.KeyLemmaFoundations in
/-- End-aligned input agreement: off `BadEventDSPaper.E`, two family sequences agree at
end-aligned input positions. -/
theorem aligned_inputs_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S) :
    ∀ ι : ℕ, ι ≤ p.1.outputState.length → ι ≤ q.1.outputState.length →
      p.1.inputState[p.1.outputState.length - ι]'(by
        rw [p.1.inputState_length_eq_outputState_length_succ]; omega)
      = q.1.inputState[q.1.outputState.length - ι]'(by
        rw [q.1.inputState_length_eq_outputState_length_succ]; omega) := by
  intro ι
  induction ι with
  | zero =>
      intro _ _
      have e1 : p.1.inputState[p.1.outputState.length - 0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]; omega) = state := by
        rw [getElem_idx_congrD p.1.inputState
          (show p.1.outputState.length - 0 = p.1.inputState.length - 1 by
            rw [p.1.inputState_length_eq_outputState_length_succ]; omega)]
        exact p.1.last_inputState_eq_state
      have e2 : q.1.inputState[q.1.outputState.length - 0]'(by
          rw [q.1.inputState_length_eq_outputState_length_succ]; omega) = state := by
        rw [getElem_idx_congrD q.1.inputState
          (show q.1.outputState.length - 0 = q.1.inputState.length - 1 by
            rw [q.1.inputState_length_eq_outputState_length_succ]; omega)]
        exact q.1.last_inputState_eq_state
      rw [e1, e2]
  | succ ι ih =>
      intro h1 h2
      have ihv := ih (Nat.le_of_succ_le h1) (Nat.le_of_succ_le h2)
      have haO : p.1.outputState.length - (ι + 1) < p.1.outputState.length := by omega
      have hbO : q.1.outputState.length - (ι + 1) < q.1.outputState.length := by omega
      have hcontP := p.1.capacitySegment_output_eq_input
        ⟨p.1.outputState.length - (ι + 1), haO⟩
      have hcontQ := q.1.capacitySegment_output_eq_input
        ⟨q.1.outputState.length - (ι + 1), hbO⟩
      simp only [Fin.getElem_fin] at hcontP hcontQ
      rw [getElem_idx_congrD p.1.inputState
        (show p.1.outputState.length - (ι + 1) + 1 = p.1.outputState.length - ι by
          omega)] at hcontP
      rw [getElem_idx_congrD q.1.inputState
        (show q.1.outputState.length - (ι + 1) + 1 = q.1.outputState.length - ι by
          omega)] at hcontQ
      exact (step_determinism_paper tr state S hE p q hp hq _ _ haO
        (by rw [p.1.inputState_length_eq_outputState_length_succ]; omega) hbO
        (by rw [q.1.inputState_length_eq_outputState_length_succ]; omega)
        (by rw [hcontP, hcontQ, ihv])).1

open DuplexSpongeFS.KeyLemmaFoundations in
/-- Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor
capacity on a chain-step output of the longer one. -/
theorem length_not_lt_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (hlt : p.1.outputState.length < q.1.outputState.length) : False := by
  have hal := aligned_inputs_paper tr state S hE p q hp hq p.1.outputState.length le_rfl
    (le_of_lt hlt)
  rw [getElem_idx_congrD p.1.inputState
    (show p.1.outputState.length - p.1.outputState.length = 0 by omega)] at hal
  have hbO : q.1.outputState.length - p.1.outputState.length - 1
      < q.1.outputState.length := by omega
  have hbI : q.1.outputState.length - p.1.outputState.length - 1
      < q.1.inputState.length := by
    rw [q.1.inputState_length_eq_outputState_length_succ]
    omega
  have hstep := q.1.capacitySegment_output_eq_input
    ⟨q.1.outputState.length - p.1.outputState.length - 1, hbO⟩
  simp only [Fin.getElem_fin] at hstep
  rw [getElem_idx_congrD q.1.inputState
    (show q.1.outputState.length - p.1.outputState.length - 1 + 1
        = q.1.outputState.length - p.1.outputState.length by omega)] at hstep
  refine hash_step_separation_paper tr state S hE p q hp hq _ hbO hbI ?_
  rw [hal, hstep]

open DuplexSpongeFS.KeyLemmaFoundations in
/-- **CO25 Lemma 5.14, paper semantics — DISCHARGED**: off `BadEventDSPaper.E`, the
backtrack family has at most one maximal sequence. -/
theorem lemma5_14_paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ BadEventDSPaper.E tr) :
    ¬ E_fork_honest tr state S := by
  intro hfork
  unfold E_fork_honest at hfork
  obtain ⟨s₁, hs₁, s₂, hs₂, hneq⟩ := Finset.one_lt_card.mp hfork
  classical
  have hp : (⟨s₁, Backtrack.BacktrackSequence.Index tr state s₁⟩ :
      Sigma fun seq : Backtrack.BacktrackSequence tr state =>
        Backtrack.BacktrackIndexList tr seq) ∈ Backtrack.J_BT S := by
    unfold Backtrack.J_BT
    exact Finset.mem_image_of_mem _ hs₁
  have hq : (⟨s₂, Backtrack.BacktrackSequence.Index tr state s₂⟩ :
      Sigma fun seq : Backtrack.BacktrackSequence tr state =>
        Backtrack.BacktrackIndexList tr seq) ∈ Backtrack.J_BT S := by
    unfold Backtrack.J_BT
    exact Finset.mem_image_of_mem _ hs₂
  have hlen : s₁.outputState.length = s₂.outputState.length := by
    rcases Nat.lt_trichotomy s₁.outputState.length s₂.outputState.length with h | h | h
    · exact absurd (length_not_lt_paper tr state S hE _ _ hp hq h) not_false
    · exact h
    · exact absurd (length_not_lt_paper tr state S hE _ _ hq hp h) not_false
  have hlenIn : s₁.inputState.length = s₂.inputState.length := by
    rw [s₁.inputState_length_eq_outputState_length_succ,
      s₂.inputState_length_eq_outputState_length_succ, hlen]
  have hin : s₁.inputState = s₂.inputState := by
    apply List.ext_getElem hlenIn
    intro k hk1 hk2
    have hkO : k ≤ s₁.outputState.length := by
      rw [s₁.inputState_length_eq_outputState_length_succ] at hk1
      omega
    have hb1 : s₁.outputState.length - k ≤ s₁.outputState.length := by omega
    have hb2 : s₁.outputState.length - k ≤ s₂.outputState.length := by omega
    have hal := aligned_inputs_paper tr state S hE _ _ hp hq
      (s₁.outputState.length - k) hb1 hb2
    dsimp only at hal
    rw [getElem_idx_congrD s₁.inputState
        (show s₁.outputState.length - (s₁.outputState.length - k) = k by omega),
      getElem_idx_congrD s₂.inputState
        (show s₂.outputState.length - (s₁.outputState.length - k) = k by omega)] at hal
    exact hal
  have hout : s₁.outputState = s₂.outputState := by
    apply List.ext_getElem hlen
    intro k hk1 hk2
    have hk1I : k < s₁.inputState.length := by
      rw [s₁.inputState_length_eq_outputState_length_succ]
      omega
    have hk2I : k < s₂.inputState.length := by
      rw [s₂.inputState_length_eq_outputState_length_succ]
      omega
    have hcontP := s₁.capacitySegment_output_eq_input ⟨k, hk1⟩
    have hcontQ := s₂.capacitySegment_output_eq_input ⟨k, hk2⟩
    simp only [Fin.getElem_fin] at hcontP hcontQ
    have hinK : s₁.inputState[k + 1]'(by
        rw [s₁.inputState_length_eq_outputState_length_succ]; omega)
        = s₂.inputState[k + 1]'(by
        rw [s₂.inputState_length_eq_outputState_length_succ]; omega) := by
      rw [getElem_list_congrD hin]
    exact (step_determinism_paper tr state S hE _ _ hp hq k k hk1 hk1I hk2 hk2I
      (by dsimp only; rw [hcontP, hcontQ, hinK])).2
  have hstmt : s₁.stmt = s₂.stmt := by
    refine hash_anchor_unique_paper tr state S hE _ _ hp hq ?_
    dsimp only
    rw [getElem_list_congrD hin]
  apply hneq
  cases s₁
  cases s₂
  dsimp only at hstmt hin hout
  subst hstmt
  subst hin
  subst hout
  rfl

/-- The residual `Lemma5_14HonestResidualPaper`, discharged. -/
theorem lemma5_14HonestResidualPaper_holds :
    Lemma5_14HonestResidualPaper StmtIn U :=
  fun tr state S hE => lemma5_14_paper tr state S hE

end DuplexSpongeFS.Sponge316


/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.Sponge316.step_determinism_paper
#print axioms DuplexSpongeFS.Sponge316.hash_step_separation_paper
#print axioms DuplexSpongeFS.Sponge316.hash_anchor_unique_paper
#print axioms DuplexSpongeFS.Sponge316.aligned_inputs_paper
#print axioms DuplexSpongeFS.Sponge316.length_not_lt_paper
#print axioms DuplexSpongeFS.Sponge316.lemma5_14HonestResidualPaper_holds
