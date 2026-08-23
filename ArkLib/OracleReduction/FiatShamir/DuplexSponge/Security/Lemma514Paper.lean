/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 M2 wave-4 — CO25 Lemma 5.14 (honest fork) over the PAPER bad event:

  `lemma514Paper : ¬ EPaper tr → ¬ E_fork_honest tr state S`

over the IN-TREE honest fork event (`DuplexSpongeFS.KeyLemmaFoundations.E_fork_honest`,
CO25 Def. 5.13: `|S_BT(tr, s)| > 1`) and the PAPER bad event (`DuplexSpongeFS.Paper.EPaper`,
CO25 Eq. 27 with the B1/B2 repairs).  The in-tree statement over the deviant `E` is
REFUTED (`Lemma514ForkFalse.lean`); this is the Def-5.5/Eq-26-faithful re-proof.

Architecture (CO25 Claim 5.19's argument, transported to the honest surface):
* Off `EPaper`, every `J_BT` chain slot is FORWARD-form (`ePaper_of_jbt_inv_slot'`
  fires `EPaper` on any inverse-form slot — the Lemma 5.12 core).
* **U1 `step_determinism`**: two chain steps (of possibly different family sequences)
  with equal output-capacity segments are the SAME `(input, output)` pair — distinct
  pairs give distinct forward first-of-class survivors with equal answer capacities,
  firing C1 (`ePaper_of_answerCap_pair`).  This is Eq. 44's `E_fork,p`/`E_prp` step.
* **U2 `hash_anchor_unique`**: two hash anchors with equal answer capacities carry the
  same statement (E_h answer-answer collision otherwise).  Eq. 39 / Eq. 45's `𝕩` step.
* **U3 `hash_step_separation`**: no chain-step output capacity equals a hash-anchor
  capacity (E_h/E_p hash-perm collision otherwise).  The `m₁ = m₂` step (Eq. 41 use).
* `aligned_inputs`: downward induction from the shared end state — aligned input states
  of two family sequences agree (base: both end at `state`; step: U1 via continuity).
* `lemma514Paper`: two distinct members of `seqFamily` would have equal lengths (U3),
  equal input/output lists (alignment + U1), and equal statements (U2) — hence be equal
  (proof fields are propositions), contradiction; so `card ≤ 1`.

All sorry-free; `#print axioms` at the end.
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsCoincidence
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma516Paper

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- Transport a `List.getElem` along a `Nat` index equality. -/
private lemma getElem_idx_congr {α : Type _} (l : List α) {i j : ℕ} (h : i = j)
    (hi : i < l.length) : l[i]'hi = l[j]'(h ▸ hi) := by subst h; rfl

/-- Transport a `List.getElem` along a list equality. -/
private lemma getElem_list_congr {α : Type _} {l l' : List α} (h : l = l') {i : ℕ}
    (hi : i < l.length) : l[i]'hi = l'[i]'(h ▸ hi) := by subst h; rfl

/-- Query-state extractor for forward-permutation entries (avoids the dependent-`Sigma`
`HEq` when comparing two forward entries componentwise). -/
private def fwdInState? (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (CanonicalSpongeState U) :=
  match e with
  | ⟨.inr (.inl sIn), _⟩ => some sIn
  | _ => none

/-- Answer-state extractor for forward-permutation entries. -/
private def fwdOutState? (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (CanonicalSpongeState U) :=
  match e with
  | ⟨.inr (.inl _), sOut⟩ => some sOut
  | _ => none

/-- **U1 (step determinism, paper event)** — CO25 Claim 5.19, Eq. 44 step: off `EPaper`,
two chain steps of family sequences with equal output-capacity segments are the same
`(input, output)` state pair.  Off `EPaper` both `J_BT` slots are forward-form
(`ePaper_of_jbt_inv_slot'`); same slot forces the pairs equal by injectivity, and distinct
slots are two forward first-of-class survivors with equal answer capacities — C1. -/
theorem step_determinism
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (a b : ℕ) (haO : a < p.1.outputState.length) (haI : a < p.1.inputState.length)
    (hbO : b < q.1.outputState.length) (hbI : b < q.1.inputState.length)
    (hcap : (p.1.outputState[a]'haO).capacitySegment
      = (q.1.outputState[b]'hbO).capacitySegment) :
    p.1.inputState[a]'haI = q.1.inputState[b]'hbI
      ∧ p.1.outputState[a]'haO = q.1.outputState[b]'hbO := by
  have hkP : (p.2.2 ⟨a, haI⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S p hp a haO haI
  have hkQ : (q.2.2 ⟨b, hbI⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S q hq b hbO hbI
  rcases jbt_perm_slot_cases' tr state S p hp a haO haI hkP with hfwdP | hinvP
  case inr => exact absurd (ePaper_of_jbt_inv_slot' tr state S p hp a haO haI hkP hinvP) hnE
  rcases jbt_perm_slot_cases' tr state S q hq b hbO hbI hkQ with hfwdQ | hinvQ
  case inr => exact absurd (ePaper_of_jbt_inv_slot' tr state S q hq b hbO hbI hkQ hinvQ) hnE
  by_cases hslot : (⟨(p.2.2 ⟨a, haI⟩).val, hkP⟩ : Fin tr.length)
      = (⟨(q.2.2 ⟨b, hbI⟩).val, hkQ⟩ : Fin tr.length)
  · -- same slot: same forward entry; injectivity gives both equalities
    have hEq : tr[(⟨(p.2.2 ⟨a, haI⟩).val, hkP⟩ : Fin tr.length)]
        = tr[(⟨(q.2.2 ⟨b, hbI⟩).val, hkQ⟩ : Fin tr.length)] :=
      congrArg (fun k : Fin tr.length => tr[k]) hslot
    rw [hfwdP, hfwdQ] at hEq
    have h1 := congrArg (fwdInState? (StmtIn := StmtIn) (U := U)) hEq
    have h2 := congrArg (fwdOutState? (StmtIn := StmtIn) (U := U)) hEq
    simp only [fwdInState?, fwdOutState?, Option.some.injEq] at h1 h2
    exact ⟨h1, h2⟩
  · -- distinct slots: two forward first-of-class survivors with equal answer caps — C1
    have hfocP := jbt_perm_slot_firstOfClassAt' tr state S p hp a haO haI hkP
    have hfocQ := jbt_perm_slot_firstOfClassAt' tr state S q hq b hbO hbI hkQ
    rcases lt_or_gt_of_ne hslot with hlt | hgt
    · refine absurd (ePaper_of_answerCap_pair tr hlt hfocP hfocQ ((hfocQ _ hlt).1) ?_) hnE
      rw [hfwdP, hfwdQ]
      simpa only [answerCap_fwd] using hcap
    · refine absurd (ePaper_of_answerCap_pair tr hgt hfocQ hfocP ((hfocP _ hgt).1) ?_) hnE
      rw [hfwdP, hfwdQ]
      simpa only [answerCap_fwd] using hcap.symm

/-- **U3 (anchor separation, paper event)**: off `EPaper`, no chain-step output capacity
equals a hash-anchor answer capacity (the `m₁ = m₂` ingredient of CO25 Claim 5.19,
Eq. 45). -/
theorem hash_step_separation
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (b : ℕ) (hbO : b < q.1.outputState.length) (hbI : b < q.1.inputState.length)
    (hcap : Vector.drop (p.1.inputState[0]'(by
        rw [p.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R
      = (q.1.outputState[b]'hbO).capacitySegment) : False := by
  have hkQ : (q.2.2 ⟨b, hbI⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S q hq b hbO hbI
  rcases jbt_perm_slot_cases' tr state S q hq b hbO hbI hkQ with hfwdQ | hinvQ
  case inr => exact absurd (ePaper_of_jbt_inv_slot' tr state S q hq b hbO hbI hkQ hinvQ) hnE
  have hHashEq := jbt_hash_getElem'' tr state S p hp
  have hfocH := jbt_hash_firstOfClassAt'' tr state S p hp
  have hfocQ := jbt_perm_slot_firstOfClassAt' tr state S q hq b hbO hbI hkQ
  have hne : p.2.1 ≠ (⟨(q.2.2 ⟨b, hbI⟩).val, hkQ⟩ : Fin tr.length) := by
    intro hEq
    have hget : tr[p.2.1] = tr[(⟨(q.2.2 ⟨b, hbI⟩).val, hkQ⟩ : Fin tr.length)] :=
      congrArg (fun k : Fin tr.length => tr[k]) hEq
    rw [hHashEq, hfwdQ] at hget
    simp at hget
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine absurd (ePaper_of_answerCap_pair tr hlt hfocH hfocQ ((hfocQ _ hlt).1) ?_) hnE
    rw [hHashEq, hfwdQ]
    simpa only [answerCap_hash, answerCap_fwd] using hcap
  · refine absurd (ePaper_of_answerCap_pair tr hgt hfocQ hfocH ((hfocH _ hgt).1) ?_) hnE
    rw [hHashEq, hfwdQ]
    simpa only [answerCap_hash, answerCap_fwd] using hcap.symm

/-- **U2 (anchor uniqueness, paper event)**: off `EPaper`, two hash anchors with equal
answer capacities carry the same statement (CO25 Claim 5.19, the Eq. 39/45 `𝕩` step). -/
theorem hash_anchor_unique
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (hcap : Vector.drop (p.1.inputState[0]'(by
        rw [p.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R
      = Vector.drop (q.1.inputState[0]'(by
        rw [q.1.inputState_length_eq_outputState_length_succ]; omega)) SpongeSize.R) :
    p.1.stmt = q.1.stmt := by
  have hHashP := jbt_hash_getElem'' tr state S p hp
  have hHashQ := jbt_hash_getElem'' tr state S q hq
  by_cases hslot : p.2.1 = q.2.1
  · -- same slot: same hash entry, statements equal
    have hEq : tr[p.2.1] = tr[q.2.1] :=
      congrArg (fun k : Fin tr.length => tr[k]) hslot
    rw [hHashP, hHashQ] at hEq
    simp only [Sigma.mk.injEq, Sum.inl.injEq, heq_eq_eq] at hEq
    exact hEq.1
  · -- distinct slots: E_h answer-answer collision — C1
    have hfocP := jbt_hash_firstOfClassAt'' tr state S p hp
    have hfocQ := jbt_hash_firstOfClassAt'' tr state S q hq
    rcases lt_or_gt_of_ne hslot with hlt | hgt
    · refine absurd (ePaper_of_answerCap_pair tr hlt hfocP hfocQ ((hfocQ _ hlt).1) ?_) hnE
      rw [hHashP, hHashQ]
      simpa only [answerCap_hash] using hcap
    · refine absurd (ePaper_of_answerCap_pair tr hgt hfocQ hfocP ((hfocP _ hgt).1) ?_) hnE
      rw [hHashP, hHashQ]
      simpa only [answerCap_hash] using hcap.symm

/-- **End-aligned input agreement** (CO25 Claim 5.19, Eq. 44 induction): off `EPaper`, the
input states of two family sequences agree at end-aligned positions — both chains end at
`state`, and each backward step is forced by `step_determinism` through continuity. -/
theorem aligned_inputs
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr)
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
        rw [getElem_idx_congr p.1.inputState
          (show p.1.outputState.length - 0 = p.1.inputState.length - 1 by
            rw [p.1.inputState_length_eq_outputState_length_succ]; omega)]
        exact p.1.last_inputState_eq_state
      have e2 : q.1.inputState[q.1.outputState.length - 0]'(by
          rw [q.1.inputState_length_eq_outputState_length_succ]; omega) = state := by
        rw [getElem_idx_congr q.1.inputState
          (show q.1.outputState.length - 0 = q.1.inputState.length - 1 by
            rw [q.1.inputState_length_eq_outputState_length_succ]; omega)]
        exact q.1.last_inputState_eq_state
      rw [e1, e2]
  | succ ι ih =>
      intro h1 h2
      have ihv := ih (Nat.le_of_succ_le h1) (Nat.le_of_succ_le h2)
      have haO : p.1.outputState.length - (ι + 1) < p.1.outputState.length := by omega
      have hbO : q.1.outputState.length - (ι + 1) < q.1.outputState.length := by omega
      -- continuity at the step preceding the aligned position
      have hcontP := p.1.capacitySegment_output_eq_input
        ⟨p.1.outputState.length - (ι + 1), haO⟩
      have hcontQ := q.1.capacitySegment_output_eq_input
        ⟨q.1.outputState.length - (ι + 1), hbO⟩
      simp only [Fin.getElem_fin] at hcontP hcontQ
      rw [getElem_idx_congr p.1.inputState
        (show p.1.outputState.length - (ι + 1) + 1 = p.1.outputState.length - ι by
          omega)] at hcontP
      rw [getElem_idx_congr q.1.inputState
        (show q.1.outputState.length - (ι + 1) + 1 = q.1.outputState.length - ι by
          omega)] at hcontQ
      exact (step_determinism tr state S hnE p q hp hq _ _ haO
        (by rw [p.1.inputState_length_eq_outputState_length_succ]; omega) hbO
        (by rw [q.1.inputState_length_eq_outputState_length_succ]; omega)
        (by rw [hcontP, hcontQ, ihv])).1

/-- Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor
capacity on a chain-step output of the longer one — `hash_step_separation`. -/
theorem length_not_lt
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr)
    (p q : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (hq : q ∈ Backtrack.J_BT S)
    (hlt : p.1.outputState.length < q.1.outputState.length) : False := by
  have hal := aligned_inputs tr state S hnE p q hp hq p.1.outputState.length le_rfl
    (le_of_lt hlt)
  rw [getElem_idx_congr p.1.inputState
    (show p.1.outputState.length - p.1.outputState.length = 0 by omega)] at hal
  -- the chain-2 step whose output capacity is the chain-1 anchor capacity
  have hbO : q.1.outputState.length - p.1.outputState.length - 1
      < q.1.outputState.length := by omega
  have hbI : q.1.outputState.length - p.1.outputState.length - 1
      < q.1.inputState.length := by
    rw [q.1.inputState_length_eq_outputState_length_succ]; omega
  have hstep := q.1.capacitySegment_output_eq_input
    ⟨q.1.outputState.length - p.1.outputState.length - 1, hbO⟩
  simp only [Fin.getElem_fin] at hstep
  rw [getElem_idx_congr q.1.inputState
    (show q.1.outputState.length - p.1.outputState.length - 1 + 1
        = q.1.outputState.length - p.1.outputState.length by omega)] at hstep
  refine hash_step_separation tr state S hnE p q hp hq _ hbO hbI ?_
  rw [hal, hstep]

/-- **CO25 Lemma 5.14 over the paper event** (M2b, Def-5.5/Eq-26-faithful): off `EPaper`
the backtrack family has at most one maximal sequence.  Two distinct members would agree
in length (`length_not_lt`), input and output lists (`aligned_inputs` +
`step_determinism`), and statement (`hash_anchor_unique`) — hence be equal. -/
theorem lemma514Paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr) :
    ¬ KeyLemmaFoundations.E_fork_honest tr state S := by
  intro hfork
  unfold KeyLemmaFoundations.E_fork_honest at hfork
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
  -- equal lengths
  have hlen : s₁.outputState.length = s₂.outputState.length := by
    rcases Nat.lt_trichotomy s₁.outputState.length s₂.outputState.length with h | h | h
    · exact absurd (length_not_lt tr state S hnE _ _ hp hq h) not_false
    · exact h
    · exact absurd (length_not_lt tr state S hnE _ _ hq hp h) not_false
  have hlenIn : s₁.inputState.length = s₂.inputState.length := by
    rw [s₁.inputState_length_eq_outputState_length_succ,
      s₂.inputState_length_eq_outputState_length_succ, hlen]
  -- equal input lists (end-aligned agreement at every position)
  have hin : s₁.inputState = s₂.inputState := by
    apply List.ext_getElem hlenIn
    intro k hk1 hk2
    have hkO : k ≤ s₁.outputState.length := by
      rw [s₁.inputState_length_eq_outputState_length_succ] at hk1; omega
    have hb1 : s₁.outputState.length - k ≤ s₁.outputState.length := by omega
    have hb2 : s₁.outputState.length - k ≤ s₂.outputState.length := by omega
    have hal := aligned_inputs tr state S hnE _ _ hp hq
      (s₁.outputState.length - k) hb1 hb2
    dsimp only at hal
    rw [getElem_idx_congr s₁.inputState
        (show s₁.outputState.length - (s₁.outputState.length - k) = k by omega),
      getElem_idx_congr s₂.inputState
        (show s₂.outputState.length - (s₁.outputState.length - k) = k by omega)] at hal
    exact hal
  -- equal output lists (per-step determinism through continuity + input agreement)
  have hout : s₁.outputState = s₂.outputState := by
    apply List.ext_getElem hlen
    intro k hk1 hk2
    have hk1I : k < s₁.inputState.length := by
      rw [s₁.inputState_length_eq_outputState_length_succ]; omega
    have hk2I : k < s₂.inputState.length := by
      rw [s₂.inputState_length_eq_outputState_length_succ]; omega
    have hcontP := s₁.capacitySegment_output_eq_input ⟨k, hk1⟩
    have hcontQ := s₂.capacitySegment_output_eq_input ⟨k, hk2⟩
    simp only [Fin.getElem_fin] at hcontP hcontQ
    have hinK : s₁.inputState[k + 1]'(by
        rw [s₁.inputState_length_eq_outputState_length_succ]; omega)
        = s₂.inputState[k + 1]'(by
        rw [s₂.inputState_length_eq_outputState_length_succ]; omega) := by
      rw [getElem_list_congr hin]
    exact (step_determinism tr state S hnE _ _ hp hq k k hk1 hk1I hk2 hk2I
      (by dsimp only; rw [hcontP, hcontQ, hinK])).2
  -- equal statements (anchor uniqueness at the shared initial capacity)
  have hstmt : s₁.stmt = s₂.stmt := by
    refine hash_anchor_unique tr state S hnE _ _ hp hq ?_
    dsimp only
    rw [getElem_list_congr hin]
  -- structures with equal data fields are equal (proof fields are propositions)
  apply hneq
  cases s₁
  cases s₂
  dsimp only at hstmt hin hout
  subst hstmt
  subst hin
  subst hout
  rfl

end DuplexSpongeFS.Paper

#print axioms DuplexSpongeFS.Paper.step_determinism
#print axioms DuplexSpongeFS.Paper.hash_step_separation
#print axioms DuplexSpongeFS.Paper.hash_anchor_unique
#print axioms DuplexSpongeFS.Paper.aligned_inputs
#print axioms DuplexSpongeFS.Paper.length_not_lt
#print axioms DuplexSpongeFS.Paper.lemma514Paper
