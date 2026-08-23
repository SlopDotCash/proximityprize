/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 M2 L516 — paper-faithful CO25 Lemma 5.16 over `EPaper`:

  `lemma516Paper : ¬ EPaper tr → ¬ E_time_honest tr state S`

over the IN-TREE honest timing events (`DuplexSpongeFS.KeyLemmaFoundations.E_time_honest`,
CO25 Def. 5.15 Eqs. 41/42) and the PAPER bad event (`DuplexSpongeFS.Paper.EPaper`,
CO25 Eq. 27 with the B1/B2 repairs).

Architecture (per the CO25 §5.6 roadmap):
* J_BT → `FirstOfClassAt` bridges: the public `Sponge316.jbt_*` no-prior lemmas say a `J_BT`
  slot has no earlier same-or-mirror occurrence, which is literally `M2Engine.FirstOfClassAt`.
  The unconditional either-direction payload lemma (`jbt_perm_getElem?_of_lt'`) is rebuilt
  locally from the public `Backtrack.BacktrackSequence.index_perm_getElem?_of_lt` by
  unfolding `J_BT` (the in-tree `_of_not_E` variant is conditioned on the deviant `E`).
* `ePaper_of_jbt_inv_slot'` (the Lemma 5.12 core, reused here for the mirror-form cases):
  if any chain step's `J_BT` slot carries the inverse-form entry, `EPaper` fires by
  downward descent — step 0 collides answer-answer with the hash anchor; step m+1 either
  recurses (previous step also inverse) or collides answer-answer with the previous
  forward step via chain continuity (C1).
* Hash half (Eq. 41): the first chain slot precedes the hash anchor; forward form fires C2
  (query cap of the chain step = answer cap of the hash anchor, strictly earlier), inverse
  form is delegated to the 5.12 core.
* Perm half (Eq. 42): slot(step ι) > slot(step ι+1); if step ι is inverse-form delegate to
  the 5.12 core; else its answer cap is the continuity capacity c = cap(s_out_ι) =
  cap(s_in_{ι+1}), and the (strictly earlier) step ι+1 slot carries c on its query side
  (forward form → C2 strict) or its answer side (inverse form → C1).

Sentinel cases (empty chain / terminal successor index) are discharged by the public
unconditional lemmas `Sponge316.jbt_time_h_outputState_nonempty` and
`Sponge316.jbt_time_p_next_outputState_bound`.

All sorry-free; `#print axioms` at the end.
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsCoincidence
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.HonestConsistency

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## J_BT payload bridges (unconditional; primed local copies where the in-tree export is
conditioned on the deviant `E`) -/

/-- Unconditional either-direction payload of a nonterminal `J_BT` permutation index
(local copy of the lift of `Backtrack.BacktrackSequence.index_perm_getElem?_of_lt` through
`J_BT` membership; the in-tree `jbt_perm_forward_getElem?_of_not_E` is conditioned on the
deviant `E`, which we must not assume). -/
theorem jbt_perm_getElem?_of_lt'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S)
    (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length) :
    GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inr (p.1.outputState[pairIdx.val]'hpair)),
          p.1.inputState[pairIdx]⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
    (trace := tr) (state := state) (seq := seq) (pairIdx := pairIdx) (hpair := hpair)

/-- A nonterminal `J_BT` permutation index is a genuine raw-trace index. -/
theorem jbt_perm_slot_lt'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S)
    (m : ℕ) (hm : m < p.1.outputState.length) (hmIn : m < p.1.inputState.length) :
    (p.2.2 ⟨m, hmIn⟩).val < tr.length := by
  rcases jbt_perm_getElem?_of_lt' tr state S p hp ⟨m, hmIn⟩ hm with h | h
  · exact (List.getElem?_eq_some_iff.mp h).1
  · exact (List.getElem?_eq_some_iff.mp h).1

/-- The raw-trace entry at a nonterminal `J_BT` permutation index is the forward or the
inverse form of that chain step (Nat-index normal form). -/
theorem jbt_perm_slot_cases'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S)
    (m : ℕ) (hm : m < p.1.outputState.length) (hmIn : m < p.1.inputState.length)
    (hk : (p.2.2 ⟨m, hmIn⟩).val < tr.length) :
    tr[(⟨(p.2.2 ⟨m, hmIn⟩).val, hk⟩ : Fin tr.length)] =
        (⟨Sum.inr (Sum.inl (p.1.inputState[m]'hmIn)), p.1.outputState[m]'hm⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
      tr[(⟨(p.2.2 ⟨m, hmIn⟩).val, hk⟩ : Fin tr.length)] =
        (⟨Sum.inr (Sum.inr (p.1.outputState[m]'hm)), p.1.inputState[m]'hmIn⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  rcases jbt_perm_getElem?_of_lt' tr state S p hp ⟨m, hmIn⟩ hm with h | h
  · obtain ⟨hk', hEq⟩ := List.getElem?_eq_some_iff.mp h
    exact Or.inl hEq
  · obtain ⟨hk', hEq⟩ := List.getElem?_eq_some_iff.mp h
    exact Or.inr hEq

/-- **Bridge**: a nonterminal `J_BT` permutation slot is first-of-mirror-class
(`M2Engine.FirstOfClassAt`) — the in-tree first-occurrence-of-either convention IS the CO25
Def. 5.4 mirror-class convention. -/
theorem jbt_perm_slot_firstOfClassAt'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S)
    (m : ℕ) (hm : m < p.1.outputState.length) (hmIn : m < p.1.inputState.length)
    (hk : (p.2.2 ⟨m, hmIn⟩).val < tr.length) :
    FirstOfClassAt tr ⟨(p.2.2 ⟨m, hmIn⟩).val, hk⟩ := by
  intro j' hj'
  have hno := Sponge316.jbt_perm_no_prior_of_lt tr state S p hp ⟨m, hmIn⟩ hm j' hj'
  rcases jbt_perm_slot_cases' tr state S p hp m hm hmIn hk with hA | hB
  · rw [hA, mirrorOf_fwd]
    exact ⟨hno.1, hno.2⟩
  · rw [hB, mirrorOf_inv]
    exact ⟨hno.2, hno.1⟩

/-- The `J_BT` hash slot carries the hash anchor (Fin-getElem normal form). -/
theorem jbt_hash_getElem''
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) :
    tr[p.2.1] =
      (⟨Sum.inl p.1.stmt,
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  have hget := Sponge316.jbt_hash_getElem? tr state S p hp
  rw [List.getElem?_eq_getElem p.2.1.isLt] at hget
  exact Option.some.inj hget

/-- **Bridge**: the `J_BT` hash slot is first-of-mirror-class (hash entries are
self-mirrors). -/
theorem jbt_hash_firstOfClassAt''
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) :
    FirstOfClassAt tr p.2.1 := by
  have hEq := jbt_hash_getElem'' tr state S p hp
  intro j' hj'
  have hno := Sponge316.jbt_hash_no_prior tr state S p hp j' hj'
  rw [hEq, mirrorOf_hash]
  exact ⟨hno, hno⟩

/-! ## The Lemma 5.12 core (reused by both 5.16 halves for the mirror-form cases) -/

/-- **5.12 core**: a chain step whose `J_BT` slot carries the *inverse-form* entry fires
`EPaper`. Downward descent on the chain index: step `0` collides answer-answer with the hash
anchor (its answer capacity is `cap(s_in,0)` = the anchor's answer); step `m+1` either
recurses into step `m` (also inverse) or collides answer-answer with step `m`'s forward
entry through chain continuity `cap(s_out,m) = cap(s_in,m+1)` (CO25 Def. 5.3 (d)). -/
theorem ePaper_of_jbt_inv_slot'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (p : Sigma fun seq : Backtrack.BacktrackSequence tr state =>
      Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ Backtrack.J_BT S) (m : ℕ) :
    ∀ (hm : m < p.1.outputState.length) (hmIn : m < p.1.inputState.length)
      (hk : (p.2.2 ⟨m, hmIn⟩).val < tr.length),
      tr[(⟨(p.2.2 ⟨m, hmIn⟩).val, hk⟩ : Fin tr.length)] =
        (⟨Sum.inr (Sum.inr (p.1.outputState[m]'hm)), p.1.inputState[m]'hmIn⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) →
      EPaper tr := by
  induction m with
  | zero =>
      intro hm hmIn hk hinv
      have hHashEq := jbt_hash_getElem'' tr state S p hp
      have hfocH := jbt_hash_firstOfClassAt'' tr state S p hp
      have hfocC := jbt_perm_slot_firstOfClassAt' tr state S p hp 0 hm hmIn hk
      -- the hash slot and the inverse slot are distinct (hash vs perm entry forms)
      have hneH : p.2.1 ≠ (⟨(p.2.2 ⟨0, hmIn⟩).val, hk⟩ : Fin tr.length) := by
        intro hEq
        have hgetEq : tr[p.2.1]
            = tr[(⟨(p.2.2 ⟨0, hmIn⟩).val, hk⟩ : Fin tr.length)] :=
          congrArg (fun k : Fin tr.length => tr[k]) hEq
        rw [hHashEq, hinv] at hgetEq
        simp at hgetEq
      rcases lt_or_gt_of_ne hneH with hlt | hgt'
      · -- hash anchor strictly earlier: C1 at (hash, inverse step 0)
        refine ePaper_of_answerCap_pair tr hlt hfocH hfocC ?_ ?_
        · rw [hHashEq, hinv]
          simp
        · rw [hHashEq, hinv]
          simp only [answerCap_hash, answerCap_inv]
      · -- inverse step 0 strictly earlier: C1 at (inverse step 0, hash)
        refine ePaper_of_answerCap_pair tr hgt' hfocC hfocH ?_ ?_
        · rw [hHashEq, hinv]
          simp
        · rw [hHashEq, hinv]
          simp only [answerCap_hash, answerCap_inv]
  | succ m ih =>
      intro hm hmIn hk hinv
      have hmP : m < p.1.outputState.length := Nat.lt_of_succ_lt hm
      have hmInP : m < p.1.inputState.length := Nat.lt_of_succ_lt hmIn
      have hkP : (p.2.2 ⟨m, hmInP⟩).val < tr.length :=
        jbt_perm_slot_lt' tr state S p hp m hmP hmInP
      rcases jbt_perm_slot_cases' tr state S p hp m hmP hmInP hkP with hfwdP | hinvP
      · -- previous step forward: continuity gives an answer-answer collision (C1)
        have hfocP := jbt_perm_slot_firstOfClassAt' tr state S p hp m hmP hmInP hkP
        have hfocC := jbt_perm_slot_firstOfClassAt' tr state S p hp (m + 1) hm hmIn hk
        have hcont : (p.1.outputState[m]'hmP).capacitySegment
            = (p.1.inputState[m + 1]'hmIn).capacitySegment :=
          p.1.capacitySegment_output_eq_input ⟨m, hmP⟩
        have hneP : (⟨(p.2.2 ⟨m, hmInP⟩).val, hkP⟩ : Fin tr.length)
            ≠ (⟨(p.2.2 ⟨m + 1, hmIn⟩).val, hk⟩ : Fin tr.length) := by
          intro hEq
          have hgetEq : tr[(⟨(p.2.2 ⟨m, hmInP⟩).val, hkP⟩ : Fin tr.length)]
              = tr[(⟨(p.2.2 ⟨m + 1, hmIn⟩).val, hk⟩ : Fin tr.length)] :=
            congrArg (fun k : Fin tr.length => tr[k]) hEq
          rw [hfwdP, hinv] at hgetEq
          simp at hgetEq
        rcases lt_or_gt_of_ne hneP with hlt | hgt'
        · -- forward step m strictly earlier: C1 at (forward m, inverse m+1)
          refine ePaper_of_answerCap_pair tr hlt hfocP hfocC ?_ ?_
          · rw [hfwdP, hinv]
            simp
          · rw [hfwdP, hinv]
            simp only [answerCap_fwd, answerCap_inv]
            exact hcont
        · -- inverse step m+1 strictly earlier: C1 at (inverse m+1, forward m)
          refine ePaper_of_answerCap_pair tr hgt' hfocC hfocP ?_ ?_
          · rw [hfwdP, hinv]
            simp
          · rw [hfwdP, hinv]
            simp only [answerCap_fwd, answerCap_inv]
            exact hcont.symm
      · -- previous step also inverse: recurse
        exact ih hmP hmInP hkP hinvP

/-! ## CO25 Lemma 5.16, hash half (Eq. 41) -/

/-- **Lemma 5.16, hash half (paper event)**: off `EPaper`, the anchoring hash query does not
appear after the first chain permutation query. -/
theorem lemma516HashPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr) :
    ¬ KeyLemmaFoundations.E_time_h_honest tr state S := by
  intro h
  apply hnE
  unfold KeyLemmaFoundations.E_time_h_honest at h
  obtain ⟨p, hp, hgt⟩ := h
  have h0 : 0 < p.1.outputState.length :=
    Sponge316.jbt_time_h_outputState_nonempty tr state S p hp hgt
  have h0In : 0 < p.1.inputState.length := by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    exact Nat.succ_pos _
  have hk : (p.2.2 ⟨0, h0In⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S p hp 0 h0 h0In
  have hHashEq := jbt_hash_getElem'' tr state S p hp
  have hfocH := jbt_hash_firstOfClassAt'' tr state S p hp
  have hfocC := jbt_perm_slot_firstOfClassAt' tr state S p hp 0 h0 h0In hk
  have hlt : (⟨(p.2.2 ⟨0, h0In⟩).val, hk⟩ : Fin tr.length) < p.2.1 := hgt
  rcases jbt_perm_slot_cases' tr state S p hp 0 h0 h0In hk with hfwd | hinv
  · -- forward chain step strictly before the hash anchor: C2 strict
    -- (query cap of step 0 = cap(s_in,0) = answer cap of the anchor)
    refine ePaper_of_queryCap_hit_lt tr
      (c := (p.1.inputState[0]'h0In).capacitySegment) hlt hfocC hfocH ?_ ?_
    · rw [hfwd, queryCap?_fwd]
    · rw [hHashEq]
      simp only [answerCap_hash]
  · -- inverse chain step: delegate to the 5.12 core
    exact ePaper_of_jbt_inv_slot' tr state S p hp 0 h0 h0In hk hinv

/-! ## CO25 Lemma 5.16, permutation half (Eq. 42) -/

/-- **Lemma 5.16, permutation half (paper event)**: off `EPaper`, no chain permutation query
appears in the trace strictly before its predecessor chain query. -/
theorem lemma516TimePPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr) :
    ¬ KeyLemmaFoundations.E_time_p_honest tr state S := by
  intro h
  apply hnE
  unfold KeyLemmaFoundations.E_time_p_honest at h
  obtain ⟨p, hp, ix, hgt⟩ := h
  have hnext : ix.val + 1 < p.1.outputState.length :=
    Sponge316.jbt_time_p_next_outputState_bound tr state S p hp ix hgt
  have hmA : ix.val < p.1.outputState.length := ix.isLt
  have hmInA : ix.val < p.1.inputState.length := by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    omega
  have hmInB : ix.val + 1 < p.1.inputState.length := by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    omega
  have hkA : (p.2.2 ⟨ix.val, hmInA⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S p hp ix.val hmA hmInA
  have hkB : (p.2.2 ⟨ix.val + 1, hmInB⟩).val < tr.length :=
    jbt_perm_slot_lt' tr state S p hp (ix.val + 1) hnext hmInB
  have hfocA := jbt_perm_slot_firstOfClassAt' tr state S p hp ix.val hmA hmInA hkA
  have hfocB := jbt_perm_slot_firstOfClassAt' tr state S p hp (ix.val + 1) hnext hmInB hkB
  -- the later chain step's slot is strictly earlier in the trace
  have hlt : (⟨(p.2.2 ⟨ix.val + 1, hmInB⟩).val, hkB⟩ : Fin tr.length)
      < (⟨(p.2.2 ⟨ix.val, hmInA⟩).val, hkA⟩ : Fin tr.length) := hgt
  -- chain continuity (CO25 Def. 5.3 (d)): cap(s_out,ι) = cap(s_in,ι+1)
  have hcont : (p.1.outputState[ix.val]'hmA).capacitySegment
      = (p.1.inputState[ix.val + 1]'hmInB).capacitySegment :=
    p.1.capacitySegment_output_eq_input ix
  rcases jbt_perm_slot_cases' tr state S p hp ix.val hmA hmInA hkA with hfwdA | hinvA
  · rcases jbt_perm_slot_cases' tr state S p hp (ix.val + 1) hnext hmInB hkB
      with hfwdB | hinvB
    · -- both forward: C2 strict — query cap of the (earlier) step ι+1 slot hits the
      -- answer cap of the (later) step ι slot through continuity
      refine ePaper_of_queryCap_hit_lt tr
        (c := (p.1.outputState[ix.val]'hmA).capacitySegment) hlt hfocB hfocA ?_ ?_
      · rw [hfwdB, queryCap?_fwd, hcont]
      · rw [hfwdA, answerCap_fwd]
    · -- step ι+1 inverse: C1 — its answer cap is cap(s_in,ι+1) = cap(s_out,ι) = answer cap
      -- of the (later) forward step ι slot
      refine ePaper_of_answerCap_pair tr hlt hfocB hfocA ?_ ?_
      · rw [hfwdA, hinvB]
        simp
      · rw [hfwdA, hinvB]
        simp only [answerCap_fwd, answerCap_inv]
        exact hcont.symm
  · -- step ι inverse: delegate to the 5.12 core
    exact ePaper_of_jbt_inv_slot' tr state S p hp ix.val hmA hmInA hkA hinvA

/-! ## CO25 Lemma 5.16 (paper event), combined -/

/-- **CO25 Lemma 5.16 over the paper bad event**: off `EPaper`, all BackTrack chain queries
appear in trace order (`¬ EPaper tr → ¬ E_time_honest tr state S`, with the in-tree honest
timing event of CO25 Def. 5.15). -/
theorem lemma516Paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hnE : ¬ EPaper tr) :
    ¬ KeyLemmaFoundations.E_time_honest tr state S := by
  intro h
  unfold KeyLemmaFoundations.E_time_honest at h
  rcases h with hh | hpp
  · exact lemma516HashPaper tr state S hnE hh
  · exact lemma516TimePPaper tr state S hnE hpp

/-! ## Axiom audit -/

#print axioms jbt_perm_getElem?_of_lt'
#print axioms jbt_perm_slot_lt'
#print axioms jbt_perm_slot_cases'
#print axioms jbt_perm_slot_firstOfClassAt'
#print axioms jbt_hash_getElem''
#print axioms jbt_hash_firstOfClassAt''
#print axioms ePaper_of_jbt_inv_slot'
#print axioms lemma516HashPaper
#print axioms lemma516TimePPaper
#print axioms lemma516Paper

end DuplexSpongeFS.Paper
