/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-
#314 M2 LEMMA 5.12 (paper-faithful) — `lemma512Paper`:
`¬ EPaper tr → ¬ E_inv_honest tr state S` (CO25 Lemma 5.12 over the in-tree honest event
`KeyLemmaFoundations.E_inv_honest` and the in-tree `Backtrack.S_BT`/`J_BT`, but with the
paper-faithful bad event `EPaper` of `EPaper.lean` instead of the deviant in-tree `E`).

Proof = the CO25 §5.6 minimal-inverse-step argument, implemented as a downward induction on
the chain-step index:

* **Index bridge** (`firstOfClassAt_of_perm_index'`): a nonterminal `BacktrackSequence.Index`
  permutation slot is a first-of-mirror-class slot of the raw trace. The in-tree
  `firstOccurrenceOfEither` runs over `{(p, sIn, sOut), (p⁻¹, sOut, sIn)}`, and
  `entryB = mirrorOf entryA` — i.e. the in-tree index convention IS the CO25 Def 5.4
  mirror-class first occurrence (no fidelity divergence). Built from the *public*
  `index_perm_getElem?_of_lt` + `index_perm_no_prior_of_lt` of `Backtrack.lean`; no private
  defs are unfolded and no deviant-`E`-conditioned lemma is used.
* **Step 0**: if the chain's step-0 first occurrence carries the inverse form, its answer
  capacity is `cap(s_in,0)`, which equals the hash anchor's answer capacity (CO25 Def 5.3(b));
  the anchor sits at a first-of-class slot by `mem_to_firstOfClass` (hash entries are
  self-mirror), and two distinct first-of-class slots with equal answer capacities fire
  `EPaper` through C1 (`ePaper_of_answerCap_pair`), in either relative order.
* **Step ι+1**: if step ι's first occurrence carries the forward form, its answer capacity
  `cap(s_out,ι)` equals `cap(s_in,ι+1)` (CO25 Def 5.3(d) continuity), the answer capacity of
  the step-(ι+1) inverse-form slot; C1 fires `EPaper` (forward and inverse entries are always
  distinct). If step ι's first occurrence also carries the inverse form, recurse — this is the
  "take the minimal inverse-realized step" argument run as plain induction.

All declarations are sorry-free; `#print axioms` at the end.
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsCoincidence

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog

namespace DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## Local bricks (primed names) -/

/-- C1, unordered form: two first-of-mirror-class slots with distinct entries and equal
answer-side capacities fire `EPaper`, regardless of relative order. -/
theorem ePaper_of_answerCap_pair'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {i j : Fin tr.length}
    (hi : FirstOfClassAt tr i) (hj : FirstOfClassAt tr j)
    (hne : tr[i] ≠ tr[j])
    (hcap : answerCap tr[i] = answerCap tr[j]) :
    EPaper tr := by
  rcases lt_trichotomy i j with h | h | h
  · exact ePaper_of_answerCap_pair tr h hi hj hne hcap
  · exact absurd (by rw [h]) hne
  · exact ePaper_of_answerCap_pair tr h hj hi (Ne.symm hne) hcap.symm

/-- **Index bridge**: a nonterminal `BacktrackSequence.Index` permutation slot is a
first-of-mirror-class slot of the raw trace (CO25 Def 5.4 first-occurrence convention,
verified against the in-tree `firstOccurrenceOfEither`: `entryB = mirrorOf entryA`). -/
theorem firstOfClassAt_of_perm_index'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)
    (seq : Backtrack.BacktrackSequence tr state)
    (pairIdx : Fin seq.inputState.length) (hpair : pairIdx.val < seq.outputState.length)
    (hlt : ((Backtrack.BacktrackSequence.Index tr state seq).2 pairIdx).val < tr.length) :
    FirstOfClassAt tr
      ⟨((Backtrack.BacktrackSequence.Index tr state seq).2 pairIdx).val, hlt⟩ := by
  intro j' hj'
  have hj'' : j'.val < ((Backtrack.BacktrackSequence.Index tr state seq).2 pairIdx).val :=
    Fin.lt_def.mp hj'
  have hno := Backtrack.BacktrackSequence.index_perm_no_prior_of_lt tr state seq
    pairIdx hpair j' hj''
  have hnoA : tr[j'] ≠ (⟨.inr (.inl seq.inputState[pairIdx]),
      seq.outputState[pairIdx.val]'hpair⟩ :
      duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hno.1
  have hnoB : tr[j'] ≠ (⟨.inr (.inr (seq.outputState[pairIdx.val]'hpair)),
      seq.inputState[pairIdx]⟩ :
      duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
    simpa only [List.get_eq_getElem, Fin.getElem_fin] using hno.2
  rcases Backtrack.BacktrackSequence.index_perm_getElem?_of_lt tr state seq pairIdx hpair
    with h | h
  · obtain ⟨hlt', heq⟩ := List.getElem?_eq_some_iff.mp h
    have hk : tr[(⟨((Backtrack.BacktrackSequence.Index tr state seq).2 pairIdx).val, hlt⟩ :
        Fin tr.length)]
        = ⟨.inr (.inl seq.inputState[pairIdx]), seq.outputState[pairIdx.val]'hpair⟩ := heq
    rw [hk]
    exact ⟨hnoA, by rw [mirrorOf_fwd]; exact hnoB⟩
  · obtain ⟨hlt', heq⟩ := List.getElem?_eq_some_iff.mp h
    have hk : tr[(⟨((Backtrack.BacktrackSequence.Index tr state seq).2 pairIdx).val, hlt⟩ :
        Fin tr.length)]
        = ⟨.inr (.inr (seq.outputState[pairIdx.val]'hpair)), seq.inputState[pairIdx]⟩ := heq
    rw [hk]
    exact ⟨hnoB, by rw [mirrorOf_inv]; exact hnoA⟩

/-- C1 finisher, hash anchor vs inverse-form chain slot (the CO25 5.12 case `ι = 0`):
equal answer capacities at two first-of-class slots of distinct kinds fire `EPaper`. -/
theorem ePaper_of_hash_inv_pair'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {kh k : Fin tr.length}
    (hfocH : FirstOfClassAt tr kh) (hfoc : FirstOfClassAt tr k)
    {stmt : StmtIn} {cap : Vector U SpongeSize.C} {sOut sIn : CanonicalSpongeState U}
    (hh : tr[kh] = ⟨.inl stmt, cap⟩)
    (hk : tr[k] = ⟨.inr (.inr sOut), sIn⟩)
    (hcap : cap = sIn.capacitySegment) :
    EPaper tr :=
  ePaper_of_answerCap_pair' tr hfocH hfoc
    (by rw [hh, hk]; simp)
    (by rw [hh, hk, answerCap_hash, answerCap_inv]; exact hcap)

/-- C1 finisher, forward-form previous step vs inverse-form current step (the CO25 5.12 case
`ι > 0`): chain continuity makes the two answer capacities coincide and fires `EPaper`. -/
theorem ePaper_of_fwd_inv_pair'
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k' k : Fin tr.length}
    (hfoc' : FirstOfClassAt tr k') (hfoc : FirstOfClassAt tr k)
    {aIn aOut sOut sIn : CanonicalSpongeState U}
    (h1 : tr[k'] = ⟨.inr (.inl aIn), aOut⟩)
    (h2 : tr[k] = ⟨.inr (.inr sOut), sIn⟩)
    (hcap : aOut.capacitySegment = sIn.capacitySegment) :
    EPaper tr :=
  ePaper_of_answerCap_pair' tr hfoc' hfoc
    (by rw [h1, h2]; simp)
    (by rw [h1, h2, answerCap_fwd, answerCap_inv]; exact hcap)

/-! ## CO25 Lemma 5.12, paper-faithful -/

/-- **CO25 Lemma 5.12 (paper event)**: off the paper-faithful bad event `EPaper`, no
BackTrack chain step is anchored by an inverse-permutation first occurrence:
`¬ EPaper tr → ¬ E_inv_honest tr state S`. -/
theorem lemma512Paper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state)
    (hE : ¬ EPaper tr) :
    ¬ KeyLemmaFoundations.E_inv_honest tr state S := by
  classical
  intro hinv
  unfold KeyLemmaFoundations.E_inv_honest at hinv
  obtain ⟨p, hp, ιx, s_out, s_in, hslot⟩ := hinv
  unfold Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  refine hE ?_
  -- Downward induction on the chain-step index = the CO25 minimal-inverse-step argument.
  suffices h : ∀ m, ∀ hm : m < seq.outputState.length,
      ∀ so si : CanonicalSpongeState U,
      tr[((Backtrack.BacktrackSequence.Index tr state seq).2
        ⟨m, by have := seq.inputState_length_eq_outputState_length_succ; omega⟩).val]?
        = some ⟨.inr (.inr so), si⟩ → EPaper tr by
    exact h ιx.val ιx.isLt s_out s_in hslot
  intro m
  induction m with
  | zero =>
      intro hm so si hslot₀
      have hin : (0 : ℕ) < seq.inputState.length := by
        have := seq.inputState_length_eq_outputState_length_succ; omega
      rcases Backtrack.BacktrackSequence.index_perm_getElem?_of_lt tr state seq
        ⟨0, hin⟩ hm with hA | hB
      · -- forward form at the step-0 slot contradicts the inverse-form hypothesis
        have hcontra := hslot₀.symm.trans hA
        simp at hcontra
      · obtain ⟨hlt₀, hgetB⟩ := List.getElem?_eq_some_iff.mp hB
        have hgetB' : tr[(⟨((Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨0, hin⟩).val, hlt₀⟩ : Fin tr.length)]
            = ⟨.inr (.inr (seq.outputState[0]'hm)),
              seq.inputState[(⟨0, hin⟩ : Fin seq.inputState.length)]⟩ := hgetB
        obtain ⟨kh, hfocH, hkh⟩ := mem_to_firstOfClass seq.hash_in_trace
        have hkh' : tr[kh] = ⟨.inl seq.stmt,
            Vector.drop (seq.inputState[0]'hin) SpongeSize.R⟩ := by
          rcases hkh with h | h
          · exact h
          · exact h
        exact ePaper_of_hash_inv_pair' tr
          hfocH (firstOfClassAt_of_perm_index' tr state seq ⟨0, hin⟩ hm hlt₀)
          hkh' hgetB' rfl
  | succ m' ih =>
      intro hm so si hslot₀
      have hm' : m' < seq.outputState.length := Nat.lt_of_succ_lt hm
      have hin' : m' < seq.inputState.length := by
        have := seq.inputState_length_eq_outputState_length_succ; omega
      have hin : m' + 1 < seq.inputState.length := by
        have := seq.inputState_length_eq_outputState_length_succ; omega
      rcases Backtrack.BacktrackSequence.index_perm_getElem?_of_lt tr state seq
        ⟨m' + 1, hin⟩ hm with hA | hB
      · -- forward form at the step-(m'+1) slot contradicts the inverse-form hypothesis
        have hcontra := hslot₀.symm.trans hA
        simp at hcontra
      · obtain ⟨hlt₀, hgetB⟩ := List.getElem?_eq_some_iff.mp hB
        have hgetB' : tr[(⟨((Backtrack.BacktrackSequence.Index tr state seq).2
            ⟨m' + 1, hin⟩).val, hlt₀⟩ : Fin tr.length)]
            = ⟨.inr (.inr (seq.outputState[m' + 1]'hm)),
              seq.inputState[(⟨m' + 1, hin⟩ : Fin seq.inputState.length)]⟩ := hgetB
        rcases Backtrack.BacktrackSequence.index_perm_getElem?_of_lt tr state seq
          ⟨m', hin'⟩ hm' with hA' | hB'
        · -- step m' realized forward: continuity + C1 fires `EPaper`
          obtain ⟨hlt', hgetA⟩ := List.getElem?_eq_some_iff.mp hA'
          have hgetA' : tr[(⟨((Backtrack.BacktrackSequence.Index tr state seq).2
              ⟨m', hin'⟩).val, hlt'⟩ : Fin tr.length)]
              = ⟨.inr (.inl seq.inputState[(⟨m', hin'⟩ : Fin seq.inputState.length)]),
                seq.outputState[m']'hm'⟩ := hgetA
          exact ePaper_of_fwd_inv_pair' tr
            (firstOfClassAt_of_perm_index' tr state seq ⟨m', hin'⟩ hm' hlt')
            (firstOfClassAt_of_perm_index' tr state seq ⟨m' + 1, hin⟩ hm hlt₀)
            hgetA' hgetB'
            (by simpa using seq.capacitySegment_output_eq_input ⟨m', hm'⟩)
        · -- step m' realized inverse: recurse (the minimality descent)
          exact ih hm' _ _ hB'

/-! ## Axiom audit -/

#print axioms ePaper_of_answerCap_pair'
#print axioms firstOfClassAt_of_perm_index'
#print axioms ePaper_of_hash_inv_pair'
#print axioms ePaper_of_fwd_inv_pair'
#print axioms lemma512Paper

end DuplexSpongeFS.Paper
