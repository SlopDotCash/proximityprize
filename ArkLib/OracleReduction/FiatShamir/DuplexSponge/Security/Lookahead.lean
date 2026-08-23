/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Lookahead Sequence Family and Extraction Procedure

This module formalizes the lookahead sequence family $S_{\mathrm{LA}}(\mathrm{tr}_{\nabla}.p, s, i)$
and the lookahead extraction procedure $\mathsf{LookAhead}(\mathrm{tr}_{\nabla}.p, s, i)$ as
defined in CO25, Section 5.3.

## Mathematical Formulation

In the soundness analysis of Fiat-Shamir applied to interactive oracle reductions (IORs) in the
duplex-sponge model, a key challenge is extracting a verifier challenge $\hat{\rho}_i$ for a
round $i$ from a partial query-answer trace. The lookahead sequence formalizes the forward
propagation of the
sponge state under permutation queries starting from a given state $s$.

1. **Lookahead Chains (Eq. 13)**: A lookahead sequence of length $m$ over a permutation table
   $\mathrm{tr}_{\nabla}.p$ is a sequence of query-answer pairs
   $((s_{\mathrm{in},\iota}, s_{\mathrm{out},\iota}))_{\iota=0}^{m-1}$ such that:
   - $s_{\mathrm{in},0} = s$ (the initial state),
   - Each pair is recorded in the permutation table $\mathrm{tr}_{\nabla}.p$,
   - The output state of a step matches the input state of the next step
     ($s_{\mathrm{out},\iota-1} = s_{\mathrm{in},\iota}$), and
   - The capacity segments are non-trivially modified
     ($\mathrm{cap}(s_{\mathrm{in},\iota}) \neq \mathrm{cap}(s_{\mathrm{out},\iota})$)
     to prevent trivial cyclic/identity loops.

2. **The Lookahead Family $S_{\mathrm{LA}}$**: This is the family of maximal lookahead chains of
   length at most $L_V(i)$ (the number of permutation calls allocated to round $i$). Maximality
   ensures that no chain in the family is a prefix/sub-chain of another.

3. **Extraction & Sampling (Step 2)**: The lookahead extraction procedure $\mathsf{LookAhead}$
   dispatches on the size of the family $S_{\mathrm{LA}}$:
   - If $|S_{\mathrm{LA}}| > 1$, a collision/fork in the forward evaluation is detected, returning
     $\mathsf{err}$.
   - If $S_{\mathrm{LA}} = \emptyset$, it returns $\mathsf{noResult}$.
   - If $S_{\mathrm{LA}}$ contains a unique maximal chain of length $m_1$, the missing
     $L_V(i) - m_1$ rate blocks are sampled uniformly at random. The concatenation of the known
     output rate blocks and these fresh samples yields the extracted challenge
     $\hat{\rho}_i \in \Sigma^{\ell_V(i)}$.

## Algorithmic Optimization

While the paper defines $S_{\mathrm{LA}}$ as a static mathematical family, this module implements a
linear forward scan (`linearScanForwards`) starting at the state $s$ to efficiently extract the
unique maximal sequence. If at any point multiple forward candidates are found, the scan immediately
aborts with `.forkErr`, which is a paper-faithful optimization since a scan-time fork coincides with
the bad event $E_{\mathrm{fork},p}$.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.Lookahead

open DSTraceStorage

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]
  [HasChallengeSize pSpec]

noncomputable section

/-! ## §5.3 paper structures — `LookaheadSequence`, `S_LA(tr_∇.p, s, i)` -/

/-- A look-ahead sequence (CO25, Equation 13) over a black-box permutation table `tr_∇.p`
and an initial state $s$. A lookahead sequence is a non-empty chain of sponge state transition pairs
$((s_{\mathrm{in},\iota}, s_{\mathrm{out},\iota}))_{\iota=0}^{m-1}$ such that:
- The first input state is the given starting state: $s_{\mathrm{in},0} = s$,
- Every transition pair is present in the permutation table:
  $(s_{\mathrm{in},\iota}, s_{\mathrm{out},\iota}) \in \mathrm{tr}_{\nabla}.p$,
- Consecutive transitions are chained: $s_{\mathrm{out},\iota-1} = s_{\mathrm{in},\iota}$ for
  $\iota \geq 1$, and
- The capacity segment changes at each transition:
  $\mathrm{cap}(s_{\mathrm{in},\iota}) \neq \mathrm{cap}(s_{\mathrm{out},\iota})$,
  guaranteeing that the chain does not contain trivial loops. -/
structure LookaheadSequence
    {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P)
    (state : CanonicalSpongeState U) where
  /-- `S_LA^(k)` chain (LookAhead §5.3 Step 1, Eq. 13): `(s_{in,ι}, s_{out,ι})` pairs. -/
  pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)
  /-- `ℓ ≥ 1` — non-empty chain (`.found` branch of LookAhead §5.3 Step 2.c). -/
  nonempty : pairs ≠ []
  /-- `s_{in,0} = state` — LookAhead §5.3 Step 1(b). -/
  first_inputState_eq_state : pairs.head?.map Prod.fst = some state
  /-- `(s_{in,ι}, s_{out,ι}) ∈ tr_∇.p` — LookAhead §5.3 Step 1(c) query-answer membership. -/
  inputOutput_mem_entries : ∀ pair ∈ pairs,
    pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp
  /-- `s_{out,ι-1} = s_{in,ι}` — LookAhead §5.3 Step 1(c) consecutive linkage. -/
  outputState_eq_next_inputState : List.IsChain (fun a b => a.2 = b.1) pairs
  /-- `cap(s_{in,ι}) ≠ cap(s_{out,ι})` — LookAhead §5.3 Step 1(d) no-loop guard. -/
  capacitySegment_inputState_ne_outputState : ∀ pair ∈ pairs,
    pair.1.capacitySegment ≠ pair.2.capacitySegment

variable {T_P : Type}
  [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

def LookaheadSequence.inputState
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.fst

def LookaheadSequence.outputState
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    List (CanonicalSpongeState U) :=
  seq.pairs.map Prod.snd

lemma LookaheadSequence.inputState_length_eq_outputState_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.outputState.length := by
  simp [LookaheadSequence.inputState, LookaheadSequence.outputState]

/-- A family of look-ahead sequences (CO25, Equation 13), parameterized by a black-box
permutation table `tr_∇.p`, an initial state $s$, and a challenge round index $i$.
The family $S_{\mathrm{LA}}(\mathrm{tr}_{\nabla}.p, s, i)$ is a finite set of lookahead sequences
satisfying:
- **Maximality**: No sequence in the family is a strict subset of another, ensuring each represents
  a maximal path.
- **Length Bound**: The length of any sequence in the family is at most $L_V(i)$, the verifier's
  permutation query bound for challenge round $i$. -/
structure LookaheadSequenceFamily
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- `S_LA` — the finite family of look-ahead sequences (LookAhead §5.3 Step 1). -/
  seqFamily : Finset (LookaheadSequence trΔp state)
  /-- LookAhead §5.3 Step 1(e) maximality: no sequence strictly contains another. -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    s ≠ s' →
      ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)
  /-- `m_k ≤ L_V(i)` — LookAhead §5.3 Step 1(a) length bound. -/
  length_le_numPermQueriesChallenge : ∀ s ∈ seqFamily, s.inputState.length ≤ pSpec.Lᵥᵢ i

/-- The maximal lookahead sequence family $S_{\mathrm{LA}}(\mathrm{tr}_{\nabla}.p, s, i)$
produced by the LookAhead extraction procedure (CO25, Section 5.3, Step 1). This is the dual
structure to the backtracking sequence family $S_{\mathrm{BT}}(\mathrm{tr}, s)$ defined in
`Backtrack.lean`. -/
abbrev S_LA
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :=
  LookaheadSequenceFamily (pSpec := pSpec) trΔp state i

/-! ## §5.3 Step 1 — Parse `tr_∇.p` into the maximal family `S_LA(tr_∇.p, s, i)` (Eq. 13) -/

/-- Computes all candidate successor states from the query-answer table $\mathrm{tr}_{\nabla}.p$
for a given state `current`. Unlike `TraceTableOps.inlu`, which assumes a single deterministic map,
this returns all forward matches in the table. This is necessary to detect branching (forks),
which must lead to an error state during extraction. -/
private def successorCandidates
    (trΔp : T_P) (current : CanonicalSpongeState U) :
    List (CanonicalSpongeState U) := by
  classical
  exact (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap fun pair =>
    if pair.1 = current then
      some pair.2
    else none

private def singletonLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hEntry : (state, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment) :
    LookaheadSequence trΔp state :=
  { pairs := [(state, next)]
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_mem_entries := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hEntry
    outputState_eq_next_inputState := by simp
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      have hPair' : pair = (state, next) := List.mem_singleton.mp hPair
      subst hPair'
      exact hNoLoop }

set_option linter.flexible false in
private def prependLookaheadSequence
    (trΔp : T_P)
    (state next : CanonicalSpongeState U)
    (hEntry : (state, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp)
    (hNoLoop : state.capacitySegment ≠ next.capacitySegment)
    (tail : LookaheadSequence trΔp next) :
    LookaheadSequence trΔp state :=
  { pairs := (state, next) :: tail.pairs
    nonempty := by simp
    first_inputState_eq_state := by simp
    inputOutput_mem_entries := by
      intro pair hPair
      rcases List.mem_cons.mp hPair with hEq | hRest
      · subst hEq
        exact hEntry
      · exact tail.inputOutput_mem_entries pair hRest
    outputState_eq_next_inputState := by
      cases hPairs : tail.pairs with
      | nil =>
          exact (tail.nonempty hPairs).elim
      | cons head rest =>
          have hHead : head.1 = next := by
            have hHd := tail.first_inputState_eq_state
            rw [hPairs] at hHd
            simp at hHd
            exact hHd
          have hTailChain : List.IsChain (fun a b => a.2 = b.1) (head :: rest) := by
            have hCh := tail.outputState_eq_next_inputState
            rw [hPairs] at hCh
            exact hCh
          exact List.IsChain.cons_cons hHead.symm hTailChain
    capacitySegment_inputState_ne_outputState := by
      intro pair hPair
      rcases List.mem_cons.mp hPair with hEq | hRest
      · subst hEq
        exact hNoLoop
      · exact tail.capacitySegment_inputState_ne_outputState pair hRest }

private lemma inputState_length_eq_pairs_length
    {trΔp : T_P}
    {state : CanonicalSpongeState U} (seq : LookaheadSequence trΔp state) :
    seq.inputState.length = seq.pairs.length := by
  simp [LookaheadSequence.inputState]

/-! ## §5.3 Step 2 — Final output dispatch on `|S_LA|`: `err` / `none` / sampled vector -/

private lemma challengeSize_le_Lvi_mul_R (i : pSpec.ChallengeIdx) :
    challengeSize i ≤ pSpec.Lᵥᵢ i * SpongeSize.R := by
  have hceil : ((challengeSize i : ℚ) / SpongeSize.R) ≤ (pSpec.Lᵥᵢ i : ℚ) := by
    simpa [ProtocolSpec.numPermQueriesChallenge] using
      (Nat.le_ceil ((challengeSize i : ℚ) / SpongeSize.R))
  have hRnonneg : (0 : ℚ) ≤ SpongeSize.R := by
    exact_mod_cast (Nat.zero_le SpongeSize.R)
  have hmul :
      ((challengeSize i : ℚ) / SpongeSize.R) * SpongeSize.R
        ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R :=
    mul_le_mul_of_nonneg_right hceil hRnonneg
  have hRne : (SpongeSize.R : ℚ) ≠ 0 := by
    exact_mod_cast (show SpongeSize.R ≠ 0 from NeZero.ne SpongeSize.R)
  have hleft :
      ((challengeSize i : ℚ) / SpongeSize.R) * SpongeSize.R = (challengeSize i : ℚ) := by
    field_simp [hRne]
  have hq : (challengeSize i : ℚ) ≤ (pSpec.Lᵥᵢ i : ℚ) * SpongeSize.R := by
    simpa [hleft] using hmul
  exact_mod_cast hq

private def sampleArrayExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {xs : Array U // xs.size = m}
  | 0 => pure ⟨#[], rfl⟩
  | m + 1 => do
      let u ← (query (spec := (Unit →ₒ U)) () : OracleComp (Unit →ₒ U) U)
      let ⟨xs, hxs⟩ ← sampleArrayExact m
      pure ⟨xs.push u, by simp [hxs]⟩

private def sampleRateVector : OracleComp (Unit →ₒ U) (Vector U SpongeSize.R) := do
  let ⟨xs, hxs⟩ ← sampleArrayExact (U := U) SpongeSize.R
  pure ⟨xs, hxs⟩

private def sampleRateVectorsExact :
    (m : Nat) → OracleComp (Unit →ₒ U) {blocks : List (Vector U SpongeSize.R) // blocks.length = m}
  | 0 => pure ⟨[], rfl⟩
  | m + 1 => do
      let head ← sampleRateVector (U := U)
      let ⟨tail, htail⟩ ← sampleRateVectorsExact m
      pure ⟨head :: tail, by simp [htail]⟩

omit [SpongeUnit U] [DecidableEq U] in
private lemma length_flatten_vector_toList (blocks : List (Vector U SpongeSize.R)) :
    (List.flatten (blocks.map Vector.toList)).length = blocks.length * SpongeSize.R := by
  induction blocks with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.right_distrib, Nat.add_comm]

private def takeVector (n : Nat) (xs : List U) (h : n ≤ xs.length) : Vector U n :=
  Vector.ofFn (fun j => xs[j.1]'(Nat.lt_of_lt_of_le j.2 h))

/-- Implements Step 2(c) of the LookAhead extraction procedure (CO25, Section 5.3).
Given a unique maximal lookahead sequence of length $m_1 \leq L_V(i)$, this function samples the
remaining $L_V(i) - m_1$ rate blocks uniformly at random from $\Sigma^r$. It then concatenates the
known output-rate blocks from the sequence with the freshly sampled blocks, extracting the prefix
of length
$\ell_V(i)$ as the challenge $\hat{\rho}_i \in \Sigma^{\ell_V(i)}$. -/
private def sampleChallengeFromSequence
    {trΔp : T_P}
    {state : CanonicalSpongeState U}
    (seq : LookaheadSequence trΔp state)
    (i : pSpec.ChallengeIdx)
    (hInputLenLe : seq.inputState.length ≤ pSpec.Lᵥᵢ i) :
    OracleComp (Unit →ₒ U) (Vector U (challengeSize i)) := do
  -- `L_V(i)` — total number of permutation calls in the verifier squeeze window for round `i`.
  let maxSteps := pSpec.Lᵥᵢ i
  -- `knownBlocks = [s_{R,out,0}^{(1)}, …, s_{R,out,m₁-1}^{(1)}]` — the `m₁` output-rate
  -- segments already determined by the unique maximal sequence `S_LA^{(1)}`.
  let knownBlocks : List (Vector U SpongeSize.R) :=
    seq.outputState.map CanonicalSpongeState.rateSegment
  -- `|knownBlocks| = |inputState| = m₁` (output and input lists have equal length by
  -- `LookaheadSequence.inputState_length_eq_outputState_length`).
  have hKnownLenEqInputLen : knownBlocks.length = seq.inputState.length := by
    have hKnownLenEqOutputLen : knownBlocks.length = seq.outputState.length := by
      simp [knownBlocks]
    have hOutputLenEqInputLen : seq.outputState.length = seq.inputState.length := by
      exact (LookaheadSequence.inputState_length_eq_outputState_length
        (T_P := T_P) (U := U) seq).symm
    exact hKnownLenEqOutputLen.trans hOutputLenEqInputLen
  -- `m₁ ≤ L_V(i)` (from the family length bound).
  have hKnownLenLeMax : knownBlocks.length ≤ maxSteps := hKnownLenEqInputLen ▸ hInputLenLe
  -- `L_V(i) - m₁` — number of additional random rate blocks to sample.
  let missingBlocks := maxSteps - knownBlocks.length
  -- Sample `s_{R,out,m₁}^{(1)}, …, s_{R,out,L_V(i)-1}^{(1)} ←$ U(Σ^r)`.
  let ⟨randomBlocks, hRandomLen⟩ ← sampleRateVectorsExact (U := U) missingBlocks
  -- `allBlocks = [s_{R,out,0}^{(1)}, …, s_{R,out,L_V(i)-1}^{(1)}]` — full output-rate list.
  let allBlocks := knownBlocks ++ randomBlocks
  -- `units = s_{R,out,0}^{(1)} ‖ s_{R,out,1}^{(1)} ‖ ⋯ ‖ s_{R,out,L_V(i)-1}^{(1)}` —
  -- concatenation of all `L_V(i)` rate blocks into a flat unit list.
  let units : List U := List.flatten (allBlocks.map Vector.toList)
  -- `|allBlocks| ≥ L_V(i)` (known `m₁` + sampled `L_V(i) - m₁`).
  have hMax_le_allBlocks : maxSteps ≤ allBlocks.length := by
    simp [allBlocks, missingBlocks, hRandomLen, Nat.add_sub_of_le hKnownLenLeMax]
  -- `|units| ≥ L_V(i) · r` (each rate block contributes exactly `r` units).
  have hMaxR_le_units : maxSteps * SpongeSize.R ≤ units.length := by
    have hmul : maxSteps * SpongeSize.R ≤ allBlocks.length * SpongeSize.R :=
      Nat.mul_le_mul_right SpongeSize.R hMax_le_allBlocks
    have hUnitsLen : units.length = allBlocks.length * SpongeSize.R := by
      exact length_flatten_vector_toList (U := U) allBlocks |>.symm ▸ rfl
    rw [hUnitsLen]; exact hmul
  -- `ℓ_V(i) ≤ L_V(i) · r ≤ |units|` — the challenge size fits within the concatenated units.
  have hChal_le_units : challengeSize i ≤ units.length := by
    have hChal_le_maxR : challengeSize i ≤ maxSteps * SpongeSize.R := by
      exact challengeSize_le_Lvi_mul_R (pSpec := pSpec) i
    exact le_trans hChal_le_maxR hMaxR_le_units
  -- Return `ρ̂_i := units[0 : ℓ_V(i)] ∈ Σ^{ℓ_V(i)}`.
  pure (takeVector (U := U) (challengeSize i) units hChal_le_units)

/-! ### Bridge lemma: `successorCandidates` → entry membership -/

private lemma successor_singleton_mem_entries
    (trΔp : T_P) (current next : CanonicalSpongeState U)
    (h : successorCandidates (T_P := T_P) (U := U) trΔp current = [next]) :
    (current, next) ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔp := by
  unfold successorCandidates at h
  classical
  have hMem : next ∈ (TraceTableOps.entries (V := CanonicalSpongeState U) trΔp).filterMap
      (fun pair => if pair.1 = current then some pair.2 else none) := by rw [h]; exact .head ..
  obtain ⟨pair, hPairMem, hPairEq⟩ := List.mem_filterMap.mp hMem
  split at hPairEq
  · next hCurr =>
      have hSnd : pair.2 = next := by injection hPairEq
      have hPairEq' : pair = (current, next) := Prod.ext hCurr hSnd
      rw [hPairEq'] at hPairMem; exact hPairMem
  · contradiction

/-! ### Optimized Linear Forwards Scan (CO25, Section 5.3, Algorithm 2)

Algorithm 2 in the paper is specified via an exhaustive enumeration of the maximal sequence family
followed by a filtering step. However, as noted in the text (line 1107), "the search stops if it
encounters two conflicting chains". We optimize this by performing a single linear forward scan.
Finding multiple successors at any step indicates a fork (corresponding to the event
$E_{\mathrm{fork},p}$), allowing us to abort immediately and return an error. -/


/-- The result of a linear forward scan. Represents either a detected branch/fork (`forkErr`)
or a successful scan returning an optional lookahead sequence (`done`). -/
private inductive LinearForwardScanResult {T_P : Type} [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (state : CanonicalSpongeState U) where
  | forkErr
  | done (seq? : Option (LookaheadSequence trΔp state))

/-- Performs a linear forward scan along the permutation table $\mathrm{tr}_{\nabla}.p$ starting
from `current`. At each step:
- If no successor candidates exist, the scan terminates.
- If a unique successor `next` is found, the scan continues recursively (after checking for capacity
  segment loops).
- If multiple successors exist, a fork is detected, and the scan aborts with `.forkErr`. -/
private def linearScanForwards
    (trΔp : T_P) (fuel : Nat) (current : CanonicalSpongeState U) :
    LinearForwardScanResult (U := U) trΔp current :=
  match fuel with
  | 0 => .done none
  | fuel' + 1 =>
    -- Look up successor in `tr_∇.p` (CO25 §5.3)
    let succs := successorCandidates (T_P := T_P) (U := U) trΔp current
    match hSuccs : succs with
    | [] => .done none -- No successor, sequence ends
    | [next] =>
        -- Found unique successor (CO25 §5.3 maximal sequence)
        if hNoLoop : current.capacitySegment = next.capacitySegment then
          .forkErr -- Self-loop → `E_inv`
        else
          have hNoLoop' : current.capacitySegment ≠ next.capacitySegment := hNoLoop
          have hEntry : (current, next) ∈ TraceTableOps.entries trΔp :=
            successor_singleton_mem_entries trΔp current next hSuccs
          match linearScanForwards trΔp fuel' next with
          | .forkErr => .forkErr
          | .done none =>
              .done (some (singletonLookaheadSequence (T_P := T_P) (U := U)
                trΔp current next hEntry hNoLoop'))
          | .done (some tailSeq) =>
              .done (some (prependLookaheadSequence (T_P := T_P) (U := U) trΔp
                current next hEntry hNoLoop' tailSeq))
    | _ :: _ :: _ => .forkErr -- `tr_∇.p` collision → `E_prp`

private lemma linearScanForwards_seq_length_le
    (trΔp : T_P) (fuel : Nat) (current : CanonicalSpongeState U)
    {seq : LookaheadSequence trΔp current}
    (hScan : linearScanForwards (T_P := T_P) (U := U) trΔp fuel current = .done (some seq)) :
    seq.pairs.length ≤ fuel := by
  induction fuel generalizing current seq with
  | zero => simp [linearScanForwards] at hScan
  | succ fuel' ih =>
      simp only [linearScanForwards] at hScan
      -- body matches on successorCandidates result
      split at hScan
      · -- succs = []: .done none, contradiction
        simp at hScan
      · next next hSuccEq => -- succs = [next]
          split at hScan
          · -- loop detected: .forkErr, contradiction
            simp at hScan
          · -- no loop: match on recursive result
            split at hScan
            · -- recursive .forkErr, contradiction
              simp at hScan
            · -- recursive .done none: singleton sequence, pairs.length = 1 ≤ fuel' + 1
              injection hScan with hEq
              injection hEq with hEq2
              subst hEq2
              exact Nat.succ_le_succ (Nat.zero_le fuel')
            · next tailSeq hTailScan =>
              -- recursive .done (some tailSeq): prepend, length = tailLen + 1 ≤ fuel' + 1
              injection hScan with hEq
              injection hEq with hEq2
              subst hEq2
              have hTailLen := ih next hTailScan
              exact Nat.succ_le_succ hTailLen
      · -- succs = _ :: _ :: _: .forkErr, contradiction
        simp at hScan

/-- The executable entry point for lookahead extraction. It runs the optimized linear scan
to extract a unique sequence, and if successful, samples any missing rate blocks to output the
challenge vector. -/
private def linearLookAhead
    (trΔp : T_P) (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))) := do
  let maxSteps := pSpec.Lᵥᵢ i
  match hScan : linearScanForwards (T_P := T_P) (U := U) trΔp maxSteps state with
  | .forkErr => pure ExperimentOutput.err
  | .done none => pure ExperimentOutput.noResult
  | .done (some seq) =>
      have hLen : seq.inputState.length ≤ pSpec.Lᵥᵢ i := by
        -- scan-invariant: `pairs.length ≤ maxSteps = pSpec.Lᵥᵢ i`.
        rw [inputState_length_eq_pairs_length]
        exact linearScanForwards_seq_length_le trΔp maxSteps state hScan
      let rhoHat ← sampleChallengeFromSequence (T_P := T_P) (U := U) (pSpec := pSpec)
        (seq := seq) (i := i) (hInputLenLe := hLen)
      pure (ExperimentOutput.some rhoHat)

/-- The formal lookahead extraction procedure $\mathsf{LookAhead}(\mathrm{tr}_{\nabla}.p, s, i)$
(CO25, Section 5.3, Algorithm 2).

### Parameters
- `trΔp`: The simulator's permutation table $\mathrm{tr}_{\nabla}.p$.
- `state`: The initial permutation state $s \in \Sigma^{r+c}$.
- `i`: The challenge round index.

### Returns
- `ExperimentOutput.err`: If multiple conflicting maximal lookahead sequences exist.
- `ExperimentOutput.noResult`: If no lookahead sequences are found starting at $s$.
- `ExperimentOutput.some \hat{\rho}_i`: If a unique maximal sequence is found; the missing rate
  blocks are completed via uniform sampling and the resulting challenge vector is returned. -/
def lookAhead
    (trΔp : T_P)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))) :=
  linearLookAhead (pSpec := pSpec) trΔp state i

end

end DuplexSpongeFS.Lookahead
