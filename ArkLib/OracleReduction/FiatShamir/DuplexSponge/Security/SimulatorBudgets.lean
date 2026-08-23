/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# Simulator query budgets — CO25 Lemma 5.1 conjuncts (a) and (b) for the `d2sAlgo` witness

This module discharges the four named budget residuals of `KeyLemmaFoundations`:

- `D2sQueryStepGSpecBudgetResidual` (F4): the §5.4 `D2SQuery` dispatcher `d2sQueryStep` makes
  at most one `gSpec` query per source query, and only on a forward-permutation query
  (CO25 §5.4 Item 4(e)i). Proven by a branch-tree analysis of the five handlers
  (`d2sHandleHashQuery` / `d2sHandleInversePermQuery` / `d2sHandleBacktrackNoResult` /
  `d2sHandleBacktrackSome` / `d2sHandleForwardPermQuery`): every other oracle access is a
  `𝒰(Σ)` / `unifSpec` draw on the right summand.
- `D2fOuterImplSharedBudgetResidual` (F4b): the composed outer implementation `d2fOuterImpl`
  forwards shared-`oSpec` queries 1:1 (`QueryImpl.id` summand) and its duplex-sponge summand
  never touches `oSpec` (the simulator's target spec embeds via the right injection, so every
  query it makes lands in the `.inr` summand).
- `SimulatedProverChallengeBudgetResidual` (M1c): the witness `simulatedProverSalted` makes at
  most `θ★ = tₚ` basic-FS challenge queries (Lemma 5.1 conjunct (b)) — one per forward-perm
  query of the malicious prover, through F4 + the Eq. 16 memoized-bridge budget (F5) + the
  `IsQueryBoundP` transfer bricks (F3a/F3b).
- `SimulatedProverSharedBudgetResidual` (M1d): the witness respects the shared-`oSpec` budgets
  `tₒ` (Lemma 5.1 conjunct (a)) — `oSpec` queries are forwarded 1:1 at every layer.

All four are proven with no `sorry`; together with `KeyLemmaHybrids.keyLemmaEager_of_steps`
they reduce `KeyLemmaEagerResidual` to the four per-step TV-bound residuals (Claims 5.21–5.24).

The §5.4 handler defs are `private` in `ProverTransform`; we access them with Batteries'
`open private` (no semantic change upstream).
-/

open OracleComp OracleSpec ProtocolSpec OracleReduction

-- The budget lemmas below inherit the broad §5.4 section variables of `ProverTransform`;
-- several helpers use only a subset (and some `Decidable`/`Fintype` instances appear in
-- proofs but not statements). Silencing the per-lemma `omit` cascade keeps the branch-tree
-- proofs readable (repo precedent: Data/CodingTheory/Connections/*).
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace DuplexSpongeFS.SimulatorBudgets

open Backtrack Lookahead DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations

open private d2sHandleHashQuery d2sHandleInversePermQuery d2sHandleBacktrackNoResult
  d2sHandleBacktrackSome d2sHandleForwardPermQuery d2sSampleUnit d2sSampleArrayExact
  d2sSampleVector d2sRateBlocksFromUnitsM d2sSynthesizeStateFromRateBlocks
  from ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

/-! ## Generic `StateT σ (AbortComp spec')` run-composition helpers

The §5.4 handlers live in `StateT σ (OptionT (OracleComp spec'))`; after `.run st |>.run`
they normalize to `OracleComp spec' (Option (α × σ))`. These lemmas compose
`IsQueryBoundP` bounds through the recurring `bind` / `lift` / `failure` shapes. -/

section RunHelpers

variable {ι' : Type} {spec' : OracleSpec ι'} {q : ι' → Prop} [DecidablePred q]

/-- Budget composition through a `StateT σ (AbortComp spec')`-level bind: the scrutinee budget
plus a uniform budget for the continuation at every reachable state. -/
private lemma isQueryBoundP_run2_bind {σ α β : Type}
    {x : StateT σ (AbortComp spec') α} {k : α → StateT σ (AbortComp spec') β}
    {n m : ℕ} {st : σ}
    (hx : IsQueryBoundP ((x.run st).run) q n)
    (hk : ∀ a s', IsQueryBoundP (((k a).run s').run) q m) :
    IsQueryBoundP (((x >>= k).run st).run) q (n + m) := by
  rw [StateT.run_bind, OptionT.run_bind]
  exact isQueryBoundP_elimM hx (isQueryBoundP_pure _ _ _) (fun pr => hk pr.1 pr.2)

/-- Budget composition through the `StateT.lift ∘ OptionT.lift` shape of the §5.4 sampling
steps: the lifted computation's budget plus the continuation's budget at the *same* state. -/
private lemma isQueryBoundP_run2_lift_bind {σ α β : Type}
    {oa : OracleComp spec' α} {k : α → StateT σ (AbortComp spec') β}
    {n m : ℕ} {st : σ}
    (h : IsQueryBoundP oa q n)
    (hk : ∀ a, IsQueryBoundP (((k a).run st).run) q m) :
    IsQueryBoundP (((StateT.lift (OptionT.lift oa) >>= k).run st).run) q (n + m) := by
  have heq : (((StateT.lift (OptionT.lift oa) >>= k).run st).run)
      = oa >>= fun a => (((k a).run st).run) := by
    simp only [StateT.run_bind, StateT.run_lift, OptionT.run_bind, OptionT.run_lift,
      bind_assoc, pure_bind, Option.elimM, Option.elim_some]
  rw [heq]
  exact isQueryBoundP_bind h (fun a _ => hk a)

/-- The aborting branch (`StateT.lift failure`, CO25 §5.4 Item 4(b) `err`) makes no queries. -/
private lemma isQueryBoundP_run2_lift_failure {σ α : Type} (st : σ) (b : ℕ) :
    IsQueryBoundP
      (((StateT.lift (failure : AbortComp spec' α) : StateT σ (AbortComp spec') α).run
        st).run) q b := by
  have heq : (((StateT.lift (failure : AbortComp spec' α) :
        StateT σ (AbortComp spec') α).run st).run)
      = (pure none : OracleComp spec' (Option (α × σ))) := by
    simp only [StateT.run_lift, OptionT.run_bind, OptionT.run_failure, Option.elimM,
      pure_bind, Option.elim_none]
  rw [heq]
  exact isQueryBoundP_pure _ _ _

end RunHelpers

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : ℕ}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-! ## F4 prerequisites — the §5.4 sampling helpers make no `gSpec` queries

Every `𝒰(Σ)`-style draw of CO25 §5.4 (Items 2(b), 3(b), 4(c)iii, 4(e)iiiA–C) goes through
`d2sSampleUnit` = one query on the right summand of `d2sQueryOracles`; none touches the
`gSpec` (left) summand. -/

section SamplerBudgets

private lemma d2sSampleUnit_left_budget :
    IsQueryBoundP (d2sSampleUnit (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (fun j => j.isLeft = true) 0 := by
  unfold d2sSampleUnit
  simp only [HasQuery.instOfMonadLift_query]
  exact (isQueryBoundP_query_iff _ _ _).mpr (by simp)

private lemma d2sSampleArrayExact_left_budget (m : ℕ) :
    IsQueryBoundP
      (d2sSampleArrayExact (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      (fun j => j.isLeft = true) 0 := by
  induction m with
  | zero =>
      simp only [d2sSampleArrayExact]
      exact isQueryBoundP_pure _ _ _
  | succ m ih =>
      simp only [d2sSampleArrayExact]
      refine isQueryBoundP_bind (n := 0) (m := 0) d2sSampleUnit_left_budget (fun u _ => ?_)
      refine isQueryBoundP_bind (n := 0) (m := 0) ih (fun xs _ => ?_)
      obtain ⟨xs, hxs⟩ := xs
      exact isQueryBoundP_pure _ _ _

private lemma d2sSampleVector_left_budget (m : ℕ) :
    IsQueryBoundP
      (d2sSampleVector (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sSampleVector
  refine isQueryBoundP_bind (n := 0) (m := 0) (d2sSampleArrayExact_left_budget m)
    (fun xs _ => ?_)
  obtain ⟨xs, hxs⟩ := xs
  exact isQueryBoundP_pure _ _ _

private lemma d2sSampleCapacity_left_budget :
    IsQueryBoundP
      (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (fun j => j.isLeft = true) 0 :=
  d2sSampleVector_left_budget _

private lemma d2sSampleState_left_budget :
    IsQueryBoundP
      (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (fun j => j.isLeft = true) 0 :=
  d2sSampleVector_left_budget _

private lemma d2sSampleCapacityList_left_budget (m : ℕ) :
    IsQueryBoundP
      (d2sSampleCapacityList (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) m)
      (fun j => j.isLeft = true) 0 := by
  induction m with
  | zero =>
      simp only [d2sSampleCapacityList]
      exact isQueryBoundP_pure _ _ _
  | succ m ih =>
      simp only [d2sSampleCapacityList]
      refine isQueryBoundP_bind (n := 0) (m := 0) d2sSampleCapacity_left_budget
        (fun head _ => ?_)
      exact isQueryBoundP_bind (n := 0) (m := 0) ih
        (fun tail _ => isQueryBoundP_pure _ _ _)

private lemma d2sRateBlocksFromUnitsM_left_budget (m : ℕ) (units : List U) :
    IsQueryBoundP
      (d2sRateBlocksFromUnitsM (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        m units)
      (fun j => j.isLeft = true) 0 := by
  induction m generalizing units with
  | zero =>
      simp only [d2sRateBlocksFromUnitsM]
      exact isQueryBoundP_pure _ _ _
  | succ m ih =>
      simp only [d2sRateBlocksFromUnitsM]
      split
      · refine isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_pure _ _ _)
          (fun y _ => ?_)
        refine isQueryBoundP_bind (n := 0) (m := 0) (ih _) (fun tail _ => ?_)
        exact isQueryBoundP_pure _ _ _
      · refine isQueryBoundP_bind (n := 0) (m := 0) (d2sSampleVector_left_budget _)
          (fun pad _ => ?_)
        refine isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_pure _ _ _)
          (fun y _ => ?_)
        refine isQueryBoundP_bind (n := 0) (m := 0) (ih _) (fun tail _ => ?_)
        exact isQueryBoundP_pure _ _ _

private lemma d2sRateBlocksFromChallenge_left_budget {i : pSpec.ChallengeIdx}
    (challenge : Vector U (challengeSize (pSpec := pSpec) i)) :
    IsQueryBoundP
      (d2sRateBlocksFromChallenge (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        challenge)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sRateBlocksFromChallenge
  refine isQueryBoundP_bind (n := 0) (m := 0) (d2sRateBlocksFromUnitsM_left_budget _ _)
    (fun blocks _ => ?_)
  obtain ⟨blocks, hBlocks⟩ := blocks
  exact isQueryBoundP_pure _ _ _

private lemma d2sQueryG_left_budget (i : pSpec.ChallengeIdx) (stmt : StmtIn)
    (salt : Vector U δ) (encodedMessages : pSpec.EncodedMessagesBefore U i.1.castSucc) :
    IsQueryBoundP
      (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        i stmt salt encodedMessages)
      (fun j => j.isLeft = true) 1 := by
  unfold d2sQueryG
  simp only [HasQuery.instOfMonadLift_query]
  exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)

end SamplerBudgets

/-! ## F4 — the five-handler branch tree (CO25 §5.4 Items 2–4) -/

section HandlerBudgets

/-- CO25 §5.4 Item 2 — the hash handler makes no `gSpec` query (cache hit returns the stored
capacity segment; cache miss draws `s_{C,out} ← 𝒰(Σ^c)` on the right summand). -/
private lemma d2sHandleHashQuery_left_budget (stmt : StmtIn)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleHashQuery (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st).run)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sHandleHashQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h : TraceTableOps.inlu st.trΔ.h stmt with
  | some capSeg =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | none =>
      exact isQueryBoundP_run2_lift_bind (n := 0) (m := 0) d2sSampleCapacity_left_budget
        (fun sampled => by
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            OptionT.run_pure]
          exact isQueryBoundP_pure _ _ _)

/-- CO25 §5.4 Item 3 — the inverse-permutation handler makes no `gSpec` query. -/
private lemma d2sHandleInversePermQuery_left_budget (stateOut : CanonicalSpongeState U)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleInversePermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st).run)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sHandleInversePermQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases h : TraceTableOps.outlu st.trΔ.p stateOut with
  | some recovered =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | none =>
      exact isQueryBoundP_run2_lift_bind (n := 0) (m := 0) d2sSampleState_left_budget
        (fun sampled => by
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            OptionT.run_pure]
          exact isQueryBoundP_pure _ _ _)

/-- CO25 §5.4 Item 4(c) — the no-result branch makes no `gSpec` query (cache pop / forward
lookup / fresh `𝒰(Σ^{r+c})` sample). -/
private lemma d2sHandleBacktrackNoResult_left_budget (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleBacktrackNoResult (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st).run)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sHandleBacktrackNoResult
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · -- Item 4(c)i — cache pop
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
      OptionT.run_pure]
    exact isQueryBoundP_pure _ _ _
  · -- pop missed: forward lookup or fresh sample
    split
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_run2_lift_bind (n := 0) (m := 0) d2sSampleState_left_budget
        (fun sampled => by
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            OptionT.run_pure]
          exact isQueryBoundP_pure _ _ _)

/-- CO25 §5.4 Item 4(e)iii — the state-synthesis helper makes no `gSpec` query (capacity
sampling on the right summand; abort on empty rate blocks). -/
private lemma d2sSynthesizeStateFromRateBlocks_left_budget
    (rateBlocks : List (Vector U SpongeSize.R))
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sSynthesizeStateFromRateBlocks (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) rateBlocks).run st).run)
      (fun j => j.isLeft = true) 0 := by
  unfold d2sSynthesizeStateFromRateBlocks
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact isQueryBoundP_run2_lift_failure _ _
  · refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
      (d2sSampleCapacityList_left_budget _) (fun caps => ?_)
    split
    · exact isQueryBoundP_run2_lift_failure _ _
    · simp only [StateT.run_pure, OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _

/-- CO25 §5.4 Items 4(d)/(e) — the backtrack-success branch makes **at most one** `gSpec`
query: the unconditional Item 4(e)i `gᵢ` query when the encoded messages are in the codec
image, and none otherwise. -/
private lemma d2sHandleBacktrackSome_left_budget (stateIn : CanonicalSpongeState U)
    (backtrackOut : BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleBacktrackSome (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut).run st).run)
      (fun j => j.isLeft = true) 1 := by
  unfold d2sHandleBacktrackSome
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · -- in codec image: one `gᵢ` query (Item 4(e)i), then only right-summand sampling
    refine isQueryBoundP_run2_lift_bind (n := 1) (m := 0)
      (d2sQueryG_left_budget _ _ _ _) (fun sampledRhoHat => ?_)
    split
    · -- Item 4(e)ii — forward cache hit
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · -- Item 4(e)iii — reshape + synthesize
      refine isQueryBoundP_run2_lift_bind (n := 0) (m := 0)
        (d2sRateBlocksFromChallenge_left_budget _) (fun rateBlocks => ?_)
      refine isQueryBoundP_run2_bind (n := 0) (m := 0)
        (d2sSynthesizeStateFromRateBlocks_left_budget _ _) (fun sc s' => ?_)
      obtain ⟨s_out, cache'⟩ := sc
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
  · -- Item 4(d) — not in codec image: lookup or fresh sample, no `gᵢ` query
    split
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
    · refine IsQueryBoundP.mono ?_ (Nat.zero_le 1)
      exact isQueryBoundP_run2_lift_bind (n := 0) (m := 0) d2sSampleState_left_budget
        (fun sampled => by
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            OptionT.run_pure]
          exact isQueryBoundP_pure _ _ _)

/-- CO25 §5.4 Item 4 — the forward-permutation handler makes at most one `gSpec` query
(`err` aborts, `noResult` only samples, `some` is Items 4(d)/(e)). -/
private lemma d2sHandleForwardPermQuery_left_budget (stateIn : CanonicalSpongeState U)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    IsQueryBoundP
      (((d2sHandleForwardPermQuery (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st).run)
      (fun j => j.isLeft = true) 1 := by
  unfold d2sHandleForwardPermQuery
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · -- `err` — Item 4(b) abort
    exact isQueryBoundP_run2_lift_failure _ _
  · -- `noResult` — Item 4(c)
    exact (d2sHandleBacktrackNoResult_left_budget _ _).mono (Nat.zero_le 1)
  · -- `some` — Items 4(d)/(e)
    exact d2sHandleBacktrackSome_left_budget _ _ _

/-- **F4** — `D2sQueryStepGSpecBudgetResidual` is true: the §5.4 dispatcher `d2sQueryStep`
makes at most one `gSpec` query, and only on a forward-permutation query
(CO25 §5.4 Item 4(e)i). -/
theorem d2sQueryStepGSpecBudget :
    D2sQueryStepGSpecBudgetResidual (StmtIn := StmtIn) (U := U) (pSpec := pSpec)
      (δ := δ) T_H T_P := by
  intro qq st
  match qq with
  | Sum.inl stmt =>
      exact d2sHandleHashQuery_left_budget stmt st
  | Sum.inr (Sum.inl stateIn) =>
      exact d2sHandleForwardPermQuery_left_budget stateIn st
  | Sum.inr (Sum.inr stateOut) =>
      exact d2sHandleInversePermQuery_left_budget stateOut st

end HandlerBudgets

/-! ## The `d2fOuterImpl` run-shapes (the `addLift` embedding, made explicit)

`d2fOuterImpl` lifts its two summands into
`StateT (D2SQueryState …) (StateT M (OptionT (OracleComp (oSpec + D2SChallengePlusUnitOracle
challengeSpec))))` through the `ToMathlib` `StateT` congruence lifts and the VCVio `OptionT`
SubSpec lift. Running all three layers exposes:

- on a shared query `.inl qo`: a single forwarded `oSpec` query (the `QueryImpl.id` summand);
- on a duplex-sponge query `.inr dsq`: the `d2sQueryImpl` run *re-indexed along the right
  injection* (a `simulateQ` with the inclusion implementation), so every query it makes lands
  in the `.inr` summand of the outer spec.

Both identities hold definitionally. -/

section OuterImplShapes

variable {κ : Type} {challengeSpec : OracleSpec κ} {M : Type}

/-- The auxiliary `(Unit →ₒ U) + unifSpec` realization baked into `d2fOuterImpl`. -/
private def d2fAuxImpl :
    QueryImpl ((Unit →ₒ U) + unifSpec)
      (StateT M (OptionT (OracleComp
        (D2SChallengePlusUnitOracle (U := U) challengeSpec)))) :=
  fun aux =>
    MonadLift.monadLift
      (MonadLift.monadLift
        (query
          (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
          (Sum.inr aux) :
            OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) _) :
        OptionT (OracleComp
          (D2SChallengePlusUnitOracle (U := U) challengeSpec)) _)

/-- Run-shape of `d2fOuterImpl` on a shared `oSpec` query: one forwarded query. -/
private lemma d2fOuterImpl_run_inl
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (qo : ι)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) :
    (((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl
        (Sum.inl qo)).run st).run m).run
      = (liftM ((oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec).query
            (Sum.inl qo)) :
          OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _)
          >>= fun u => pure (some ((u, st), m)) := rfl

/-- Run-shape of `d2fOuterImpl` on a duplex-sponge query: the `d2sQueryImpl` run re-indexed
along the right injection. -/
private lemma d2fOuterImpl_run_inr
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) :
    (((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl
        (Sum.inr dsq)).run st).run m).run
      = simulateQ (fun t =>
            (liftM ((D2SChallengePlusUnitOracle (U := U) challengeSpec).query t) :
              OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _))
          ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              (m := StateT M (OptionT (OracleComp
                (D2SChallengePlusUnitOracle (U := U) challengeSpec))))
              (gImpl := gImpl)
              (auxImpl := d2fAuxImpl)
              dsq).run st).run m).run) := rfl

/-- The right-injection inclusion implementation realizes each query as a single `.inr`
query of the sum spec. -/
private lemma inclusion_impl_eq (t : κ ⊕ (Unit ⊕ ℕ)) :
    (liftM ((D2SChallengePlusUnitOracle (U := U) challengeSpec).query t) :
        OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _)
      = liftM ((oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec).query
          (Sum.inr t)) := rfl

/-- Budget transfer along the right-injection `simulateQ`: a sub-spec budget over `p`
becomes an outer budget over any predicate `q` agreeing with `p` on `.inr`. -/
private lemma isQueryBoundP_simulateQ_inclusion {α : Type}
    {oa : OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) α}
    {p : (κ ⊕ (Unit ⊕ ℕ)) → Prop} [DecidablePred p]
    {q : (ι ⊕ (κ ⊕ (Unit ⊕ ℕ))) → Prop} [DecidablePred q] {b : ℕ}
    (h : IsQueryBoundP oa p b)
    (hq : ∀ t, q (Sum.inr t) ↔ p t) :
    IsQueryBoundP
      (simulateQ (fun t =>
          (liftM ((D2SChallengePlusUnitOracle (U := U) challengeSpec).query t) :
            OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) _))
        oa) q b := by
  refine IsQueryBoundP.simulateQ_of_step h (fun t hp => ?_) (fun t hnp => ?_)
  · rw [inclusion_impl_eq (oSpec := oSpec)]
    exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)
  · rw [inclusion_impl_eq (oSpec := oSpec)]
    exact (isQueryBoundP_query_iff _ _ _).mpr (fun hqt => absurd ((hq t).mp hqt) hnp)

end OuterImplShapes

/-! ## F4b — shared-budget forwarding of `d2fOuterImpl` -/

section SharedForwarding

/-- **F4b** — `D2fOuterImplSharedBudgetResidual` is true: per source query, `d2fOuterImpl`
makes at most one `oSpec` query at index `i`, and only when the source query *is* the
`oSpec` query at `i`. The duplex-sponge summand embeds along the right injection and never
touches `oSpec`. -/
theorem d2fOuterImplSharedBudget [DecidableEq ι] :
    D2fOuterImplSharedBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (pSpec := pSpec) (δ := δ) T_H T_P := by
  intro κ challengeSpec M gImpl t st m i
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨?_, fun u => isQueryBoundP_pure _ _ _⟩
      by_cases hqo : (Sum.inl qo : ι ⊕ (StmtIn ⊕ CanonicalSpongeState U
          ⊕ CanonicalSpongeState U)).getLeft? = some i
      · refine Or.inr ?_
        simp only [Sum.getLeft?_inl] at hqo
        simp [hqo]
      · exact Or.inl (by simpa using hqo)
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr]
      have hbound : (if (Sum.inr dsq : ι ⊕ (StmtIn ⊕ CanonicalSpongeState U
          ⊕ CanonicalSpongeState U)).getLeft? = some i then 1 else 0) = 0 := by
        simp
      rw [hbound]
      refine isQueryBoundP_simulateQ_inclusion (p := fun _ => False)
        (isQueryBoundP_false _ 0) (fun t => ?_)
      simp

end SharedForwarding

/-! ## M1c — challenge budget of the witness (Lemma 5.1 conjunct (b), `θ★ = tₚ`) -/

section ChallengeBudget

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- Challenge classifier on the §5.4 D2SAlgo target spec index
`ι ⊕ (κf ⊕ (Unit ⊕ ℕ))`: `true` exactly on the basic-FS challenge summand. -/
private def isMidChallengeIdx {ι₁ κ : Type} : (ι₁ ⊕ (κ ⊕ (Unit ⊕ ℕ))) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- The §5.4 `d2sQueryImpl` with the Eq. 16 memoized codec bridge makes at most one basic-FS
challenge query per source query, and only on a forward-permutation query: F4 (≤1 `gSpec`
query, only on `p`) composed with F5 (≤1 challenge query per `gSpec` query). -/
private lemma d2sQueryImpl_bridge_run_left_budget
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    IsQueryBoundP
      ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (m := StateT (D2SAlgoMemo StmtIn U δ Salt pSpec) (OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U)
              (fsChallengeOracle (StmtIn × Salt) pSpec)))))
          (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ) (Salt := Salt))
          (auxImpl := d2fAuxImpl)
          dsq).run s₁).run s₂).run)
      (fun j => j.isLeft = true)
      (match dsq with | .inr (.inl _) => 1 | _ => 0) := by
  unfold d2sQueryImpl
  refine isQueryBoundP_run2_bind
    (n := match dsq with | .inr (.inl _) => 1 | _ => 0) (m := 0)
    ?_ (fun pairOpt m' => ?_)
  · -- the simulated dispatcher run: F3a with F4 + F5
    refine isQueryBoundP_simulateQ_stateT_optionT_of_step
      (p := fun j => j.isLeft = true)
      (d2sQueryStepGSpecBudget (T_H := T_H) (T_P := T_P) dsq s₁)
      (fun t s => ?_) s₂
    match t with
    | Sum.inl gq =>
        simp only [Sum.isLeft_inl, QueryImpl.add_apply_inl]
        exact d2sCodecBridgeImplMemo_challenge_budget (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ) (Salt := Salt) gq s
    | Sum.inr aux =>
        simp only [Sum.isLeft_inr, QueryImpl.add_apply_inr]
        have h0 : IsQueryBoundP
            ((query (spec := D2SChallengePlusUnitOracle (U := U)
                (fsChallengeOracle (StmtIn × Salt) pSpec)) (Sum.inr aux) :
                OracleComp (D2SChallengePlusUnitOracle (U := U)
                  (fsChallengeOracle (StmtIn × Salt) pSpec)) _)
              >>= fun u => pure (some (u, s)))
            (fun j => j.isLeft = true) 0 := by
          simp only [HasQuery.instOfMonadLift_query]
          exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
            ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩
        exact h0
  · -- the `match pairOpt` postlude makes no queries
    match pairOpt with
    | none => exact isQueryBoundP_run2_lift_failure _ _
    | some p =>
        simp only [StateT.run_pure, OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _

/-- Per-step challenge budget of `d2fOuterImpl` with the Eq. 16 memoized bridge: at most one
basic-FS challenge query per source query, and only on a forward-permutation query. -/
private lemma d2fOuterImpl_bridge_challenge_step
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
          (gImpl := d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
            (δ := δ) (Salt := Salt)) t).run s₁).run s₂).run)
      (fun j => isMidChallengeIdx j = true)
      (if DuplexSpongeFS.dsQueryFlavor t = DuplexSpongeFS.DSQueryFlavor.perm
        then 1 else 0) := by
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [isMidChallengeIdx]), fun u => isQueryBoundP_pure _ _ _⟩
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr]
      have hbound : (if DuplexSpongeFS.dsQueryFlavor
            (Sum.inr dsq : ι ⊕ (StmtIn ⊕ CanonicalSpongeState U
              ⊕ CanonicalSpongeState U)) = DuplexSpongeFS.DSQueryFlavor.perm
          then 1 else 0)
          = (match dsq with | .inr (.inl _) => 1 | _ => 0) := by
        match dsq with
        | Sum.inl _ => simp [DuplexSpongeFS.dsQueryFlavor]
        | Sum.inr (Sum.inl _) => simp [DuplexSpongeFS.dsQueryFlavor]
        | Sum.inr (Sum.inr _) => simp [DuplexSpongeFS.dsQueryFlavor]
      rw [hbound]
      exact isQueryBoundP_simulateQ_inclusion
        (d2sQueryImpl_bridge_run_left_budget (T_H := T_H) (T_P := T_P) dsq s₁ s₂)
        (fun t => by cases t <;> simp [isMidChallengeIdx])

/-- The (run of the) §5.4 simulated prover `D2SAlgo^f(𝒜)` makes at most `tₚ` basic-FS
challenge queries when `𝒜` makes at most `tₚ` forward-permutation queries (F3b at the
outer layer). -/
private lemma d2sAlgo_run_challenge_budget
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) (tₚ : ℕ)
    (h𝒜 : IsQueryBoundP 𝒜
      (fun j => DuplexSpongeFS.dsQueryFlavor j = DuplexSpongeFS.DSQueryFlavor.perm) tₚ) :
    IsQueryBoundP
      ((d2sAlgo (T_H := T_H) (T_P := T_P) (Salt := Salt) 𝒜).run)
      (fun j => isMidChallengeIdx j = true) tₚ := by
  unfold d2sAlgo
  rw [OptionT.run_bind]
  refine isQueryBoundP_elimM (n := tₚ) (m := 0) ?_ (isQueryBoundP_pure _ _ _)
    (fun a => ?_)
  · unfold D2FQueryProver
    rw [OptionT.run_map, isQueryBoundP_map_iff, OptionT.run_map, isQueryBoundP_map_iff]
    unfold d2fRaw
    exact isQueryBoundP_simulateQ_stateT2_optionT_of_step h𝒜
      (fun t s₁ s₂ => d2fOuterImpl_bridge_challenge_step (oSpec := oSpec) t s₁ s₂)
      default default
  · obtain ⟨stmt, τ, msgs⟩ := a
    rw [OptionT.run_pure]
    exact isQueryBoundP_pure _ _ _

/-- **M1c** — `SimulatedProverChallengeBudgetResidual` is true: the witness
`simulatedProverSalted` makes at most `θ★ = tₚ` basic-FS challenge queries
(CO25 Lemma 5.1 conjunct (b)). -/
theorem simulatedProverChallengeBudget
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)] :
    SimulatedProverChallengeBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P := by
  intro unitImpl 𝒜 tₕ tₚ tₚᵢ hUnit h𝒜
  have hAlgo := d2sAlgo_run_challenge_budget (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
    (Salt := Salt) 𝒜 tₚ h𝒜
  unfold simulatedProverSalted
  rw [isQueryBoundP_map_iff]
  have hstep := IsQueryBoundP.simulateQ_of_step
    (impl := simulatedProverImpl (oSpec := oSpec) (U := U) (pSpec := pSpec)
      (Salt := Salt) unitImpl)
    (q := fun j => isFSChallengeCoinIdx j = true) hAlgo
    (fun t ht => ?_) (fun t ht => ?_)
  · exact hstep
  · -- one challenge query per mid-challenge step
    match t with
    | Sum.inr (Sum.inl qf) =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)
    | Sum.inl qo => simp [isMidChallengeIdx] at ht
    | Sum.inr (Sum.inr (Sum.inl qu)) => simp [isMidChallengeIdx] at ht
    | Sum.inr (Sum.inr (Sum.inr mq)) => simp [isMidChallengeIdx] at ht
  · -- no challenge queries on the other steps
    match t with
    | Sum.inl qo =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isFSChallengeCoinIdx])
    | Sum.inr (Sum.inl qf) => simp [isMidChallengeIdx] at ht
    | Sum.inr (Sum.inr (Sum.inl qu)) =>
        simpa only [simulatedProverImpl] using hUnit qu
    | Sum.inr (Sum.inr (Sum.inr mq)) =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isFSChallengeCoinIdx])

end ChallengeBudget

/-! ## M1d — shared budget of the witness (Lemma 5.1 conjunct (a)) -/

section SharedBudget

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- The (run of the) §5.4 simulated prover forwards shared-`oSpec` queries 1:1: at most
`tₒ i` queries at each index `i` (F3b with the F4b step). -/
private lemma d2sAlgo_run_shared_budget [DecidableEq ι]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) (tₒ : ι → ℕ)
    (h𝒜 : ∀ i, IsQueryBoundP 𝒜 (fun j => j.getLeft? = some i) (tₒ i)) (i : ι) :
    IsQueryBoundP
      ((d2sAlgo (T_H := T_H) (T_P := T_P) (Salt := Salt) 𝒜).run)
      (fun j => j.getLeft? = some i) (tₒ i) := by
  unfold d2sAlgo
  rw [OptionT.run_bind]
  refine isQueryBoundP_elimM (n := tₒ i) (m := 0) ?_ (isQueryBoundP_pure _ _ _)
    (fun a => ?_)
  · unfold D2FQueryProver
    rw [OptionT.run_map, isQueryBoundP_map_iff, OptionT.run_map, isQueryBoundP_map_iff]
    unfold d2fRaw
    exact isQueryBoundP_simulateQ_stateT2_optionT_of_step (h𝒜 i)
      (fun t s₁ s₂ => d2fOuterImplSharedBudget (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
        _ _ _ t s₁ s₂ i)
      default default
  · obtain ⟨stmt, τ, msgs⟩ := a
    rw [OptionT.run_pure]
    exact isQueryBoundP_pure _ _ _

/-- **M1d** — `SimulatedProverSharedBudgetResidual` is true: the witness
`simulatedProverSalted` respects the shared-`oSpec` budgets `tₒ`
(CO25 Lemma 5.1 conjunct (a)). -/
theorem simulatedProverSharedBudget [DecidableEq ι]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)] :
    SimulatedProverSharedBudgetResidual (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) T_H T_P := by
  intro unitImpl 𝒜 tₒ hUnit h𝒜 i
  have hAlgo := d2sAlgo_run_shared_budget (oSpec := oSpec) (T_H := T_H) (T_P := T_P)
    (Salt := Salt) 𝒜 tₒ h𝒜 i
  unfold simulatedProverSalted
  rw [isQueryBoundP_map_iff]
  have hstep := IsQueryBoundP.simulateQ_of_step
    (impl := simulatedProverImpl (oSpec := oSpec) (U := U) (pSpec := pSpec)
      (Salt := Salt) unitImpl)
    (q := fun j => isSharedCoinIdx i j = true) hAlgo
    (fun t ht => ?_) (fun t ht => ?_)
  · exact hstep
  · -- the shared query at `i` is forwarded 1:1
    match t with
    | Sum.inl qo =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)
    | Sum.inr (Sum.inl qf) => simp at ht
    | Sum.inr (Sum.inr (Sum.inl qu)) => simp at ht
    | Sum.inr (Sum.inr (Sum.inr mq)) => simp at ht
  · -- no shared queries at `i` on the other steps
    match t with
    | Sum.inl qo =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        refine (isQueryBoundP_query_iff _ _ _).mpr (fun hq => ?_)
        simp only [Sum.getLeft?_inl] at ht
        simp only [isSharedCoinIdx, decide_eq_true_eq] at hq
        exact absurd (by simpa using hq) ht
    | Sum.inr (Sum.inl qf) =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isSharedCoinIdx])
    | Sum.inr (Sum.inr (Sum.inl qu)) =>
        simpa only [simulatedProverImpl] using hUnit qu i
    | Sum.inr (Sum.inr (Sum.inr mq)) =>
        simp only [simulatedProverImpl, HasQuery.instOfMonadLift_query]
        exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isSharedCoinIdx])

end SharedBudget

end DuplexSpongeFS.SimulatorBudgets

#print axioms DuplexSpongeFS.SimulatorBudgets.d2sQueryStepGSpecBudget
#print axioms DuplexSpongeFS.SimulatorBudgets.d2fOuterImplSharedBudget
#print axioms DuplexSpongeFS.SimulatorBudgets.simulatedProverChallengeBudget
#print axioms DuplexSpongeFS.SimulatorBudgets.simulatedProverSharedBudget
