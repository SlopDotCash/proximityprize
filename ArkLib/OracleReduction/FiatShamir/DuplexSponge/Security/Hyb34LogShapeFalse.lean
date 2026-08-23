/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay

/-!
# Ground-truth refutation bricks for the unsalted `Hyb₃ → Hyb₄` step: the F1 log-shape gap

This module machine-checks the **F1 verifier-log-shape falsifier** for the CO25 §5.8
`Hyb₃ → Hyb₄` leg (issue #314, ladder lane): the memoized/hit-only `gᵢ` bridges of the middle
hybrids are *query-silent* (the hit-only bridge is `pure` on a hit and `pure none` on a miss —
the proven bricks `d2sCodecBridgeImplMemoHitOnly_run_hit` / `_run_miss`), so **every**
`some`-output of `Hyb3Strict` carries a verifier log with **zero** `fsChallengeOracle`
entries. `Hyb₄`'s `V.fiatShamir`, by contrast, queries `fsChallengeOracle` once per challenge
round inside the logged run (`ArkLib/OracleReduction/FiatShamir/Basic.lean`, `processRoundFS` /
`deriveTranscriptFS`). The `some`-supports of the two games are therefore disjoint on the
verifier-log coordinate, and the TV distance is bounded *below* by the probability that `Hyb₄`
produces a `some`-output whose verifier log contains a challenge entry.

## Proven here (no `sorry`, axiom-clean)

- **R0** `projectRightQueryLog` (+ `append` homomorphism): right-summand log projection,
  mirror of `KeyLemmaFoundations.projectLeftQueryLog`.
- **R1-lite** `d2fRaw_hitOnly_challenge_budget`: the *whole* `Hyb3Strict` verifier pipeline
  (`d2fRaw` with the hit-only bridge) makes **zero** challenge-summand queries — an
  `IsQueryBoundP … 0` fact in the `SimulatorBudgets` idiom, for *any* source computation.
- **R1** `hyb3Strict_vLog_challenge_free`: every `some`-output of the `Hyb3Strict` game body
  has a challenge-entry-free verifier log (`projectRightQueryLog out.2.2.2.2 = []`), via a
  generic logging brick `queryLog_entries_not_p_of_isQueryBoundP_zero` (zero query budget ⟹
  no log entries at the targeted indices) and `support_simulateQ_subset`.
- **R2** `probOutput_true_le_tvDist_of_flag_false_left`: generic SPMF/TV brick — if a Boolean
  observable is identically `false` on the support of the left game, the probability it fires
  on the right game lower-bounds the TV distance (chains the VCVio bricks `tvDist_map_le` and
  `abs_probOutput_toReal_sub_le_tvDist`).
- **εB ground truth** `probOutput_challengeEntry_le_tvDist_hyb3Strict_hyb4`: for *every*
  basic-FS prover `P'`,
  `Pr[Hyb₄ outputs some with a challenge entry in the verifier log] ≤ Δ(Hyb3Strict, Hyb₄)`.
  In particular εB = 0 (and εB ≤ claim5_24Bound, wherever that event has larger probability)
  is **false**: the strict-split `hB` hypothesis of `hyb34Step_of_strictSplit` cannot be
  discharged below this event mass.
- **R4** `hyb34StepResidual_logShape_false`: conditional refutation of the *full*
  `Hyb34StepResidual` — given any bound `εA` on the genuine `Hyb₃ ↔ Hyb3Strict` bad-event leg
  with `claim5_24Bound + εA < Pr[challenge-entry event over Hyb₄ at the canonical witness]`,
  `Hyb34StepResidual` is false. (The triangle inequality routes the `Hyb3Strict` log-shape
  disjointness through `Hyb₃`.)

## What remains open (named residual, NOT proven)

- **R3** `Hyb4ChallengeEntryResidual`: every `some`-output of `Hyb₄` has a *nonempty*
  challenge log (one entry per challenge round of `V.fiatShamir`); under it, the event in the
  R4 hypothesis widens to the full `some`-mass of `Hyb₄`. This is a per-round log-suffix
  support induction over `deriveTranscriptFS` (Fin.induction round structure); it sharpens
  but is *not needed for* the refutation theorems above, whose event hypothesis is already
  decisive whenever the event mass exceeds the claimed budget.

The fully-quantified (hypothesis-free) `¬ Hyb34StepResidual` additionally needs a concrete
instance (`U`, `pSpec` with a challenge round, `Codec`, `LawfulTraceNablaImpl`, an
always-accepting `V`, …) on which the event probability is computed to exceed
`claim5_24Bound + εA`; building that instance is deliberately left out of this brick
(see the issue #314 brief `/tmp/eb_zero_brief.md`, Phase R).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.Hyb34LogShapeFalse

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids
  VerifierReplay

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it
-- (repo precedent: `VerifierReplay.lean`, `SimulatorBudgets.lean`).
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## R0 — right-summand log projection -/

section ProjectRight

/-- Project out the left-summand entries of a mixed query log, retaining the right summand
(mirror of `KeyLemmaFoundations.projectLeftQueryLog`). For the eager output surface
`oSpec + fsChallengeOracle StmtIn pSpec`, this extracts exactly the FS-challenge entries of a
verifier log. -/
def projectRightQueryLog {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₂ :=
  log.filterMap fun e =>
    match e with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- `projectRightQueryLog` is a list homomorphism. -/
lemma projectRightQueryLog_append {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} (l₁ l₂ : QueryLog (spec₁ + spec₂)) :
    projectRightQueryLog (l₁ ++ l₂)
      = projectRightQueryLog l₁ ++ projectRightQueryLog l₂ := by
  simp [projectRightQueryLog]

/-- A log all of whose entries sit in the left summand projects to the empty right log. -/
lemma projectRightQueryLog_eq_nil_of_forall_isLeft {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} (log : QueryLog (spec₁ + spec₂)) :
    (∀ e ∈ log, e.1.isLeft = true) → projectRightQueryLog log = [] := by
  induction log with
  | nil => intro _; rfl
  | cons e t ih =>
      intro h
      match e with
      | ⟨.inl q, r⟩ =>
          have ht : ∀ e' ∈ t, e'.1.isLeft = true :=
            fun e' he' => h e' (List.mem_cons_of_mem _ he')
          simpa [projectRightQueryLog, List.filterMap_cons] using ih ht
      | ⟨.inr q, r⟩ =>
          have := h ⟨.inr q, r⟩ List.mem_cons_self
          simp at this

end ProjectRight

/-! ## Generic logging brick — zero query budget means no targeted log entries -/

section LoggingBrick

universe u

/-- If `oa` makes **zero** queries at `p`-indices (`IsQueryBoundP oa p 0`), then no reachable
query log of the logged run contains a `p`-entry. The bridge from the F4/F5-style budget
facts to log-shape statements. -/
theorem queryLog_entries_not_p_of_isQueryBoundP_zero
    {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} (h : IsQueryBoundP oa p 0)
    {x : α} {log : QueryLog spec}
    (hmem : (x, log) ∈ support ((simulateQ loggingOracle oa).run)) :
    ∀ e ∈ log, ¬ p e.1 := by
  induction oa using OracleComp.inductionOn generalizing x log with
  | pure y =>
      simp only [simulateQ_pure] at hmem
      have hlog : log = [] := by
        revert hmem
        simp only [WriterT.run_pure', support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq]
        exact fun h2 => h2.2
      subst hlog
      simp
  | query_bind t mx ih =>
      rw [run_simulateQ_loggingOracle_query_bind] at hmem
      rw [isQueryBoundP_query_bind_iff] at h
      have hpt : ¬ p t := h.1.resolve_right (by omega)
      rw [mem_support_bind_iff] at hmem
      obtain ⟨u, -, hmem⟩ := hmem
      rw [support_map] at hmem
      obtain ⟨⟨y, log'⟩, hy, heq⟩ := hmem
      obtain ⟨hx, hlog⟩ := Prod.mk.injEq .. ▸ heq
      subst hx
      subst hlog
      have h0 : IsQueryBoundP (mx u) p 0 := by simpa using h.2 u
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hpt
      · exact ih u h0 hy e he'

end LoggingBrick

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
  {δ : ℕ} {Salt : Type}

/-! ## The challenge-summand classifier on the §5.4 simulator's outer spec -/

/-- Challenge classifier on the simulator's outer spec index
`ι ⊕ (κ ⊕ (Unit ⊕ ℕ))` (= `oSpec + D2SChallengePlusUnitOracle challengeSpec`): `true`
exactly on the external challenge summand. -/
def isChallengeEntryIdx {ι₁ κ : Type} : (ι₁ ⊕ (κ ⊕ (Unit ⊕ ℕ))) → Bool
  | .inr (.inl _) => true
  | _ => false

/-! ## R1-lite — the `d2fRaw` pipeline with a challenge-silent `gᵢ` realization makes zero
challenge queries

The run-shape and budget-composition helpers below mirror (and where `private` upstream,
locally restate) the `SimulatorBudgets` F4/F4b plumbing, specialized to the **zero-budget**
case: when the plugged-in `gImpl` makes no external queries at all on the challenge summand,
neither does the entire simulated run — for *any* source computation and *any* initial
states. -/

section ZeroBudgetPlumbing

variable {κ : Type} {challengeSpec : OracleSpec κ} {M : Type}

/-- Budget composition through a `StateT σ (AbortComp spec')`-level bind (local restatement of
the `private` `SimulatorBudgets.isQueryBoundP_run2_bind`). -/
private lemma isQueryBoundP_run2_bind' {ι' : Type} {spec' : OracleSpec ι'}
    {q : ι' → Prop} [DecidablePred q] {σ α β : Type}
    {x : StateT σ (AbortComp spec') α} {k : α → StateT σ (AbortComp spec') β}
    {b m : ℕ} {st : σ}
    (hx : IsQueryBoundP ((x.run st).run) q b)
    (hk : ∀ a s', IsQueryBoundP (((k a).run s').run) q m) :
    IsQueryBoundP (((x >>= k).run st).run) q (b + m) := by
  rw [StateT.run_bind, OptionT.run_bind]
  exact isQueryBoundP_elimM hx (isQueryBoundP_pure _ _ _) (fun pr => hk pr.1 pr.2)

/-- The aborting branch makes no queries (local restatement of the `private`
`SimulatorBudgets.isQueryBoundP_run2_lift_failure`). -/
private lemma isQueryBoundP_run2_lift_failure' {ι' : Type} {spec' : OracleSpec ι'}
    {q : ι' → Prop} [DecidablePred q] {σ α : Type} (st : σ) (b : ℕ) :
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

/-- The auxiliary `(Unit →ₒ U) + unifSpec` realization baked into `d2fOuterImpl` (local copy
of the `private` `SimulatorBudgets.d2fAuxImpl`; definitionally the inline `auxImpl` of
`d2fOuterImpl`). -/
private def auxImplD2F :
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

/-- Run-shape of `d2fOuterImpl` on a shared `oSpec` query: one forwarded query (local copy of
the `private` `SimulatorBudgets.d2fOuterImpl_run_inl`). -/
private lemma d2fOuterImpl_run_inl'
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
along the right injection (local copy of the `private`
`SimulatorBudgets.d2fOuterImpl_run_inr`). -/
private lemma d2fOuterImpl_run_inr'
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
              (auxImpl := auxImplD2F)
              dsq).run st).run m).run) := rfl

/-- Budget transfer along the right-injection `simulateQ` (local copy of the `private`
`SimulatorBudgets.isQueryBoundP_simulateQ_inclusion`). -/
private lemma isQueryBoundP_simulateQ_inclusion' {α : Type}
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
  refine IsQueryBoundP.simulateQ_of_step h (fun t _ => ?_) (fun t hnp => ?_)
  · exact (isQueryBoundP_query_iff _ _ _).mpr (fun _ => one_pos)
  · exact (isQueryBoundP_query_iff _ _ _).mpr (fun hqt => absurd ((hq t).mp hqt) hnp)

/-- The §5.4 `d2sQueryImpl` with a challenge-silent `gᵢ` realization makes **zero**
challenge-summand queries, on every source query and from every state. -/
private lemma d2sQueryImpl_challengeSilent_run_budget
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (hg : ∀ (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : M),
      IsQueryBoundP (((gImpl gq).run s).run)
        (fun (j : κ ⊕ (Unit ⊕ ℕ)) => j.isLeft = true) 0)
    (dsq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : M) :
    IsQueryBoundP
      ((((d2sQueryImpl (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (m := StateT M (OptionT (OracleComp
            (D2SChallengePlusUnitOracle (U := U) challengeSpec))))
          (gImpl := gImpl)
          (auxImpl := auxImplD2F)
          dsq).run s₁).run s₂).run)
      (fun (j : κ ⊕ (Unit ⊕ ℕ)) => j.isLeft = true) 0 := by
  unfold d2sQueryImpl
  refine isQueryBoundP_run2_bind' (b := 0) (m := 0) ?_ (fun pairOpt m' => ?_)
  · refine isQueryBoundP_simulateQ_stateT_optionT_of_step (p := fun _ => False)
      (isQueryBoundP_false _ 0) (fun t s => ?_) s₂
    match t with
    | Sum.inl gq =>
        simp only [QueryImpl.add_apply_inl]
        simpa using hg gq s
    | Sum.inr aux =>
        simp only [QueryImpl.add_apply_inr]
        have h0 : IsQueryBoundP
            ((query (spec := D2SChallengePlusUnitOracle (U := U) challengeSpec)
                (Sum.inr aux) :
                OracleComp (D2SChallengePlusUnitOracle (U := U) challengeSpec) _)
              >>= fun u => pure (some (u, s)))
            (fun (j : κ ⊕ (Unit ⊕ ℕ)) => j.isLeft = true) 0 := by
          simp only [HasQuery.instOfMonadLift_query]
          exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
            ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩
        simpa using h0
  · match pairOpt with
    | none => exact isQueryBoundP_run2_lift_failure' _ _
    | some p =>
        simp only [StateT.run_pure, OptionT.run_pure]
        exact isQueryBoundP_pure _ _ _

/-- Per-step challenge budget of `d2fOuterImpl` with a challenge-silent `gᵢ` realization:
**zero** challenge queries on every source query. -/
private lemma d2fOuterImpl_challengeSilent_step
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (hg : ∀ (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : M),
      IsQueryBoundP (((gImpl gq).run s).run)
        (fun (j : κ ⊕ (Unit ⊕ ℕ)) => j.isLeft = true) 0)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (s₁ : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (s₂ : M) :
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl t).run s₁).run
        s₂).run)
      (fun j => isChallengeEntryIdx j = true) 0 := by
  match t with
  | Sum.inl qo =>
      rw [d2fOuterImpl_run_inl']
      exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inl (by simp [isChallengeEntryIdx]), fun u => isQueryBoundP_pure _ _ _⟩
  | Sum.inr dsq =>
      rw [d2fOuterImpl_run_inr']
      exact isQueryBoundP_simulateQ_inclusion'
        (d2sQueryImpl_challengeSilent_run_budget gImpl hg dsq s₁ s₂)
        (fun t => by cases t <;> simp [isChallengeEntryIdx])

/-- **R1-lite (generic form)** — the whole `d2fRaw` pipeline with a challenge-silent `gᵢ`
realization makes zero challenge-summand queries, for any source computation and initial
memo. -/
theorem d2fRaw_challengeSilent_budget [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (hg : ∀ (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) (s : M),
      IsQueryBoundP (((gImpl gq).run s).run)
        (fun (j : κ ⊕ (Unit ⊕ ℕ)) => j.isLeft = true) 0)
    {α : Type}
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    IsQueryBoundP
      ((d2fRaw (T_H := T_H) (T_P := T_P) gImpl comp initM).run)
      (fun j => isChallengeEntryIdx j = true) 0 := by
  unfold d2fRaw
  exact isQueryBoundP_simulateQ_stateT2_optionT_of_step (p := fun _ => False)
    (isQueryBoundP_false comp 0)
    (fun t s₁ s₂ => by simpa using d2fOuterImpl_challengeSilent_step gImpl hg t s₁ s₂)
    default initM

end ZeroBudgetPlumbing

/-! ## R1-lite at the hit-only bridge -/

section HitOnlyBudget

variable [SaltCodec U δ Salt]

/-- The hit-only bridge is challenge-silent: it makes **no external queries at all** — `pure`
of the stored response on a hit (`d2sCodecBridgeImplMemoHitOnly_run_hit`), `pure none` on a
miss (`…_run_miss`). -/
lemma d2sCodecBridgeImplMemoHitOnly_challenge_silent
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    IsQueryBoundP
      (((d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run)
      (fun j => j.isLeft = true) 0 := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r =>
      rw [d2sCodecBridgeImplMemoHitOnly_run_hit gq memo r hl]
      exact isQueryBoundP_pure _ _ _
  | none =>
      rw [d2sCodecBridgeImplMemoHitOnly_run_miss gq memo hl]
      exact isQueryBoundP_pure _ _ _

/-- **R1-lite** — the `Hyb3Strict` verifier pipeline (`d2fRaw` with the hit-only bridge)
makes **zero** challenge-summand queries, for any source computation and shared memo. This is
the `IsQueryBoundP … 0` boundary fact in the F4/F5 `SimulatorBudgets` idiom. -/
theorem d2fRaw_hitOnly_challenge_budget {α : Type}
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    IsQueryBoundP
      ((d2fRaw (T_H := T_H) (T_P := T_P)
        (d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt)) comp memo).run)
      (fun j => isChallengeEntryIdx j = true) 0 :=
  d2fRaw_challengeSilent_budget _
    (fun gq s => d2sCodecBridgeImplMemoHitOnly_challenge_silent gq s) comp memo

end HitOnlyBudget

/-! ## R1 — every `some`-output of `Hyb3Strict` has a challenge-free verifier log -/

section R1

variable [SaltCodec U δ Salt]

/-- Entries surviving `projectChallengePlusUnitQueryLog` from a challenge-entry-free raw log
all sit in the left (`oSpec`) summand. -/
private lemma project_isLeft_of_challenge_free
    (raw : QueryLog (oSpec + D2SChallengePlusUnitOracle (U := U)
      (fsChallengeOracle (StmtIn × Salt) pSpec)))
    (hfree : ∀ e ∈ raw, ¬ (isChallengeEntryIdx e.1 = true)) :
    ∀ e' ∈ projectChallengePlusUnitQueryLog (oSpec := oSpec) (U := U) raw,
      e'.1.isLeft = true := by
  intro e' he'
  unfold projectChallengePlusUnitQueryLog at he'
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp he'
  match e with
  | ⟨.inl q, r⟩ =>
      simp only [Option.some.injEq] at hfe
      subst hfe
      rfl
  | ⟨.inr (.inl q), r⟩ =>
      exact absurd (by simp [isChallengeEntryIdx]) (hfree ⟨.inr (.inl q), r⟩ he)
  | ⟨.inr (.inr q), r⟩ =>
      simp at hfe

/-- The salt-erasing line-4 remap preserves the summand of every entry, so an all-left log
stays all-left. Stated against the literal `filterMap` body of `hyb3Line4SaltErase`. -/
private lemma saltErase_isLeft_of_isLeft
    (l : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (hl : ∀ e ∈ l, e.1.isLeft = true) :
    ∀ e' ∈ (l.filterMap (fun entry =>
        match entry with
        | ⟨.inl q, r⟩ => some ⟨.inl q, r⟩
        | ⟨.inr ⟨roundIdx, ((stmt, _salt), messagesBefore)⟩, challenge⟩ =>
            some ⟨.inr ⟨roundIdx, (stmt, messagesBefore)⟩, challenge⟩) :
        QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)),
      e'.1.isLeft = true := by
  intro e' he'
  obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp he'
  match e with
  | ⟨.inl q, r⟩ =>
      simp only [Option.some.injEq] at hfe
      subst hfe
      rfl
  | ⟨.inr ⟨roundIdx, ((stmt, salt), messagesBefore)⟩, challenge⟩ =>
      exact absurd (hl _ he) (by simp)

/-- **R1** — every `some`-output of the `Hyb3Strict` game body has a verifier log with zero
`fsChallengeOracle` entries: the hit-only bridge never queries the challenge summand
(R1-lite), the `auxImpl` of `d2fOuterImpl` only emits `.inr (.inr _)` queries, and the line-4
maps preserve challenge-freeness. -/
theorem hyb3Strict_vLog_challenge_free [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (out : StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (h : some out ∈ support (hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (hyb3Line4SaltErase Salt) oImpl V P)) :
    projectRightQueryLog out.2.2.2.2 = [] := by
  simp only [hybGameEagerSplit, mem_support_bind_iff] at h
  obtain ⟨c, -, ⟨pRes?, pLogRaw⟩, -, h⟩ := h
  match pRes? with
  | none => simp at h
  | some ⟨⟨⟨stmtIn, messages⟩, dst⟩, memo⟩ =>
      simp only [mem_support_bind_iff] at h
      obtain ⟨⟨vRes?, vLogRaw⟩, hv, h⟩ := h
      -- the verifier-side raw log is challenge-free
      have hv' : (vRes?, vLogRaw) ∈ support
          ((simulateQ loggingOracle
            ((d2fRaw (T_H := T_H) (T_P := T_P)
              (d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
                (δ := δ) (Salt := Salt))
              ((V.duplexSpongeFiatShamir.run
                stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
              memo).run)).run) :=
        support_simulateQ_subset _ _ hv
      have hfree : ∀ e ∈ vLogRaw, ¬ (isChallengeEntryIdx e.1 = true) :=
        queryLog_entries_not_p_of_isQueryBoundP_zero
          (d2fRaw_hitOnly_challenge_budget _ memo) hv'
      rcases vRes? with _ | ⟨⟨stmtOut?, dst'⟩, memo'⟩
      · simp at h
      · rcases stmtOut? with _ | stmtOut
        · simp at h
        · simp only [mem_support_bind_iff] at h
          obtain ⟨pLog'?, -, vLog'?, hvl, h⟩ := h
          rcases pLog'? with _ | pLog' <;> rcases vLog'? with _ | vLog'
          · simp at h
          · simp at h
          · simp at h
          · simp only [support_pure, Set.mem_singleton_iff,
              Option.some.injEq] at h
            subst h
            -- pin down `vLog'` from the deterministic line-4 map
            simp only [hyb3Line4SaltErase, OptionT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff, Option.some.injEq] at hvl
            subst hvl
            exact projectRightQueryLog_eq_nil_of_forall_isLeft _
              (saltErase_isLeft_of_isLeft _
                (project_isLeft_of_challenge_free vLogRaw hfree))

end R1

/-! ## R2 — generic TV lower bound from a one-sided Boolean observable -/

section R2

/-- **R2** — if a Boolean observable is identically `false` on the support of the left game,
the probability it fires on the right game lower-bounds the TV distance (VCVio bricks
`tvDist_map_le` + `abs_probOutput_toReal_sub_le_tvDist`). -/
theorem probOutput_true_le_tvDist_of_flag_false_left
    {α : Type} (game₁ game₂ : ProbComp α) (f : α → Bool)
    (h₁ : ∀ x ∈ support game₁, f x = false) :
    (Pr[= true | f <$> game₂]).toReal ≤ tvDist game₁ game₂ := by
  have h0 : Pr[= true | f <$> game₁] = 0 := by
    refine probOutput_eq_zero_of_not_mem_support ?_
    rw [support_map]
    rintro ⟨x, hx, hfx⟩
    rw [h₁ x hx] at hfx
    cases hfx
  have habs := abs_probOutput_toReal_sub_le_tvDist (f <$> game₁) (f <$> game₂)
  have hmap := tvDist_map_le f game₁ game₂
  rw [h0] at habs
  simp only [ENNReal.toReal_zero, zero_sub, abs_neg,
    abs_of_nonneg ENNReal.toReal_nonneg] at habs
  linarith

end R2

/-! ## The challenge-entry observable and the εB ground truth -/

section EBGroundTruth

variable [SaltCodec U δ Salt]

/-- The F1 Boolean observable: `true` exactly on `some`-outputs whose verifier log contains
at least one `fsChallengeOracle` entry. -/
def challengeEntryFlag :
    Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) → Bool :=
  fun o? => o?.elim false fun o => !(projectRightQueryLog o.2.2.2.2).isEmpty

/-- The flag never fires on `Hyb3Strict` (R1 in observable form). -/
lemma challengeEntryFlag_false_on_hyb3Strict [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ∀ x ∈ support (hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (hyb3Line4SaltErase Salt) oImpl V P),
      challengeEntryFlag (oSpec := oSpec) x = false := by
  intro x hx
  match x with
  | none => rfl
  | some out =>
      have := hyb3Strict_vLog_challenge_free (T_H := T_H) (T_P := T_P) (δ := δ)
        (Salt := Salt) oImpl V P out hx
      simp [challengeEntryFlag, this]

/-- **εB ground truth (the F1 refutation core)** — for *every* basic-FS prover `P'`, the
probability that `Hyb₄` outputs `some` with a challenge entry in the verifier log
lower-bounds `Δ(Hyb3Strict, Hyb₄)`. Wherever this event has positive probability, εB = 0 is
false; wherever it exceeds `claim5_24Bound`, the strict-split `hB` budget of
`hyb34Step_of_strictSplit` is unsatisfiable. -/
theorem probOutput_challengeEntry_le_tvDist_hyb3Strict_hyb4 [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages)) :
    (Pr[= true | challengeEntryFlag (oSpec := oSpec) <$>
        basicFiatShamirGameEagerRand
          (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)) oImpl V P']).toReal
      ≤ SPMF.tvDist (Hyb3Strict T_H T_P δ Salt oImpl V P) (Hyb4 oImpl V P') :=
  probOutput_true_le_tvDist_of_flag_false_left _ _ _
    (challengeEntryFlag_false_on_hyb3Strict (T_H := T_H) (T_P := T_P) (δ := δ)
      (Salt := Salt) oImpl V P)

end EBGroundTruth

/-! ## R3 — the `Hyb₄` challenge-entry residual (open) -/

section R3Residual

/-- **R3 (open)** — every `some`-output of `Hyb₄` has a verifier log with at least one
`fsChallengeOracle` entry, provided `pSpec` has a challenge round: `V.fiatShamir` re-derives
each challenge by an explicit `fsChallengeOracle` query inside the logged run
(`Verifier.fiatShamir` / `deriveTranscriptFS`, `ArkLib/OracleReduction/FiatShamir/Basic.lean`).
Discharging this is a per-round log-suffix support induction over the `Fin.induction` round
structure of `deriveTranscriptFS`. Under this residual, the event in
`hyb34StepResidual_logShape_false` widens to the full `some`-mass of `Hyb₄` (the flag fires
on **every** `some`-output). -/
def Hyb4ChallengeEntryResidual : Prop :=
  ∀ (_ : Nonempty pSpec.ChallengeIdx)
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages))
    (out : StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)),
    some out ∈ support (basicFiatShamirGameEagerRand
      (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)) oImpl V P') →
    projectRightQueryLog out.2.2.2.2 ≠ []

end R3Residual

/-! ## R4 — conditional refutation of `Hyb34StepResidual` -/

section R4

variable [SaltCodec U δ Salt]

/-- **R4 — conditional refutation of the full CO25 Claim 5.24 step residual.** Given
1. any upper bound `εA` on the genuine `Hyb₃ ↔ Hyb3Strict` leg (the bad-event mass that the
   εA side of the strict split would have to certify anyway), and
2. an instance where the `Hyb₄` challenge-entry event mass at the canonical witness exceeds
   `claim5_24Bound + εA`,

`Hyb34StepResidual` is **false**: by R1+R2 the event mass lower-bounds
`Δ(Hyb3Strict, Hyb₄)`, while the residual plus the triangle inequality would cap it at
`εA + claim5_24Bound`.

What instantiation remains for an unconditional `¬ Hyb34StepResidual`: a concrete
(`U`, `pSpec`-with-challenge-round, `Codec`, `LawfulTraceNablaImpl`, always-accepting `V`)
instance with a computed event mass above the budget — deliberately out of scope for this
ground-truth brick (see module docstring). -/
theorem hyb34StepResidual_logShape_false [SampleableType U]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ L : ℕ)
    (hL : pSpec.totalNumPermQueries ≤ L)
    (hHash : IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ)
    (hPerm : IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ)
    (hPermInv : IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ)
    (εA : ℝ)
    (hA : SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
      (Hyb3Strict T_H T_P δ Salt oImpl V P) ≤ εA)
    (hgap : claim5_24Bound U tₕ tₚ tₚᵢ L + εA
      < (Pr[= true | challengeEntryFlag (oSpec := oSpec) <$>
          basicFiatShamirGameEagerRand
            (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec)) oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt)
              P)]).toReal) :
    ¬ Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro hres
  have h34 := hres V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have hev := probOutput_challengeEntry_le_tvDist_hyb3Strict_hyb4
    (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt) oImpl V P
    (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P)
  have htri := SPMF.tvDist_triangle (Hyb3Strict T_H T_P δ Salt oImpl V P)
    (Hyb3 T_H T_P δ Salt oImpl V P)
    (Hyb4 oImpl V
      (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
  have hcomm : SPMF.tvDist (Hyb3Strict T_H T_P δ Salt oImpl V P)
      (Hyb3 T_H T_P δ Salt oImpl V P)
      = SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
        (Hyb3Strict T_H T_P δ Salt oImpl V P) :=
    SPMF.tvDist_comm _ _
  linarith

end R4

#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.projectRightQueryLog_append
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.projectRightQueryLog_eq_nil_of_forall_isLeft
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.queryLog_entries_not_p_of_isQueryBoundP_zero
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.d2fRaw_challengeSilent_budget
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.d2sCodecBridgeImplMemoHitOnly_challenge_silent
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.d2fRaw_hitOnly_challenge_budget
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.hyb3Strict_vLog_challenge_free
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.probOutput_true_le_tvDist_of_flag_false_left
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.challengeEntryFlag_false_on_hyb3Strict
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.probOutput_challengeEntry_le_tvDist_hyb3Strict_hyb4
#print axioms DuplexSpongeFS.Hyb34LogShapeFalse.hyb34StepResidual_logShape_false

end DuplexSpongeFS.Hyb34LogShapeFalse

end
