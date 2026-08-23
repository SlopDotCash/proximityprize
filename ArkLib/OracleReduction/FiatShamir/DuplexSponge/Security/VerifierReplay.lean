/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaHybrids

/-!
# CO25 Claim 5.24 — verifier replay for `Hyb₃ → Hyb₄`: the deterministic layer

This module proves the **deterministic-replay layer** of CO25 Claim 5.24 (Eq. 55), the
`Hyb₃ → Hyb₄` step of the §5.8 ladder (`KeyLemmaHybrids.Hyb34StepResidual`): in `Hyb₄` the
basic-FS verifier re-derives challenges by reading the once-sampled FS table at the keys the
simulated prover `P' = D2SAlgo^f(𝒫̃)` queried; the lemmas here show that this re-derivation
**matches what the simulator committed**, query by query, unconditionally.

## The deterministic-replay layer (all proven, axiom-clean)

Three independent determinism mechanisms make the replay exact:

1. **`tr_i` memo determinism in run form** (CO25 §5.4 D2SAlgo Item 3, completing the F6
   bricks of `KeyLemmaFoundations`): on a memo hit the Eq. 16 bridge is a *pure* computation
   that returns the stored response and leaves the memo unchanged
   (`d2sCodecBridgeImplMemo_run_hit`); on a miss it commits its fresh response into the memo
   (`d2sCodecBridgeImplMemo_commit`), so a replay of the same key — in particular by the
   `Hyb₃` verifier, which *shares* the prover's memo — deterministically returns the
   committed response (`d2sCodecBridgeImplMemo_replay`), and earlier bindings persist
   (`d2sCodecBridgeImplMemo_preserves_lookup`). The same statements hold for the eager
   unsalted bridge actually used by `Hyb₃` (`d2sCodecBridgeImplMemoEager_run_eq` reduces it
   to the salted bridge under the salt-erasing re-keying; `..._run_hit` / `..._commit` /
   `..._replay`).

2. **`ψ`/`ψ⁻¹` codec round-trip** (CO25 Def. 4.1): every encoded challenge `ρ̂ᵢ` the
   simulator hands the malicious prover is sampled from `ψᵢ⁻¹(ρᵢ)`, so it deserializes back
   to *exactly* the FS challenge `ρᵢ` the basic-FS verifier re-derives
   (`deserialize_of_mem_support_uniformDeserializePreimage` and its `simulateQ` form). Note
   that the *matching* is exact — `codec.decodingBias` does **not** enter this step; the
   bias is paid once at the `Hyb₁ → Hyb₂` step (Claim 5.22).

3. **Eager-table read determinism**: against the once-sampled `f ← 𝒟_IP` carrier, every
   oracle read is `pure` of the table value (`uniform_toImpl_apply`), so the prover-time
   `fᵢ` query and the verifier-time replay of the same key return the same challenge. The
   keystone `memoCoherentTable_keystone` combines all three mechanisms: against a fixed
   table `c`, every response the memoized bridge ever serves deserializes to `c` at the
   replayed FS key `(i, (𝕩, τ̌), α_{<i})` — i.e. the `Hyb₄` verifier's re-derived transcript
   coincides with the simulator's committed transcript — and the coherence invariant
   `MemoCoherentTable` is preserved across the run.

## The probabilistic part (the genuinely open core, named obligations)

What remains of Claim 5.24 is the *divergence analysis*: the probability that the `Hyb₃`
verifier's `D2SQuery` run does **not** follow the pure replay path — a fresh (non-memoized)
`gᵢ` query, a `φ⁻¹` parse failure, or a BackTrack/LookAhead asymmetry against the trace the
honest verifier itself generates — bounded by `claim5_24Bound` (CO25's bad event `E_𝒱`,
Eq. 55). This module instruments the split exactly as CO25 does:

- `d2sCodecBridgeImplMemoEagerHitOnly` — the *hit-only* bridge that aborts on any verifier
  `gᵢ` miss (proven to agree with the real bridge on hits:
  `d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit`);
- `hybGameEagerSplit` — the Figure-4 skeleton with separate prover/verifier `gᵢ`
  realizations sharing the `tr_i` memo (diagonal identification
  `hybGameEagerSplit_diag` with `KeyLemmaHybrids.hybGameEager`);
- `Hyb3Strict` — `Hyb₃` with the hit-only verifier bridge;
- **`hyb34Step_of_strictSplit`** (proven): any two coupling bounds
  `Δ(Hyb₃, Hyb₃Strict) ≤ εA` (the bad-event mass) and `Δ(Hyb₃Strict, Hyb₄) ≤ εB` (the
  hit-path collapse) with `εA + εB ≤ claim5_24Bound` assemble into the full
  `Hyb34StepResidual`. The two coupling bounds themselves are the open research core; they
  require CO25's §5.6 trace analysis (Lemmas 5.8–5.10 applied to the verifier's replayed
  trace) and are *not* axiomatized here — `Hyb34StepResidual` (KeyLemmaHybrids) remains the
  single consuming obligation.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.VerifierReplay

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

-- Sections below share one DSFS-wide variable block; several bricks use only a slice of it.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! ## Generic support bricks -/

section SupportBricks

universe u

/-- Simulating an oracle computation through *any* oracle-valued implementation can only
shrink the support: every output reachable after `simulateQ` was already reachable in the
source computation (where each query may return any value). Oracle-monad analogue of VCVio's
`support_simulateQ_run'_subset` (which covers the `StateT` case). -/
theorem support_simulateQ_subset {ι₁ ι₂ : Type u} {spec : OracleSpec ι₁}
    {spec' : OracleSpec ι₂} {α : Type u}
    (impl : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      intro x hx
      rw [simulateQ_query_bind] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query t u, ih u hx⟩

end SupportBricks

/-! ## DSFS context -/

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {δ : ℕ} {Salt : Type}

/-! ## `tr_i` memo lookup toolkit (completing the F6 bricks)

`lookupD2SAlgoMemo` is a first-match-wins left fold. The bricks below give it a clean
head/tail calculus: persistence of earlier bindings under arbitrary memo extension, skipping
of non-matching prefixes, and inversion of a singleton hit. -/

section MemoLookup

/-- F6b generalized — a binding present in `m₁` survives extension by an arbitrary suffix
`m₂` (first match wins). The across-the-run persistence form of
`lookupD2SAlgoMemo_insert_stable`. -/
lemma lookupD2SAlgoMemo_append_of_some
    (m₁ m₂ : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (x : StmtIn) (s : Salt)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (r : Vector U (challengeSize (pSpec := pSpec) i))
    (h : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        m₁ i x s em = some r) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        (m₁ ++ m₂) i x s em = some r := by
  induction m₂ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t e ih =>
      rw [← List.append_assoc]
      exact lookupD2SAlgoMemo_insert_stable (m₁ ++ t) e i x s em r ih

/-- A prefix with no binding at the key is transparent to lookup. -/
lemma lookupD2SAlgoMemo_append_of_none
    (m₁ m₂ : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (x : StmtIn) (s : Salt)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (h : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        m₁ i x s em = none) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        (m₁ ++ m₂) i x s em
      = lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
          m₂ i x s em := by
  unfold lookupD2SAlgoMemo at h ⊢
  rw [List.foldl_append, h]

/-- Inversion of a singleton-memo hit: a successful match forces the entry to carry exactly
the queried key and the returned response (`HEq` for the round-indexed fields). -/
private lemma lookupD2SAlgoMemo_singleton_some_inv
    {e : D2SAlgoMemoEntry StmtIn U δ Salt pSpec}
    {i : pSpec.ChallengeIdx} {x : StmtIn} {s : Salt}
    {em : pSpec.EncodedMessagesBefore U i.1.castSucc}
    {r : Vector U (challengeSize (pSpec := pSpec) i)}
    (h : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        [e] i x s em = some r) :
    ∃ _hRound : e.roundIdx = i, e.stmt = x ∧ e.salt = s
      ∧ HEq e.encodedMessages em ∧ HEq e.response r := by
  obtain ⟨eR, eX, eS, eEm, eResp⟩ := e
  by_cases hR : eR = i
  · subst hR
    by_cases hc : eX = x ∧ eS = s ∧ eEm = em
    · have heval : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
          (pSpec := pSpec)
          [(⟨eR, eX, eS, eEm, eResp⟩ : D2SAlgoMemoEntry StmtIn U δ Salt pSpec)] eR x s em
          = some eResp :=
        dite_eq_iff.mpr (Or.inl ⟨rfl, if_pos hc⟩)
      rw [heval] at h
      cases h
      exact ⟨rfl, hc.1, hc.2.1, heq_of_eq hc.2.2, HEq.rfl⟩
    · have heval : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
          (pSpec := pSpec)
          [(⟨eR, eX, eS, eEm, eResp⟩ : D2SAlgoMemoEntry StmtIn U δ Salt pSpec)] eR x s em
          = none :=
        dite_eq_iff.mpr (Or.inl ⟨rfl, if_neg hc⟩)
      rw [heval] at h
      simp at h
  · have heval : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec)
        [(⟨eR, eX, eS, eEm, eResp⟩ : D2SAlgoMemoEntry StmtIn U δ Salt pSpec)] i x s em
        = none :=
      dite_eq_iff.mpr (Or.inr ⟨hR, rfl⟩)
    rw [heval] at h
    simp at h

end MemoLookup

/-! ## Run-shape lemmas for the memoized Eq. 16 bridge (salted) -/

section SaltedBridgeShapes

variable [SaltCodec U δ Salt]

/-- Hit purity (CO25 §5.4 D2SAlgo Item 3, run form): on a `tr_i` memo hit the memoized
bridge makes **no oracle queries and no state change** — it is `pure` of the stored response
with the memo untouched. This is the deterministic half of the verifier replay: a key the
prover already committed is answered without consulting `f` again. -/
lemma d2sCodecBridgeImplMemo_run_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run
      = pure (some (r, memo)) := by
  unfold d2sCodecBridgeImplMemo
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  rfl

/-- The fresh entry committed by a miss of the memoized bridge at query `gq` with response
`resp` (CO25 §5.4 D2SAlgo Item 3, the `tr_i ∪ {(i, 𝕩, τ̌, α̂) ↦ ρ̂}` step). -/
@[reducible]
def bridgeMemoEntry (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (resp : Vector U (challengeSize (pSpec := pSpec) gq.1)) :
    D2SAlgoMemoEntry StmtIn U δ Salt pSpec :=
  { roundIdx := gq.1, stmt := gq.2.1,
    salt := SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1,
    encodedMessages := gq.2.2.2, response := resp }

/-- Miss shape: on a `tr_i` memo miss the memoized bridge is the raw Eq. 16 bridge followed
by the deterministic memo insert (abort propagating as `none`). -/
lemma d2sCodecBridgeImplMemo_run_miss
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = none) :
    ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run
      = (d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run >>= fun o =>
            match o with
            | none => pure none
            | some resp =>
                pure (some (resp, insertD2SAlgoMemo memo
                  (bridgeMemoEntry (Salt := Salt) gq resp))) := by
  unfold d2sCodecBridgeImplMemo
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  simp only [StateT.run_monadLift, monadLift_self, OptionT.run_bind, bind_assoc, pure_bind]
  unfold Option.elimM
  refine bind_congr fun o => ?_
  match o with
  | none => rfl
  | some resp => simp [insertD2SAlgoMemo, bridgeMemoEntry, Option.elim]

/-- Commit (CO25 §5.4 D2SAlgo Item 3): every successful outcome `(r, memo')` of the memoized
bridge records its own binding — the output memo looks up the queried key to exactly the
returned response, and extends the input memo by a (possibly empty) suffix. -/
theorem d2sCodecBridgeImplMemo_commit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run)) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo' gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r
    ∧ ∃ tail, memo' = memo ++ tail := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r₀ =>
      rw [d2sCodecBridgeImplMemo_run_hit gq memo r₀ hl] at h
      replace h : some (r, memo') ∈ support
          ((pure (some (r₀, memo)) : OracleComp
            (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
            (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
              × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hm⟩ := h
      subst hr; subst hm
      exact ⟨hl, [], by simp⟩
  | none =>
      rw [d2sCodecBridgeImplMemo_run_miss gq memo hl] at h
      obtain ⟨o, _, h⟩ := (mem_support_bind_iff _ _ _).mp h
      match o with
      | none =>
          replace h : some (r, memo') ∈ support
              ((pure none : OracleComp
                (D2SChallengePlusUnitOracle (U := U)
                  (fsChallengeOracle (StmtIn × Salt) pSpec))
                (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
                  × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
          simp at h
      | some resp =>
          replace h : some (r, memo') ∈ support
              ((pure (some (resp, insertD2SAlgoMemo memo
                  (bridgeMemoEntry (Salt := Salt) gq resp))) : OracleComp
                (D2SChallengePlusUnitOracle (U := U)
                  (fsChallengeOracle (StmtIn × Salt) pSpec))
                (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
                  × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
          simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hr, hm⟩ := h
          subst hr; subst hm
          refine ⟨?_, [bridgeMemoEntry (Salt := Salt) gq r], rfl⟩
          exact lookupD2SAlgoMemo_insert_self_of_none memo
            (bridgeMemoEntry (Salt := Salt) gq r) hl

/-- **Verifier replay determinism at the bridge** (CO25 §5.4 D2SAlgo Item 3, the property
Claim 5.24 consumes): once the memoized bridge has answered `gq` with `(r, memo')`, replaying
the *same* key against `memo'` — as the `Hyb₃` verifier does, sharing the prover's memo — is
a pure computation returning the committed `r` with no further oracle interaction. -/
theorem d2sCodecBridgeImplMemo_replay
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run)) :
    ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo').run
      = pure (some (r, memo')) :=
  d2sCodecBridgeImplMemo_run_hit gq memo' r (d2sCodecBridgeImplMemo_commit gq memo r memo' h).1

/-- Persistence: a binding present before a bridge call survives it (Item 3 across the whole
run — together with `d2sCodecBridgeImplMemo_commit` this gives same-key-same-response for
*every* pair of `gᵢ` queries in a run, prover- or verifier-side). -/
theorem d2sCodecBridgeImplMemo_preserves_lookup
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run))
    (i : pSpec.ChallengeIdx) (x : StmtIn) (s : Salt)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (r₀ : Vector U (challengeSize (pSpec := pSpec) i))
    (h₀ : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo i x s em = some r₀) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo' i x s em = some r₀ := by
  obtain ⟨tail, htail⟩ := (d2sCodecBridgeImplMemo_commit gq memo r memo' h).2
  subst htail
  exact lookupD2SAlgoMemo_append_of_some memo tail i x s em r₀ h₀

end SaltedBridgeShapes

/-! ## Run-shape lemmas for the eager unsalted bridge (the `Hyb₃` realization) -/

section EagerBridgeShapes

variable [SaltCodec U δ Salt]

/-- The eager unsalted bridge **is** the salted Eq. 16 bridge under the salt-erasing
re-keying: its run is exactly `simulateQ saltEraseChallengePlusUnitImpl` of the salted run.
All salted determinism bricks transfer along this identity. -/
lemma d2sCodecBridgeImplMemoEager_run_eq
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run
      = simulateQ
          (saltEraseChallengePlusUnitImpl (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (Salt := Salt))
          (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (Salt := Salt) gq).run memo).run) := by
  unfold d2sCodecBridgeImplMemoEager
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
    OptionT.run_bind, OptionT.run_mk, StateT.run_set, bind_assoc, pure_bind]
  unfold Option.elimM
  refine Eq.trans (bind_congr fun o => ?_) (bind_pure _)
  match o with
  | none => rfl
  | some res => rfl

/-- Hit purity for the eager bridge: a `tr_i` memo hit is answered purely, with no oracle
queries and no memo change (eager twin of `d2sCodecBridgeImplMemo_run_hit`). -/
lemma d2sCodecBridgeImplMemoEager_run_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run
      = pure (some (r, memo)) := by
  rw [d2sCodecBridgeImplMemoEager_run_eq gq memo,
    d2sCodecBridgeImplMemo_run_hit gq memo r hl]
  rfl

/-- Commit for the eager bridge: every successful outcome records its binding and extends
the memo (transferred from the salted bridge along `support_simulateQ_subset`). -/
theorem d2sCodecBridgeImplMemoEager_commit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run)) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo' gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r
    ∧ ∃ tail, memo' = memo ++ tail := by
  rw [d2sCodecBridgeImplMemoEager_run_eq gq memo] at h
  exact d2sCodecBridgeImplMemo_commit gq memo r memo' (support_simulateQ_subset _ _ h)

/-- Verifier replay determinism for the eager bridge actually plugged into `Hyb₃`: replaying
a committed key against the shared memo is pure and returns the committed response. -/
theorem d2sCodecBridgeImplMemoEager_replay
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support
      (((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run)) :
    ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo').run
      = pure (some (r, memo')) :=
  d2sCodecBridgeImplMemoEager_run_hit gq memo' r
    (d2sCodecBridgeImplMemoEager_commit gq memo r memo' h).1

end EagerBridgeShapes

/-! ## `ψ`/`ψ⁻¹` codec round-trip and eager-table read determinism -/

section CodecRoundTrip

/-- Sampling from a list can only return list elements. -/
private lemma mem_of_mem_support_sampleFromList
    {α κ : Type} {challengeSpec : OracleSpec κ}
    (l : List α) (hl : l ≠ []) (x : α)
    (hx : x ∈ support (sampleFromList (U := U) (challengeSpec := challengeSpec) l hl)) :
    x ∈ l := by
  unfold sampleFromList at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨idxRaw, _, hx⟩ := hx
  subst hx
  exact List.get_mem l _

/-- **`ψ`/`ψ⁻¹` round-trip** (CO25 Def. 4.1, the exact-matching half of Claim 5.24): every
encoded challenge `ρ̂ᵢ` in the support of the `ψᵢ⁻¹` uniform-preimage sampler deserializes to
exactly the challenge `ρᵢ` it was sampled for. The committed response the simulator hands
the malicious prover therefore re-derives, under the verifier's `ψᵢ`, the very FS challenge
the basic-FS verifier reads from the table — with **zero** error (`codec.decodingBias` does
not enter this step). -/
theorem deserialize_of_mem_support_uniformDeserializePreimage
    {κ : Type} {challengeSpec : OracleSpec κ} {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) (v : Vector U (challengeSize (pSpec := pSpec) i))
    (hv : v ∈ support (uniformDeserializePreimage (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec) ch)) :
    Deserialize.deserialize v = ch := by
  unfold uniformDeserializePreimage at hv
  have hmem := mem_of_mem_support_sampleFromList (U := U) (challengeSpec := challengeSpec)
    _ _ v hv
  rw [Finset.mem_toList] at hmem
  unfold deserializePreimageFinset at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- `simulateQ` form of the round-trip, for use inside table-instantiated bridge runs. -/
theorem deserialize_of_mem_support_simulateQ_uniformDeserializePreimage
    {κ ι₂ : Type} {challengeSpec : OracleSpec κ} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl (D2SChallengePlusUnitOracle (U := U) challengeSpec) (OracleComp spec₂))
    {i : pSpec.ChallengeIdx}
    (ch : pSpec.Challenge i) (v : Vector U (challengeSize (pSpec := pSpec) i))
    (hv : v ∈ support (simulateQ impl (uniformDeserializePreimage (pSpec := pSpec) (U := U)
      (challengeSpec := challengeSpec) ch))) :
    Deserialize.deserialize v = ch :=
  deserialize_of_mem_support_uniformDeserializePreimage ch v
    (support_simulateQ_subset impl _ hv)

/-- **Eager-table read determinism**: against a once-sampled uniform oracle carrier, every
read is `pure` of the table value — so the prover-time `fᵢ` query and the `Hyb₄` verifier's
replay of the same key deterministically return the same challenge. -/
lemma uniform_toImpl_apply {ι' : Type} (spec' : OracleSpec ι')
    [SampleableType (OracleFamily spec')]
    (c : (OracleDistribution.uniform spec').Carrier) (q : spec'.Domain) :
    (OracleDistribution.uniform spec').toImpl c q = pure (c q) := rfl

end CodecRoundTrip

/-! ## The table-coupling keystone: committed responses match the replayed table reads -/

section TableCoupling

variable [SaltCodec U δ Salt]

/-- Instantiate the FS-challenge summand of the bridge's oracle surface with a fixed eager
table `c`, leaving the auxiliary `(Unit →ₒ U) + unifSpec` sampling oracles free. This is the
bridge's view of the `Hyb₃`/`Hyb₄` experiment after line 1 (`f ← 𝒟_IP`) has been sampled. -/
def fsTableAuxImpl (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    QueryImpl
      (D2SChallengePlusUnitOracle (U := U) (fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleComp ((Unit →ₒ U) + unifSpec)) :=
  fun q =>
    match q with
    | .inl qf => pure (c qf)
    | .inr aux => query (spec := (Unit →ₒ U) + unifSpec) aux

/-- The replayed basic-FS key of a `gSpec` query (CO25 §5.4 Eq. 16 Step 2): round index,
statement augmented with the binarized salt, and the `φ⁻¹`-decoded message prefix. -/
@[reducible]
def replayKey (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc) :
    (fsChallengeOracle (StmtIn × Salt) pSpec).Domain :=
  ⟨gq.1, ((gq.2.1, SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1), msgs)⟩

/-- Raw-bridge table coupling: against a fixed FS table `c`, every successful response of the
Eq. 16 bridge `ψ⁻¹ ∘ f ∘ φ⁻¹` deserializes to exactly the table value at the replayed key.
This is the per-query content of "the re-derived transcript matches the simulator's
commitment". -/
theorem deserialize_of_mem_support_bridge_table
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hr : some r ∈ support (simulateQ (fsTableAuxImpl (U := U) c)
      ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run))) :
    (Deserialize.deserialize r : pSpec.Challenge gq.1)
      = c (replayKey (Salt := Salt) gq msgs) := by
  have hshape : simulateQ (fsTableAuxImpl (U := U) c)
      ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run)
      = (simulateQ (fsTableAuxImpl (U := U) c)
          (uniformDeserializePreimage (pSpec := pSpec) (U := U)
            (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec)
            (c (replayKey (Salt := Salt) gq msgs)))) >>= fun v => pure (some v) := by
    unfold d2sCodecBridgeImpl
    simp only [hparse]
    simp only [OptionT.run_bind, OptionT.run_lift, pure_bind, Option.elimM, Option.elim,
      simulateQ_bind, simulateQ_map, bind_pure_comp]
    rfl
  rw [hshape] at hr
  obtain ⟨v, hv, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  replace hr : some r ∈ support ((pure (some v) : OracleComp ((Unit →ₒ U) + unifSpec)
      (Option (Vector U (challengeSize (pSpec := pSpec) gq.1))))) := hr
  simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
  subst hr
  exact deserialize_of_mem_support_simulateQ_uniformDeserializePreimage _ _ _ hv

/-- Coherence of a `tr_i` memo with a fixed FS table `c` (the run invariant of CO25
Claim 5.24): every binding the memo holds deserializes to the table value at its replayed
key. The empty memo is vacuously coherent; `memoCoherentTable_keystone` shows the memoized
bridge preserves coherence while serving only coherent responses. -/
def MemoCoherentTable (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) : Prop :=
  ∀ (i : pSpec.ChallengeIdx) (x : StmtIn) (s : Salt)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (r : Vector U (challengeSize (pSpec := pSpec) i))
    (msgs : pSpec.MessagesUpTo i.1.castSucc),
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo i x s em = some r →
    hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) i em = some msgs →
    (Deserialize.deserialize r : pSpec.Challenge i) = c ⟨i, ((x, s), msgs)⟩

/-- The empty memo is coherent with any table. -/
lemma memoCoherentTable_nil (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)) :
    MemoCoherentTable (U := U) (δ := δ) c [] := by
  unfold MemoCoherentTable
  intro i x s em r msgs hlook _
  simp [lookupD2SAlgoMemo] at hlook

/-- Coherence is preserved by inserting a binding whose response matches the table at its
replayed key. -/
lemma MemoCoherentTable.insert
    {c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec)}
    {memo : D2SAlgoMemo StmtIn U δ Salt pSpec}
    (hcoh : MemoCoherentTable (U := U) (δ := δ) c memo)
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (resp : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hresp : ∀ msgs : pSpec.MessagesUpTo gq.1.1.castSucc,
      hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs →
      (Deserialize.deserialize resp : pSpec.Challenge gq.1)
        = c (replayKey (Salt := Salt) gq msgs)) :
    MemoCoherentTable (U := U) (δ := δ) c
      (insertD2SAlgoMemo memo (bridgeMemoEntry (Salt := Salt) gq resp)) := by
  unfold MemoCoherentTable
  intro i x s em r msgs hlook hparse
  cases hm : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo i x s em with
  | some r₀ =>
      have := lookupD2SAlgoMemo_append_of_some memo
        [bridgeMemoEntry (Salt := Salt) gq resp] i x s em r₀ hm
      rw [show insertD2SAlgoMemo memo (bridgeMemoEntry (Salt := Salt) gq resp)
          = memo ++ [bridgeMemoEntry (Salt := Salt) gq resp] from rfl, this] at hlook
      cases Option.some.inj hlook
      exact hcoh i x s em r msgs hm hparse
  | none =>
      rw [show insertD2SAlgoMemo memo (bridgeMemoEntry (Salt := Salt) gq resp)
          = memo ++ [bridgeMemoEntry (Salt := Salt) gq resp] from rfl,
        lookupD2SAlgoMemo_append_of_none memo _ i x s em hm] at hlook
      obtain ⟨hR, hx, hs, hem, hr⟩ := lookupD2SAlgoMemo_singleton_some_inv hlook
      -- The matched entry is the freshly inserted one: transport the key equalities.
      subst hR
      subst hx
      subst hs
      obtain rfl := eq_of_heq hem
      obtain rfl := eq_of_heq hr
      exact hresp msgs hparse

/-- **The verifier-replay keystone** (CO25 Claim 5.24, deterministic layer): against a fixed
eager FS table `c` and a `c`-coherent `tr_i` memo, every response the memoized Eq. 16 bridge
serves deserializes to the table value at the replayed basic-FS key, and the output memo is
again `c`-coherent. By induction over a run started from the empty memo
(`memoCoherentTable_nil`), **every** challenge the simulated prover ever absorbed via the
`gᵢ` path matches the challenge the `Hyb₄` basic-FS verifier re-derives at the same key —
the re-derived transcript coincides with the simulator's committed transcript. -/
theorem memoCoherentTable_keystone
    (c : OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hcoh : MemoCoherentTable (U := U) (δ := δ) c memo)
    (msgs : pSpec.MessagesUpTo gq.1.1.castSucc)
    (hparse : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 = some msgs)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (memo' : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (h : some (r, memo') ∈ support (simulateQ (fsTableAuxImpl (U := U) c)
      (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run memo).run))) :
    (Deserialize.deserialize r : pSpec.Challenge gq.1)
      = c (replayKey (Salt := Salt) gq msgs)
    ∧ MemoCoherentTable (U := U) (δ := δ) c memo' := by
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r₀ =>
      rw [d2sCodecBridgeImplMemo_run_hit gq memo r₀ hl] at h
      replace h : some (r, memo') ∈ support
          ((pure (some (r₀, memo)) : OracleComp ((Unit →ₒ U) + unifSpec)
            (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
              × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hr, hm⟩ := h
      subst hr; subst hm
      exact ⟨hcoh gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
        r msgs hl hparse, hcoh⟩
  | none =>
      rw [d2sCodecBridgeImplMemo_run_miss gq memo hl, simulateQ_bind] at h
      obtain ⟨o, ho, h⟩ := (mem_support_bind_iff _ _ _).mp h
      match o with
      | none =>
          replace h : some (r, memo') ∈ support
              ((pure none : OracleComp ((Unit →ₒ U) + unifSpec)
                (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
                  × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
          simp at h
      | some resp =>
          replace h : some (r, memo') ∈ support
              ((pure (some (resp, insertD2SAlgoMemo memo
                  (bridgeMemoEntry (Salt := Salt) gq resp)))
                : OracleComp ((Unit →ₒ U) + unifSpec)
                  (Option (Vector U (challengeSize (pSpec := pSpec) gq.1)
                    × D2SAlgoMemo StmtIn U δ Salt pSpec)))) := h
          simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨hr, hm⟩ := h
          subst hr; subst hm
          have hfresh := deserialize_of_mem_support_bridge_table c gq msgs hparse r ho
          refine ⟨hfresh, hcoh.insert gq r fun msgs' hparse' => ?_⟩
          rw [hparse'] at hparse
          cases Option.some.inj hparse
          exact hfresh

end TableCoupling

/-! ## The CO25 Eq. 55 split: the hit-only verifier bridge and the strict hybrid

The remaining (probabilistic) content of Claim 5.24 is the divergence analysis: with what
probability does the `Hyb₃` verifier's `D2SQuery` run leave the pure replay path? The
definitions below instrument exactly that event, and `hyb34Step_of_strictSplit` (proven)
assembles any pair of coupling bounds across the instrumented hybrid into the full
`Hyb34StepResidual`. -/

section StrictSplit

variable [SaltCodec U δ Salt]

/-- The **hit-only** eager bridge: identical to `d2sCodecBridgeImplMemoEager` on `tr_i` memo
hits, but **aborts** on any miss. Running the `Hyb₃` verifier against this bridge (with the
prover's memo) realizes CO25's good event "the verifier re-derives only committed keys"; the
probability that it diverges from the real bridge is the Claim 5.24 bad-event mass. -/
noncomputable def d2sCodecBridgeImplMemoEagerHitOnly :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle StmtIn pSpec) (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun gq => do
    let memo ← get
    match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
    | some r => pure r
    | none => StateT.lift failure

/-- On a memo hit the hit-only bridge is pure (twin of
`d2sCodecBridgeImplMemoEager_run_hit`). -/
lemma d2sCodecBridgeImplMemoEagerHitOnly_run_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = pure (some (r, memo)) := by
  unfold d2sCodecBridgeImplMemoEagerHitOnly
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  rfl

/-- On a memo miss the hit-only bridge aborts. -/
lemma d2sCodecBridgeImplMemoEagerHitOnly_run_miss
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = none) :
    ((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = pure none := by
  unfold d2sCodecBridgeImplMemoEagerHitOnly
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl, StateT.run_lift]
  simp

/-- The hit-only bridge agrees with the real eager bridge on every memo hit — the two `Hyb₃`
verifier runs are identical until the first fresh verifier-side `gᵢ` key (identical-until-bad
for the Eq. 55 split). -/
theorem d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemoEagerHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = ((d2sCodecBridgeImplMemoEager (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run := by
  rw [d2sCodecBridgeImplMemoEagerHitOnly_run_hit gq memo r hl,
    d2sCodecBridgeImplMemoEager_run_hit gq memo r hl]

/-- The **hit-only** salted bridge: identical to `d2sCodecBridgeImplMemo` on `tr_i` memo
hits, but **aborts** on any miss. This is the salted-surface twin of
`d2sCodecBridgeImplMemoEagerHitOnly`, matching the repaired `Hyb₃` (salted `fᵢ` table, salt
erased only in the line-4 log projection). It never queries the external oracle. -/
noncomputable def d2sCodecBridgeImplMemoHitOnly :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (fsChallengeOracle (StmtIn × Salt) pSpec) (D2SAlgoMemo StmtIn U δ Salt pSpec) :=
  fun gq => do
    let memo ← get
    match lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
        (pSpec := pSpec) memo gq.1 gq.2.1
        (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
    | some r => pure r
    | none => StateT.lift failure

/-- On a memo hit the salted hit-only bridge is pure (twin of
`d2sCodecBridgeImplMemoEagerHitOnly_run_hit`). -/
lemma d2sCodecBridgeImplMemoHitOnly_run_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = pure (some (r, memo)) := by
  unfold d2sCodecBridgeImplMemoHitOnly
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl]
  rfl

/-- On a memo miss the salted hit-only bridge aborts. -/
lemma d2sCodecBridgeImplMemoHitOnly_run_miss
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = none) :
    ((d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = pure none := by
  unfold d2sCodecBridgeImplMemoHitOnly
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hl, StateT.run_lift]
  simp

/-- The salted hit-only bridge agrees with the real salted bridge on every memo hit —
identical-until-bad for the Eq. 55 split on the repaired `Hyb₃` surface. -/
theorem d2sCodecBridgeImplMemoHitOnly_run_eq_of_hit
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (r : Vector U (challengeSize (pSpec := pSpec) gq.1))
    (hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo gq.1 gq.2.1 (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2
      = some r) :
    ((d2sCodecBridgeImplMemoHitOnly (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
        (δ := δ) (Salt := Salt) gq).run memo).run
      = ((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec)
          (δ := δ) (Salt := Salt) gq).run memo).run := by
  rw [d2sCodecBridgeImplMemoHitOnly_run_hit gq memo r hl,
    d2sCodecBridgeImplMemo_run_hit gq memo r hl]

end StrictSplit

/-! ## The split skeleton and the strict hybrid -/

section SplitSkeleton

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 Figure 4 lines 2–4 with **separate** prover/verifier `gᵢ` realizations sharing the
`tr_i` memo (D2SAlgo Item 3). Specializing both to the same realization recovers
`KeyLemmaHybrids.hybGameEager` (`hybGameEagerSplit_diag`); specializing the verifier side to
the hit-only bridge yields the instrumented `Hyb3Strict`. -/
noncomputable def hybGameEagerSplit [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImplP gImplV : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) := do
  let c ← Dχ.sample
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let impl : QueryImpl (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec) ProbComp :=
    oImpl + (Dχ.toImpl c + (d2sUnitSampleImpl (U := U) + coins))
  let ⟨pRes?, pLogRaw⟩ ←
    simulateQ impl
      ((simulateQ loggingOracle
        ((d2fRaw (T_H := T_H) (T_P := T_P) gImplP P default).run)).run)
  match pRes? with
  | none => pure none
  | some ⟨⟨⟨stmtIn, messages⟩, _⟩, memo⟩ => do
      let ⟨vRes?, vLogRaw⟩ ←
        simulateQ impl
          ((simulateQ loggingOracle
            ((d2fRaw (T_H := T_H) (T_P := T_P) gImplV
              ((V.duplexSpongeFiatShamir.run
                stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run)
              memo).run)).run)
      match vRes? with
      | none => pure none
      | some ⟨⟨stmtOut?, _⟩, _⟩ =>
          match stmtOut? with
          | none => pure none
          | some stmtOut => do
              let pLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) pLogRaw)).run)
              let vLog'? ←
                simulateQ (d2sUnitSampleImpl (U := U))
                  ((lineFour (projectChallengePlusUnitQueryLog (U := U) vLogRaw)).run)
              match pLog'?, vLog'? with
              | some pLog', some vLog' =>
                  pure (some ⟨stmtIn, stmtOut, messages, pLog', vLog'⟩)
              | _, _ => pure none

/-- Diagonal identification: the split skeleton with equal prover/verifier realizations is
the `KeyLemmaHybrids` skeleton. -/
lemma hybGameEagerSplit_diag [SampleableType U]
    {κ : Type} {challengeSpec : OracleSpec κ} {M : Type} [Inhabited M] (δ : ℕ)
    (Dχ : OracleDistribution challengeSpec)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (lineFour : QueryLog (oSpec + challengeSpec) →
      UnitSampleM U (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ Dχ gImpl gImpl lineFour oImpl V P
      = hybGameEager (T_H := T_H) (T_P := T_P) δ Dχ gImpl lineFour oImpl V P := rfl

variable [SaltCodec U δ Salt]

/-- `Hyb₃` with the **hit-only** verifier bridge: the prover runs against the real eager
Eq. 16 bridge; the verifier replays against the *committed memo only*, aborting on any fresh
`gᵢ` key. `Δ(Hyb₃, Hyb3Strict)` is exactly the CO25 Claim 5.24 bad-event mass (the verifier
leaves the replay path); `Δ(Hyb3Strict, Hyb₄)` is the pure-replay collapse. -/
noncomputable def Hyb3Strict [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    SPMF (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) :=
  𝒟[hybGameEagerSplit (T_H := T_H) (T_P := T_P) δ
      (OracleDistribution.uniform (fsChallengeOracle (StmtIn × Salt) pSpec))
      (d2sCodecBridgeImplMemo (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (d2sCodecBridgeImplMemoHitOnly (StmtIn := StmtIn) (δ := δ) (Salt := Salt))
      (hyb3Line4SaltErase Salt) oImpl V P]

end SplitSkeleton

/-! ## Assembly: any strict-split coupling pair discharges the Claim 5.24 step -/

section Assembly

/-- **CO25 Eq. 55 proof skeleton (proven)**: if the `Hyb₃`-to-strict divergence (the
bad-event mass `εA`: the verifier's `D2SQuery` run makes a fresh `gᵢ` query or aborts off
the replay path) and the strict-to-`Hyb₄` collapse cost (`εB`: pure replay equals the
basic-FS verifier, on the hit path) sum to at most `claim5_24Bound`, then the full
`Hyb34StepResidual` holds. The two hypotheses are the genuinely open probabilistic core of
Claim 5.24 (they require the §5.6 trace analysis applied to the verifier's replayed trace);
the deterministic bricks of this module are the toolkit for `hB`. -/
theorem hyb34Step_of_strictSplit [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (εA εB : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hA : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
          (Hyb3Strict T_H T_P δ Salt oImpl V P)
        ≤ εA tₕ tₚ tₚᵢ L)
    (hB : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (Hyb3Strict T_H T_P δ Salt oImpl V P)
          (Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
        ≤ εB tₕ tₚ tₚᵢ L)
    (hsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      εA tₕ tₚ tₚᵢ L + εB tₕ tₚ tₚᵢ L ≤ claim5_24Bound U tₕ tₚ tₚᵢ L) :
    Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl := by
  intro V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have h1 := hA V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have h2 := hB V P tₕ tₚ tₚᵢ L hL hHash hPerm hPermInv
  have htri := SPMF.tvDist_triangle (Hyb3 T_H T_P δ Salt oImpl V P)
    (Hyb3Strict T_H T_P δ Salt oImpl V P)
    (Hyb4 oImpl V
      (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
  have hs := hsum tₕ tₚ tₚᵢ L
  linarith

end Assembly

#print axioms DuplexSpongeFS.VerifierReplay.support_simulateQ_subset
#print axioms DuplexSpongeFS.VerifierReplay.lookupD2SAlgoMemo_append_of_some
#print axioms DuplexSpongeFS.VerifierReplay.lookupD2SAlgoMemo_append_of_none
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemo_run_hit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemo_run_miss
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemo_commit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemo_replay
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemo_preserves_lookup
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEager_run_eq
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEager_run_hit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEager_commit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEager_replay
#print axioms DuplexSpongeFS.VerifierReplay.deserialize_of_mem_support_uniformDeserializePreimage
#print axioms DuplexSpongeFS.VerifierReplay.uniform_toImpl_apply
#print axioms DuplexSpongeFS.VerifierReplay.deserialize_of_mem_support_bridge_table
#print axioms DuplexSpongeFS.VerifierReplay.memoCoherentTable_nil
#print axioms DuplexSpongeFS.VerifierReplay.MemoCoherentTable.insert
#print axioms DuplexSpongeFS.VerifierReplay.memoCoherentTable_keystone
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEagerHitOnly_run_hit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEagerHitOnly_run_miss
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoEagerHitOnly_run_eq_of_hit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoHitOnly_run_hit
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoHitOnly_run_miss
#print axioms DuplexSpongeFS.VerifierReplay.d2sCodecBridgeImplMemoHitOnly_run_eq_of_hit
#print axioms DuplexSpongeFS.VerifierReplay.hybGameEagerSplit_diag
#print axioms DuplexSpongeFS.VerifierReplay.hyb34Step_of_strictSplit

end DuplexSpongeFS.VerifierReplay

end
