/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKCoupling

/-!
# Lazy caching Fiat-Shamir challenge impl + prover-run message coupling (#116)

This develops the *lazy caching* Fiat-Shamir challenge implementation and proves that the
prover-run message distribution it induces equals the one induced by the canonical *uniform*
implementation `fsChallengeUniformImpl`.  Composed with the already-proven `coupling_run`
(uniform FS messages = interactive messages), this yields the lazy FS prover-run message
coupling needed for PR #272 (Path A).

Key mathematical content: during `runToRoundFS`, the prover queries the FS oracle at keys whose
challenge-round index `q.1.1 : Fin n` is *exactly* the current round.  Hence, threading a cache
that only ever holds keys of strictly smaller round index, every prover query is a cache **miss**
→ a fresh uniform draw → identical to `fsChallengeUniformImpl`.  We capture this with the cache
invariant `CacheBelow j` ("every cached key has round index `< j`"), preserved round-to-round, and
run a `Fin.induction` mirroring `coupling_run`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]

/-- The lazy caching Fiat-Shamir challenge implementation: on a cache miss, draw a fresh uniform
challenge and store it; on a hit, replay the stored value. This is `srChallengeQueryImpl.withCaching`
specialized to the FS oracle. -/
@[reducible, inline]
def fsChallengeLazyImpl :
    QueryImpl (fsChallengeOracle StmtIn pSpec)
      (StateT (QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp) :=
  (srChallengeQueryImpl (Statement := StmtIn) (pSpec := pSpec)).withCaching

/-- Cache-MISS query atom: under the lazy impl, a query at an uncached key draws a fresh uniform
challenge (mirroring `fsChallengeUniformImpl`) and stores it. -/
theorem fsChallengeLazy_run_miss
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) (hmiss : cache q = none) :
    StateT.run (fsChallengeLazyImpl (StmtIn := StmtIn) (pSpec := pSpec) q) cache
      = (fun c => (c, cache.cacheQuery q c)) <$> ($ᵗ (pSpec.Challenge q.1)) := by
  unfold fsChallengeLazyImpl
  exact QueryImpl.withCaching_run_none _ hmiss

/-- Cache-HIT query atom: under the lazy impl, a query at a cached key replays the stored value and
leaves the cache unchanged. -/
theorem fsChallengeLazy_run_hit
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (u : (fsChallengeOracle StmtIn pSpec).Range q) (hhit : cache q = some u) :
    StateT.run (fsChallengeLazyImpl (StmtIn := StmtIn) (pSpec := pSpec) q) cache
      = pure (u, cache) := by
  unfold fsChallengeLazyImpl
  exact QueryImpl.withCaching_run_some _ hhit

/-! ## The combined product-state implementations

We thread a product state `σ × QueryCache`.  The ambient oracle handler acts on `σ` (leaving the
cache untouched); the FS handler acts on the cache (uniform: ignoring it; lazy: caching).  Both
combined handlers live in `StateT (σ × QueryCache) ProbComp`, so we can take their `+`. -/

/-- Ambient handler lifted to the product state (acts on `σ`, leaves the cache untouched). -/
@[reducible, inline]
def ambientProd (pSpec : ProtocolSpec n) [∀ i, DecidableEq (pSpec.Message i)]
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    QueryImpl oSpec (StateT (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp) :=
  QueryImpl.extendState (Q := QueryCache (fsChallengeOracle StmtIn pSpec)) impl
    (fun _ _ _ _ c => c)

/-- Uniform FS handler over the product state (ignores both components). -/
@[reducible, inline]
def fsUniformProd (pSpec : ProtocolSpec n) [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, DecidableEq (pSpec.Message i)] :
    QueryImpl (fsChallengeOracle StmtIn pSpec)
      (StateT (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp) :=
  fsChallengeUniformImpl (σ := σ × QueryCache (fsChallengeOracle StmtIn pSpec))

/-- Lazy FS handler over the product state (acts on the cache component). -/
@[reducible, inline]
def fsLazyProd (pSpec : ProtocolSpec n) [∀ i, SampleableType (pSpec.Challenge i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Message i)] :
    QueryImpl (fsChallengeOracle StmtIn pSpec)
      (StateT (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp) :=
  QueryImpl.extendStateLeft (Q := σ) (fsChallengeLazyImpl (StmtIn := StmtIn) (pSpec := pSpec))
    (fun _ _ _ _ s => s)

/-- A combined query under `fsLazyProd` at the FS oracle, on a cache MISS, draws a fresh uniform
challenge and stores it; the ambient `σ` component is untouched. The lazy-product analogue of
`simulateQ_addLift_fsChallengeUniform_query_run`. -/
theorem simulateQ_lazyProd_query_run_miss
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (s : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) (hmiss : cache q = none) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (query (spec := fsChallengeOracle StmtIn pSpec) q :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q))) (s, cache)
      = (fun c => (c, s, cache.cacheQuery q c)) <$> ($ᵗ (pSpec.Challenge q.1)) := by
  rw [show (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))
      = liftM (liftM (OracleSpec.query q) :
          OracleQuery (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q)) from rfl,
    simulateQ_query]
  show (_ <$> (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ)
      pSpec) (Sum.inr q)).run (s, cache) = _
  rw [QueryImpl.add_apply_inr, StateT.run_map]
  show (fun p => ((id : (fsChallengeOracle StmtIn pSpec).Range q → _) p.1, p.2)) <$>
      (fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec q).run (s, cache) = _
  rw [show (fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec q).run (s, cache)
      = ((fsChallengeLazyImpl (StmtIn := StmtIn) (pSpec := pSpec) q).run cache >>=
        fun p => pure (p.1, (s, p.2))) from rfl]
  simp only [fsChallengeLazy_run_miss q cache hmiss, map_bind, _root_.map_pure, bind_pure_comp,
    Function.comp, Functor.map_map, id_eq]

/-- The uniform-product FS query atom: a fresh uniform draw, leaving both state components
untouched (the uniform impl ignores its whole state). Unconditional analogue of
`simulateQ_lazyProd_query_run_miss`. -/
theorem simulateQ_uniformProd_query_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (s : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (query (spec := fsChallengeOracle StmtIn pSpec) q :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q))) (s, cache)
      = (fun c => (c, s, cache)) <$> ($ᵗ (pSpec.Challenge q.1)) := by
  rw [show (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))
      = liftM (liftM (OracleSpec.query q) :
          OracleQuery (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q)) from rfl,
    simulateQ_query]
  show (_ <$> (ambientProd (StmtIn := StmtIn) pSpec impl
      + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec) (Sum.inr q)).run (s, cache) = _
  rw [QueryImpl.add_apply_inr, StateT.run_map]
  show (fun p => ((id : (fsChallengeOracle StmtIn pSpec).Range q → _) p.1, p.2)) <$>
      (fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec q).run (s, cache) = _
  rw [show (fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec q).run (s, cache)
      = (fun c => (c, (s, cache))) <$> ($ᵗ (pSpec.Challenge q.1)) from rfl]
  simp only [Functor.map_map, Function.comp, id_eq, Prod.mk.eta, id_map']

/-! ## The cache invariant: only round indices `< j` are cached -/

/-- A cache satisfies `CacheBelow j` if every cached FS key has challenge-round index `< j`. -/
def CacheBelow (j : Fin (n + 1)) (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) : Prop :=
  ∀ q, cache q ≠ none → (q.1.1 : ℕ) < j.val

/-- The empty cache satisfies `CacheBelow` for any bound. -/
theorem cacheBelow_empty (j : Fin (n + 1)) :
    CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j (∅ : QueryCache _) := by
  intro q hq; simp at hq

/-- `CacheBelow` is monotone in the bound. -/
theorem CacheBelow.mono {j k : Fin (n + 1)} (hjk : j.val ≤ k.val)
    {cache : QueryCache (fsChallengeOracle StmtIn pSpec)}
    (h : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j cache) :
    CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) k cache :=
  fun q hq => lt_of_lt_of_le (h q hq) hjk

/-- The key the prover queries at round `j` (a V_to_P round) is NOT cached when the cache only
holds round indices `< j` (since this key's round index is exactly `j`). -/
theorem cacheBelow_miss_at_round (j : Fin n) (hDir : pSpec.dir j = Direction.V_to_P)
    (stmt : StmtIn) (messages : pSpec.MessagesUpTo j.castSucc)
    {cache : QueryCache (fsChallengeOracle StmtIn pSpec)}
    (h : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j.castSucc cache) :
    cache ⟨⟨j, hDir⟩, ⟨stmt, messages⟩⟩ = none := by
  by_contra hne
  have := h ⟨⟨j, hDir⟩, ⟨stmt, messages⟩⟩ hne
  simp only [Fin.coe_castSucc] at this
  exact absurd this (lt_irrefl _)

/-- The ambient-product handler `ambientProd impl` leaves the cache component invariant: every
output of any ambient query started from cache `c₀` carries cache `c₀`. -/
theorem ambientProd_cache_inv (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : oSpec.Domain) (s : σ) (c₀ : QueryCache (fsChallengeOracle StmtIn pSpec))
    (x : _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hx : x ∈ support ((ambientProd (StmtIn := StmtIn) pSpec impl t).run (s, c₀))) :
    x.2.2 = c₀ := by
  simp only [ambientProd, QueryImpl.extendState_apply] at hx
  rw [support_bind] at hx
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨p, _, hp⟩ := hx
  rw [hp]

/-- Running an ambient (`oSpec`) computation under `ambientProd impl` from `(s, c₀)` threads the
cache `c₀` unchanged: the result is the plain `impl`-run on `s`, re-paired with `c₀`. -/
theorem simulateQ_ambientProd_run (impl : QueryImpl oSpec (StateT σ ProbComp))
    {β : Type} (oa : OracleComp oSpec β) (s : σ)
    (c₀ : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    (simulateQ (ambientProd (StmtIn := StmtIn) pSpec impl) oa).run (s, c₀)
      = (fun p => (p.1, (p.2, c₀))) <$> (simulateQ impl oa).run s := by
  have h := OracleComp.simulateQ_run_eq_of_snd_invariant
    (impl := ambientProd (StmtIn := StmtIn) pSpec impl) (q₀ := c₀)
    (fun t s x hx => ambientProd_cache_inv impl t s c₀ x hx) oa s
  rw [h]
  have hfix : QueryImpl.fixSndStateT (ambientProd (StmtIn := StmtIn) pSpec impl) c₀ = impl := by
    funext t
    apply StateT.ext
    intro s'
    show Prod.map id Prod.fst <$>
        ((impl t).run s' >>= fun p => pure (p.1, (p.2, c₀))) = (impl t).run s'
    rw [map_bind]
    conv_rhs => rw [← bind_pure ((impl t).run s')]
    refine bind_congr fun ⟨u, s''⟩ => ?_
    simp [Prod.map]
  rw [hfix]

variable (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- **Per-round lazy↔uniform step.** Running one Fiat-Shamir round `processRoundFS j` under the
lazy-product impl, starting from a cache that misses the round-`j` key, projects (to messages,
prover state, and the ambient `σ`, dropping the cache) to the SAME distribution as running it under
the uniform-product impl. Both reduce to the identical fresh `$ᵗ` draw on the round-`j` challenge;
the cache is irrelevant after projection. -/
theorem processRoundFS_lazy_uniform_step
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (j : Fin n)
    (m : pSpec.MessagesUpTo j.castSucc) (st : P.PrvState j.castSucc)
    (σ' : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (hmiss : ∀ (hDir : pSpec.dir j = Direction.V_to_P),
      cache ⟨⟨j, hDir⟩, ⟨stmt, m⟩⟩ = none) :
    (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.processRoundFS j (pure (m, stmt, st)))) (σ', cache))
      = (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.processRoundFS j (pure (m, stmt, st)))) (σ', cache)) := by
  simp only [Prover.processRoundFS, pure_bind]
  split
  · rename_i hDir
    -- V_to_P: the ambient `receiveChallenge` is handled identically (by `ambientProd impl`) on
    -- both sides via `simulateQ_ambientProd_run` (which re-pairs the *same* cache `cache`); the FS
    -- challenge `query` then reduces to the same fresh `$ᵗ` draw (lazy via the miss atom, uniform
    -- unconditionally).
    -- Reduce the OracleComp-level run on BOTH sides to a common shape.
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, bind_map_left, Function.comp,
      evalDist_map, evalDist_bind, map_bind]
    refine bind_congr fun a => ?_
    rw [simulateQ_lazyProd_query_run_miss impl _ a.2 cache (hmiss hDir),
      simulateQ_uniformProd_query_run impl _ a.2 cache]
    simp only [simulateQ_pure, StateT.run_pure]
    -- Push `evalDist` through the FS draw on both sides; `erw` handles the proof-in-index
    -- (`⟨j, hDir⟩`) mismatch between the lazy and uniform `$ᵗ` arguments.
    erw [evalDist_map, evalDist_map]
    simp only [evalDist_pure, bind_map_left, _root_.map_pure, Function.comp]
    refine bind_congr fun c => ?_
    rw [LawfulApplicative.map_pure, LawfulApplicative.map_pure]
  · rename_i hDir
    -- P_to_V: no FS query; both runs are the identical ambient `sendMessage`.
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_pure, StateT.run_pure, Function.comp]

/-- The cache grows by at most the round-`j` key (a V_to_P key of round index `j`) after a lazy
round `processRoundFS j`: from `CacheBelow j.castSucc`, every output cache satisfies
`CacheBelow j.succ`. -/
theorem processRoundFS_lazy_cacheBelow (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (j : Fin n)
    (m : pSpec.MessagesUpTo j.castSucc) (st : P.PrvState j.castSucc)
    (σ' : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (hcache : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j.castSucc cache)
    (z : _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hz : z ∈ support (StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (P.processRoundFS j (pure (m, stmt, st)))) (σ', cache))) :
    CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j.succ z.2.2 := by
  -- It suffices that the output cache `z.2.2` is `≤ cache.cacheQuery (round-j key) _` (V_to_P) or
  -- `= cache` (P_to_V); in both cases every cached index is `< j + 1`.
  have hjj : (j.castSucc : Fin (n + 1)).val ≤ (j.succ : Fin (n + 1)).val := by
    simp [Fin.coe_castSucc, Fin.val_succ]
  revert hz
  simp only [Prover.processRoundFS, pure_bind]
  split
  · rename_i hDir
    -- V_to_P
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_pure, StateT.run_pure,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image]
    rintro ⟨i, ⟨x, _, rfl⟩, i_1, hi1, hzp⟩
    rw [simulateQ_lazyProd_query_run_miss impl ⟨⟨j, hDir⟩, (stmt, m)⟩ x.2 cache
        (cacheBelow_miss_at_round j hDir stmt m hcache)] at hi1
    simp only [support_map, Set.mem_image] at hi1
    obtain ⟨c, _, rfl⟩ := hi1
    simp only [support_pure, Set.mem_singleton_iff] at hzp
    subst hzp
    -- output cache = `cache.cacheQuery (round-j key) c`; its indices are `< j` (from `hcache`) or `j`.
    simp only [CacheBelow]
    intro q hq
    by_cases hqk : q = ⟨⟨j, hDir⟩, (stmt, m)⟩
    · subst hqk; simp [Fin.val_succ]
    · rw [QueryCache.cacheQuery_of_ne _ _ hqk] at hq
      exact lt_of_lt_of_le (hcache q hq) hjj
  · rename_i hDir
    -- P_to_V: cache unchanged.
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_pure, StateT.run_pure,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image]
    rintro ⟨i, ⟨x, _, rfl⟩, hzp⟩
    simp only [support_pure, Set.mem_singleton_iff] at hzp
    subst hzp
    exact hcache.mono hjj

/-- **Run-level cache invariant.** Every output cache of the lazy-product `runToRoundFS j` run
(started from a cache with `CacheBelow 0`, e.g. `∅`) satisfies `CacheBelow j`. -/
theorem runToRoundFS_lazy_cacheBelow (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (wit : WitIn) (j : Fin (n + 1))
    (cache₀ : QueryCache (fsChallengeOracle StmtIn pSpec)) (σ' : σ)
    (hcache₀ : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) 0 cache₀)
    (z : _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hz : z ∈ support (StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (P.runToRoundFS j stmt (P.input (stmt, wit)))) (σ', cache₀))) :
    CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j z.2.2 := by
  induction j using Fin.induction with
  | zero =>
    simp only [Prover.runToRoundFS, Fin.induction_zero, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hcache₀
  | succ j ih =>
    rw [runToRoundFS_succ] at hz
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hpre := ih w hw
    -- the carried `stmtIn` in the prover tuple equals the run's `stmt`.
    refine processRoundFS_lazy_cacheBelow P impl w.1.2.1 j w.1.1 w.1.2.2 w.2.1 w.2.2 hpre z ?_
    simpa using hz

/-- In the support of any (product-state, combined-impl) `runToRoundFS j` run, the prover tuple's
carried `stmtIn` equals the run's input `stmt` (it is threaded unchanged by `processRoundFS`).
Stated generically over the FS handler so it applies to both the lazy and uniform impls. -/
theorem runToRoundFS_stmt_inv {τ : Type}
    (fsImpl : QueryImpl (fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (ambImpl : QueryImpl oSpec (StateT τ ProbComp))
    (stmt : StmtIn) (st0 : P.PrvState 0) (j : Fin (n + 1)) (s0 : τ) (z : _ × τ)
    (hz : z ∈ support (StateT.run (simulateQ (ambImpl + fsImpl)
      (P.runToRoundFS j stmt st0)) s0)) :
    z.1.2.1 = stmt := by
  induction j using Fin.induction generalizing s0 with
  | zero =>
    simp only [Prover.runToRoundFS, Fin.induction_zero, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl
  | succ j ih =>
    have hsucc : P.runToRoundFS j.succ stmt st0
        = P.runToRoundFS j.castSucc stmt st0 >>= fun r => P.processRoundFS j (pure r) := by
      conv_lhs => rw [Prover.runToRoundFS, Fin.induction_succ]
      rw [Prover.processRoundFS]
      simp only [bind_pure_comp, Prover.runToRoundFS, map_eq_bind_pure_comp, bind_assoc]
      rfl
    rw [hsucc] at hz
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hwst : w.1.2.1 = stmt := ih s0 w hw
    revert hz
    simp only [Prover.processRoundFS, pure_bind]
    split <;> rename_i hDir <;>
      simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, support_bind,
        support_map, Set.mem_iUnion, Set.mem_image, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff]
    · rintro ⟨i, _, i_1, _, hzz⟩
      subst hzz; simpa using hwst
    · rintro ⟨i, _, hzz⟩
      subst hzz; simpa using hwst

/-- Support-restricted `bind_congr` for `SPMF` (= `OptionT PMF`): two continuations that agree on
the support of `p` give equal binds. -/
theorem SPMF.bind_congr_of_support {α β : Type} (p : SPMF α) (f g : α → SPMF β)
    (h : ∀ x ∈ p.support, f x = g x) : p >>= f = p >>= g := by
  refine SPMF.ext fun y => ?_
  have := probOutput_bind_congr (m := SPMF) (mx := p) (ob₁ := f) (ob₂ := g) (y := y)
    (fun x hx => by rw [h x hx])
  simpa [probOutput] using this

/-- The uniform-product round's projection is independent of the carried cache (the uniform handler
ignores the whole product state's cache component). -/
theorem processRoundFS_uniform_cache_irrelevant (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (j : Fin n) (m : pSpec.MessagesUpTo j.castSucc) (st : P.PrvState j.castSucc)
    (σ' : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) :
    (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.processRoundFS j (pure (m, stmt, st)))) (σ', cache))
      = (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.processRoundFS j (pure (m, stmt, st)))) (σ', ∅)) := by
  simp only [Prover.processRoundFS, pure_bind]
  split
  · rename_i hDir
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_ambientProd_run impl _ σ' ∅,
      bind_map_left, Function.comp, evalDist_map, evalDist_bind, map_bind]
    refine bind_congr fun a => ?_
    rw [simulateQ_uniformProd_query_run impl _ a.2 cache,
      simulateQ_uniformProd_query_run impl _ a.2 ∅]
    simp only [simulateQ_pure, StateT.run_pure]
    erw [evalDist_map, evalDist_map]
    simp only [evalDist_pure, bind_map_left, _root_.map_pure, Function.comp]
    refine bind_congr fun c => ?_
    rw [LawfulApplicative.map_pure, LawfulApplicative.map_pure]
  · rename_i hDir
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, map_bind,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_ambientProd_run impl _ σ' ∅,
      simulateQ_pure, StateT.run_pure, Function.comp, evalDist_map, evalDist_bind, evalDist_pure,
      map_bind, _root_.map_pure, bind_map_left]
    refine bind_congr fun a => ?_
    rw [LawfulApplicative.map_pure, LawfulApplicative.map_pure]

/-- **Run-level lazy↔uniform message coupling.** The lazy-product `runToRoundFS j` run, projected to
its messages, prover state, and ambient `σ` (dropping the cache), has the same `evalDist` as the
uniform-product run. By `Fin.induction` over rounds (mirroring `coupling_run`): the per-round step
`processRoundFS_lazy_uniform_step` reconciles each round, its cache-miss precondition supplied by the
run-level cache invariant `runToRoundFS_lazy_cacheBelow`. -/
theorem runToRoundFS_lazy_uniform_coupling (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (wit : WitIn) (j : Fin (n + 1)) (σ' : σ) :
    (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j stmt (P.input (stmt, wit)))) (σ', ∅))
      = (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j stmt (P.input (stmt, wit)))) (σ', ∅)) := by
  induction j using Fin.induction with
  | zero =>
    simp only [Prover.runToRoundFS, Fin.induction_zero, simulateQ_pure, StateT.run_pure,
      _root_.map_pure, evalDist_pure]
  | succ j ih =>
    -- Peel one round. The common per-round continuation `G` depends only on `(messages, prvState,
    -- σ)`; the lazy round (from a `CacheBelow j.castSucc` cache — always a miss) and the uniform
    -- round agree on it by `processRoundFS_lazy_uniform_step`, and the prefix runs agree by `ih`.
    simp only [runToRoundFS_succ, simulateQ_bind, StateT.run_bind, map_bind, evalDist_bind,
      evalDist_map, Function.comp]
    -- the round projection `ψ` (drop carried stmt + cache) and the common continuation `G`.
    set ψ : (pSpec.MessagesUpTo j.castSucc × StmtIn × P.PrvState j.castSucc)
        × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) →
        pSpec.MessagesUpTo j.castSucc × P.PrvState j.castSucc × σ :=
      fun r => (r.1.1, r.1.2.2, r.2.1) with hψ
    set G : pSpec.MessagesUpTo j.castSucc × P.PrvState j.castSucc × σ →
        SPMF (pSpec.MessagesUpTo j.succ × P.PrvState j.succ × σ) :=
      fun q => (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.processRoundFS j (pure (q.1, stmt, q.2.1)))) (q.2.2, ∅)) with hG
    have hmapbind : ∀ {β : Type} (p : SPMF ((pSpec.MessagesUpTo j.castSucc × StmtIn
          × P.PrvState j.castSucc) × (σ × QueryCache (fsChallengeOracle StmtIn pSpec))))
        (k : _ → SPMF β),
        (p >>= fun x => k (ψ x)) = (ψ <$> p) >>= k := by
      intro β p k
      rw [← bind_pure_comp, bind_assoc]; simp only [pure_bind]
    -- LHS continuation = `G ∘ ψ` on the lazy-prefix support.
    have hL : (evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅))) >>=
          (fun x => (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
            evalDist (StateT.run (simulateQ
                (ambientProd (StmtIn := StmtIn) pSpec impl
                  + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
              (P.processRoundFS j (pure x.1))) x.2))
        = (ψ <$> evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅))) >>= G := by
      rw [← hmapbind]
      refine SPMF.bind_congr_of_support _ _ _ (fun x hx => ?_)
      have hxoc : x ∈ support (StateT.run (simulateQ
          (ambientProd (StmtIn := StmtIn) pSpec impl
            + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅)) := by
        rw [← mem_support_evalDist_iff]; simpa using hx
      have hst : x.1.2.1 = stmt :=
        runToRoundFS_stmt_inv (P := P) (fsImpl := fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (ambImpl := ambientProd (StmtIn := StmtIn) pSpec impl) (stmt := stmt)
          (st0 := P.input (stmt, wit)) (j := j.castSucc) (s0 := (σ', ∅)) (z := x) (hz := hxoc)
      have hcb : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j.castSucc x.2.2 :=
        runToRoundFS_lazy_cacheBelow P impl stmt wit j.castSucc ∅ σ' (cacheBelow_empty 0) x hxoc
      rw [hG]
      have hstep := processRoundFS_lazy_uniform_step P impl stmt j x.1.1 x.1.2.2 x.2.1 x.2.2
        (fun hDir => cacheBelow_miss_at_round j hDir stmt x.1.1 hcb)
      have hci := processRoundFS_uniform_cache_irrelevant P impl stmt j x.1.1 x.1.2.2 x.2.1 x.2.2
      -- rewrite `x.1` as `(x.1.1, stmt, x.1.2.2)` using `hst`, then chain
      -- lazy@(σ,cache) = uniform@(σ,cache) [hstep] = uniform@(σ,∅) [hci].
      have hx1 : x.1 = (x.1.1, stmt, x.1.2.2) := by rw [← hst]
      rw [hx1, show x.2 = (x.2.1, x.2.2) from rfl]
      exact hstep.trans hci
    -- RHS continuation = `G ∘ ψ` on the uniform-prefix support.
    have hR : (evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅))) >>=
          (fun x => (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
            evalDist (StateT.run (simulateQ
                (ambientProd (StmtIn := StmtIn) pSpec impl
                  + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
              (P.processRoundFS j (pure x.1))) x.2))
        = (ψ <$> evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅))) >>= G := by
      rw [← hmapbind]
      refine SPMF.bind_congr_of_support _ _ _ (fun x hx => ?_)
      have hxoc : x ∈ support (StateT.run (simulateQ
          (ambientProd (StmtIn := StmtIn) pSpec impl
            + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j.castSucc stmt (P.input (stmt, wit)))) (σ', ∅)) := by
        rw [← mem_support_evalDist_iff]; simpa using hx
      have hst : x.1.2.1 = stmt :=
        runToRoundFS_stmt_inv (P := P) (fsImpl := fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (ambImpl := ambientProd (StmtIn := StmtIn) pSpec impl) (stmt := stmt)
          (st0 := P.input (stmt, wit)) (j := j.castSucc) (s0 := (σ', ∅)) (z := x) (hz := hxoc)
      rw [hG]
      have hx1 : x.1 = (x.1.1, stmt, x.1.2.2) := by rw [← hst]
      rw [hx1, show x.2 = (x.2.1, x.2.2) from rfl]
      -- the uniform round ignores the cache, so the carried cache `x.2.2` is irrelevant.
      rw [processRoundFS_uniform_cache_irrelevant P impl stmt j x.1.1 x.1.2.2 x.2.1 x.2.2]
    rw [hL, hR]
    exact congrArg (· >>= G) ih

/-- **The lazy FS prover-run message coupling (Path A, final deliverable).**

Running the Fiat-Shamir prover `runToRoundFS` up to any round under the *lazy caching* FS
implementation (ambient queries via `impl`, FS-challenge queries cached: fresh uniform draw on a
miss, replay on a hit), projected to its messages (and prover state and ambient `σ`, dropping the
cache), induces the SAME `evalDist` as running the interactive prover `runToRound` (verifier
challenges via `challengeQueryImpl`), projected to its messages.

This is the lazy-impl analogue of `coupling_run`, obtained by transferring it through
`runToRoundFS_lazy_uniform_coupling`: the prover's FS queries are at pairwise-distinct (round-indexed)
keys, hence all cache misses, so the lazy impl reproduces the fresh-draw behaviour of the canonical
uniform impl `fsChallengeUniformImpl` that `coupling_run` uses.

The interactive side is run under the cache-decorated ambient handler `ambientProd impl` over the
same product state `σ × QueryCache` (exactly the form `coupling_run` produces when instantiated at
`σ := σ × QueryCache`); the FS-cache `QueryCache` is a passive bookkeeping component there. Both
sides are projected to `(messages, prover state, ambient σ)`, dropping the cache. Axiom-clean. -/
theorem coupling_run_lazy (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (wit : WitIn) (j : Fin (n + 1)) (σ' : σ) :
    (fun r => (r.1.1, r.1.2.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            (ambientProd (StmtIn := StmtIn) pSpec impl
              + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
          (P.runToRoundFS j stmt (P.input (stmt, wit)))) (σ', ∅))
      = (fun r => (r.1.1.toMessagesUpTo, r.1.2, r.2.1)) <$>
        evalDist (StateT.run (simulateQ
            ((ambientProd (StmtIn := StmtIn) pSpec impl).addLift
              (challengeQueryImpl (pSpec := pSpec)) :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ)
              (StateT (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp))
          (P.runToRound j stmt wit)) (σ', ∅)) := by
  -- (1) lazy-product = uniform-product (this file's run coupling).
  rw [runToRoundFS_lazy_uniform_coupling P impl stmt wit j σ']
  -- (2) uniform-product = interactive, via `coupling_run` at `σ := σ × QueryCache`,
  --     ambient impl `:= ambientProd impl`. Its `addLift fsChallengeUniformImpl` is exactly
  --     `ambientProd impl + fsUniformProd`.
  have hcr := coupling_run P (σ := σ × QueryCache (fsChallengeOracle StmtIn pSpec))
    (ambientProd (StmtIn := StmtIn) pSpec impl) stmt wit j (σ', ∅)
  have halign : ((ambientProd (StmtIn := StmtIn) pSpec impl).addLift
        (fsChallengeUniformImpl (σ := σ × QueryCache (fsChallengeOracle StmtIn pSpec))) :
      QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
        (StateT (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) ProbComp))
      = ambientProd (StmtIn := StmtIn) pSpec impl
        + fsUniformProd (StmtIn := StmtIn) (σ := σ) pSpec := by
    rw [QueryImpl.addLift_def, QueryImpl.liftTarget_self, QueryImpl.liftTarget_self]
  rw [halign] at hcr
  -- `coupling_run` keeps the whole product state `(σ, cache)` as the third projected component;
  -- post-compose `Prod.map id (Prod.map id Prod.fst)` on both sides to drop the cache, matching our
  -- `(messages, prvState, σ)` projection.
  have hmap := congrArg (fun d => (Prod.map id (Prod.map id Prod.fst)
      : _ × _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)) → _ × _ × σ) <$> d) hcr
  simp only [evalDist_map, Functor.map_map, Function.comp, Prod.map, id_eq] at hmap ⊢
  -- The interactive challenge handler is lifted to the product `StateT` via a (defeq) `MonadLiftT`
  -- chain that differs syntactically from `coupling_run`'s; reconcile per query with `QueryImpl.ext`.
  convert hmap using 5
  apply QueryImpl.ext
  rintro (t | t)
  · rfl
  · apply StateT.ext
    intro s
    simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
      liftM, monadLift, MonadLift.monadLift, StateT.lift, StateT.run_bind, StateT.run_monadLift,
      bind_pure_comp, map_bind, _root_.map_pure, Functor.map_map, Function.comp]
    rfl

-- Axiom audit of the deliverables (all `[propext, Classical.choice, Quot.sound]`).
#print axioms processRoundFS_lazy_uniform_step
#print axioms runToRoundFS_lazy_uniform_coupling
#print axioms coupling_run_lazy

end Reduction
