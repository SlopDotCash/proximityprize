/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKTransferReduction
import ArkLib.ToMathlib.OracleCompEvalDistBindComm

/-!
# Infrastructure for the #116 HVZK coupling kernel `canonicalFSPerStateCoupling`

Verified bricks toward the per-`oSpec`-state lazy-vs-eager coupling residual of the basic
Fiat-Shamir HVZK transfer (`Reduction.canonicalFSPerStateCoupling`):

1. **Fiat-Shamir key distinctness** (`fsKey_ne_of_round_ne`, `fsKey_ne_of_round_lt`): the
   Fiat-Shamir challenge-oracle domain is a sigma over the challenge round index, so keys at
   different rounds are automatically distinct.
2. **Cache discipline** (`FSCacheBelow` and its lemmas, `canonicalFSChallengeImpl_run_none`,
   `FSCacheBelow.canonicalFSChallengeImpl_run`): a cache containing only keys with round index
   `< j` answers any round-`≥ j` query by a cache miss, which through the lazy random oracle is a
   fresh uniform sample plus a single cache write.
3. **Run shapes of the combined implementations** (`canonicalFSImpl_run_inl/inr`,
   `addLift_challengeQueryImpl_run_inl/inr`, `add_fsTableImpl_run_inl/inr`): how the combined
   implementations act on their states, exposing that `oSpec` queries never touch the challenge
   cache and challenge queries never touch the `oSpec` state.
4. **The mixed lazy = eager challenge-table bridge**
   (`evalDist_simulateQ_canonicalFSImpl_run_eq_eager` and its `run'`/empty-cache forms): for
   *any* computation over `oSpec + fsChallengeOracle`, simulating through the canonical combined
   implementation (lazy random oracle on the challenge side) is distributionally equal to
   pre-sampling a uniform full dependent challenge table and answering challenge queries
   deterministically from it. This lifts `fsChallenge_lazy_eq_eager` across the mixed
   `oSpec`-interleaved simulation and eliminates the challenge cache from the kernel.
5. **Kernel reduction** (`canonicalFSPerStateCoupling_of_eagerCoupling`): the coupling kernel
   `canonicalFSPerStateCoupling` follows from the single cache-free eager residual
   `canonicalFSPerStateEagerCoupling`.
6. **Eager verifier collapse** (`derivedTranscriptAux`,
   `simulateQ_add_fsTableImpl_deriveTranscriptSRAux_run`,
   `simulateQ_add_fsTableImpl_deriveTranscriptFS_run`): under the eager table implementation the
   Fiat-Shamir verifier's transcript re-derivation is `pure` of the deterministic table-derived
   transcript — no randomness, no state change.
7. **Prefix-consistency bricks for the per-round coupling induction**
   (`ProtocolSpec.toMessagesUpTo_extend`, `MessagesUpTo.take_extend_self`,
   `MessagesUpTo.take_concat_self`): message bundles extended across a round leave all proper
   prefixes unchanged, so the honest prover's round-`j` Fiat-Shamir key coincides with the
   verifier's re-derivation key.

The single remaining unproven residual is `canonicalFSPerStateEagerCoupling`: the per-round
`Fin.induction` coupling the eager-table honest execution to the interactive run (fresh-uniform
challenges), whose remaining ingredients are the derive-vs-extend/concat commutation (from the
take-lemmas above), per-round adaptive table-read marginalization
(`evalDist_uniformSample_bind_update_bind_dep` + key distinctness), and the
`receiveChallenge`/`getChallenge` order swap (`OracleComp.evalDist_bind_comm`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]

/-! ## Piece 1: Fiat-Shamir query keys at different rounds are distinct -/

/-- **Fiat-Shamir keys at different challenge rounds are distinct.** The domain of
`fsChallengeOracle StmtIn pSpec` is the sigma type
`(i : pSpec.ChallengeIdx) × (StmtIn × pSpec.MessagesUpTo i.1.castSucc)`, so two keys with
different round indices are automatically different (regardless of the statement/message-prefix
payloads, whose types depend on the round). -/
theorem fsKey_ne_of_round_ne {i j : pSpec.ChallengeIdx} (h : i ≠ j)
    (x : StmtIn × pSpec.MessagesUpTo i.1.castSucc)
    (y : StmtIn × pSpec.MessagesUpTo j.1.castSucc) :
    (⟨i, x⟩ : (fsChallengeOracle StmtIn pSpec).Domain) ≠ ⟨j, y⟩ :=
  fun hEq => h (congrArg Sigma.fst hEq)

/-- Round-ordered form of `fsKey_ne_of_round_ne`: a strictly earlier challenge round gives a
distinct Fiat-Shamir key. -/
theorem fsKey_ne_of_round_lt {i j : pSpec.ChallengeIdx} (h : (i.1 : ℕ) < (j.1 : ℕ))
    (x : StmtIn × pSpec.MessagesUpTo i.1.castSucc)
    (y : StmtIn × pSpec.MessagesUpTo j.1.castSucc) :
    (⟨i, x⟩ : (fsChallengeOracle StmtIn pSpec).Domain) ≠ ⟨j, y⟩ :=
  fsKey_ne_of_round_ne
    (fun hij => absurd (congrArg (fun k : pSpec.ChallengeIdx => (k.1 : ℕ)) hij)
      (Nat.ne_of_lt h)) x y

/-! ## Piece 2: cache discipline and lazy-random-oracle freshness -/

/-- A Fiat-Shamir challenge cache is **below round `j`** if it contains no entry whose key has
challenge-round index `≥ j`. Along an honest run processed in round order, the cache before
round `j` is below `j`, so the round-`j` query is guaranteed to be a fresh cache miss. -/
def FSCacheBelow (j : ℕ) (cache : (fsChallengeOracle StmtIn pSpec).QueryCache) : Prop :=
  ∀ key : (fsChallengeOracle StmtIn pSpec).Domain, j ≤ (key.1.1 : ℕ) → cache key = none

/-- The empty cache is below every round. -/
theorem fsCacheBelow_empty (j : ℕ) :
    FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j ∅ :=
  fun _ _ => rfl

/-- Cache-below is monotone in the round bound. -/
theorem FSCacheBelow.mono {j k : ℕ} (hjk : j ≤ k)
    {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    (h : FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j cache) :
    FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) k cache :=
  fun key hk => h key (le_trans hjk hk)

/-- A cache below round `j` misses every key at a round `≥ j`. -/
theorem FSCacheBelow.miss {j : ℕ} {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    (h : FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j cache)
    {i : pSpec.ChallengeIdx} (hij : j ≤ (i.1 : ℕ))
    (x : StmtIn × pSpec.MessagesUpTo i.1.castSucc) :
    cache ⟨i, x⟩ = none :=
  h ⟨i, x⟩ hij

/-- Caching a key at a round `< j` preserves being below round `j` (the new entry is at a strictly
earlier round, hence at a distinct key from any round-`≥ j` query by `fsKey_ne_of_round_ne`). -/
theorem FSCacheBelow.cacheQuery {j : ℕ} {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    (h : FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j cache)
    {i : pSpec.ChallengeIdx} (hi : (i.1 : ℕ) < j)
    (x : StmtIn × pSpec.MessagesUpTo i.1.castSucc)
    (u : (fsChallengeOracle StmtIn pSpec).Range ⟨i, x⟩) :
    FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j
      (cache.cacheQuery ⟨i, x⟩ u) := by
  intro key hkey
  have hne : key ≠ (⟨i, x⟩ : (fsChallengeOracle StmtIn pSpec).Domain) := by
    intro hEq
    have h1 : ((key.1.1 : Fin n) : ℕ) = ((i.1 : Fin n) : ℕ) :=
      congrArg (fun k : (fsChallengeOracle StmtIn pSpec).Domain => ((k.1.1 : Fin n) : ℕ)) hEq
    omega
  rw [QueryCache.cacheQuery_of_ne (t' := key) (t := ⟨i, x⟩) cache u hne]
  exact h key hkey

/-- **Lazy random-oracle cache miss = fresh uniform sample + single cache write.** On an uncached
key, the canonical Fiat-Shamir challenge implementation samples the challenge uniformly and adds
exactly that key to the cache. -/
theorem canonicalFSChallengeImpl_run_none
    {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    {t : (fsChallengeOracle StmtIn pSpec).Domain} (h : cache t = none) :
    ((canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)) t).run cache
      = (fun u => (u, cache.cacheQuery t u)) <$>
          ($ᵗ ((fsChallengeOracle StmtIn pSpec).Range t)) := by
  unfold canonicalFSChallengeImpl
  exact QueryImpl.withCaching_run_none _ h

/-- Lazy random-oracle cache hit: the cached value is returned and the cache is unchanged. -/
theorem canonicalFSChallengeImpl_run_some
    {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    {t : (fsChallengeOracle StmtIn pSpec).Domain}
    {u : (fsChallengeOracle StmtIn pSpec).Range t} (h : cache t = some u) :
    ((canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)) t).run cache
      = pure (u, cache) := by
  unfold canonicalFSChallengeImpl
  exact QueryImpl.withCaching_run_some _ h

/-- **Round-`j` queries are fresh through a below-`j` cache**: combining `FSCacheBelow.miss` with
the lazy random-oracle miss semantics, a round-`≥ j` challenge query through a cache below round
`j` is answered by a fresh uniform draw, and the cache gains exactly the queried key. -/
theorem FSCacheBelow.canonicalFSChallengeImpl_run {j : ℕ}
    {cache : (fsChallengeOracle StmtIn pSpec).QueryCache}
    (h : FSCacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j cache)
    {i : pSpec.ChallengeIdx} (hij : j ≤ (i.1 : ℕ))
    (x : StmtIn × pSpec.MessagesUpTo i.1.castSucc) :
    ((canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)) ⟨i, x⟩).run cache
      = (fun u => (u, cache.cacheQuery ⟨i, x⟩ u)) <$>
          ($ᵗ ((fsChallengeOracle StmtIn pSpec).Range ⟨i, x⟩)) :=
  canonicalFSChallengeImpl_run_none (h.miss hij x)

/-! ## Run shapes of the combined (addLift) implementations

These expose the action of the two combined implementations on their states: `oSpec` queries act
only on the `σ` component (never the challenge cache), and challenge queries act only on the cache
(never the `σ` state) on the Fiat-Shamir side, resp. leave `σ` unchanged on the interactive side.
-/

/-- An `oSpec` query through the canonical combined Fiat-Shamir implementation acts on the `σ`
component only; the challenge cache rides along unchanged. (The `pure` is ascribed at the
sum-spec range type so that downstream `bind_assoc`/`pure_bind` rewrites match the
`simulateQ`-generated bind type ascriptions syntactically.) -/
theorem canonicalFSImpl_run_inl (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : ι) (a : σ) (c : (fsChallengeOracle StmtIn pSpec).QueryCache) :
    ((canonicalFSImpl (StmtIn := StmtIn) impl) (Sum.inl t)).run (a, c)
      = (impl t).run a >>= fun y =>
          (pure (y.1, (y.2, c)) :
            ProbComp ((oSpec + fsChallengeOracle StmtIn pSpec).Range (Sum.inl t) ×
              (σ × (fsChallengeOracle StmtIn pSpec).QueryCache))) :=
  rfl

/-- A challenge query through the canonical combined Fiat-Shamir implementation acts on the cache
component only; the `σ` state rides along unchanged. -/
theorem canonicalFSImpl_run_inr (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : (fsChallengeOracle StmtIn pSpec).Domain) (a : σ)
    (c : (fsChallengeOracle StmtIn pSpec).QueryCache) :
    ((canonicalFSImpl (StmtIn := StmtIn) impl) (Sum.inr t)).run (a, c)
      = ((canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec)) t).run c >>=
          fun y =>
          (pure (y.1, (a, y.2)) :
            ProbComp ((oSpec + fsChallengeOracle StmtIn pSpec).Range (Sum.inr t) ×
              (σ × (fsChallengeOracle StmtIn pSpec).QueryCache))) :=
  rfl

/-- An `oSpec` query through the interactive combined implementation is just `impl`. -/
theorem addLift_challengeQueryImpl_run_inl (impl : QueryImpl oSpec (StateT σ ProbComp))
    (t : ι) (a : σ) :
    ((impl.addLift (challengeQueryImpl (pSpec := pSpec))
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (Sum.inl t)).run a
      = (impl t).run a :=
  rfl

/-- A challenge query through the interactive combined implementation is a fresh uniform draw,
leaving the `σ` state unchanged. -/
theorem addLift_challengeQueryImpl_run_inr (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : ([pSpec.Challenge]ₒ).Domain) (a : σ) :
    ((impl.addLift (challengeQueryImpl (pSpec := pSpec))
        : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (Sum.inr q)).run a
      = ($ᵗ (pSpec.Challenge q.1)) >>= fun u => pure (u, a) :=
  rfl

/-! ## Piece 2 capstone: the mixed lazy = eager challenge-table bridge

`Reduction.fsChallenge_lazy_eq_eager` covers computations over the Fiat-Shamir challenge oracle
*alone*. The coupling kernel needs the same lazy-vs-eager equivalence **lifted across the mixed
`oSpec + fsChallengeOracle` simulation**: the honest execution interleaves (probabilistic,
stateful) `oSpec` queries through `impl` with challenge queries through the lazy random oracle.
The bridge below shows that the joint `(output, oSpec-state)` distribution of any such mixed
computation, simulated through `canonicalFSImpl impl` from cache `c`, equals: sample a full
dependent challenge table `g` uniformly, then run the computation with challenge queries answered
*deterministically* from the overlay `tableExtendingDep c g` (cache entries take priority). This
eliminates the challenge cache from the kernel entirely. -/

/-- Deterministic Fiat-Shamir challenge implementation answering from a fixed table `g`, in the
same state monad as a given `oSpec` implementation (the state is untouched). -/
def fsTableImpl (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q) :
    QueryImpl (fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp) :=
  fun t => pure (g t)

@[simp]
theorem fsTableImpl_run (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
    (fsChallengeOracle StmtIn pSpec).Range q)
    (t : (fsChallengeOracle StmtIn pSpec).Domain) (a : σ) :
    ((fsTableImpl (σ := σ) g) t).run a = pure (g t, a) :=
  rfl

/-- An `oSpec` query through the eager-table combined implementation is just `impl` (stated at the
sum-spec range type so it fires on `simulateQ`-generated goals). -/
theorem add_fsTableImpl_run_inl (impl : QueryImpl oSpec (StateT σ ProbComp))
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) (t : ι) (a : σ) :
    ((impl + fsTableImpl (σ := σ) g) (Sum.inl t)).run a = (impl t).run a :=
  rfl

/-- A challenge query through the eager-table combined implementation reads the table and leaves
the state unchanged (stated at the sum-spec range type so it fires on `simulateQ`-generated
goals). -/
theorem add_fsTableImpl_run_inr (impl : QueryImpl oSpec (StateT σ ProbComp))
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (t : (fsChallengeOracle StmtIn pSpec).Domain) (a : σ) :
    ((impl + fsTableImpl (σ := σ) g) (Sum.inr t)).run a
      = (pure (g t, a) :
          ProbComp ((oSpec + fsChallengeOracle StmtIn pSpec).Range (Sum.inr t) × σ)) :=
  rfl

/-- Monadic form of the dependent marginalization lemma
`OracleComp.evalDist_uniformSample_bind_update_dep`: post-binding an arbitrary probabilistic
continuation `Ψ` through a single-coordinate resample of a uniform dependent table is
measure-preserving. -/
lemma evalDist_uniformSample_bind_update_bind_dep
    {ι' : Type} {R : ι' → Type} [Fintype ι'] [DecidableEq ι']
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] [∀ i, SampleableType (R i)]
    [SampleableType (∀ i, R i)] (t : ι') {β : Type} (Ψ : (∀ i, R i) → ProbComp β) :
    𝒟[do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); Ψ (Function.update g t u)]
      = 𝒟[do let g ← $ᵗ (∀ i, R i); Ψ g] := by
  have h1 : (do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); Ψ (Function.update g t u))
      = (($ᵗ (R t)) >>= fun u => ($ᵗ (∀ i, R i)) >>= fun g =>
          pure (Function.update g t u)) >>= Ψ := by
    simp only [bind_assoc, pure_bind]
  have h2 : (($ᵗ (R t)) >>= fun u => ($ᵗ (∀ i, R i)) >>= fun g =>
        pure (Function.update g t u))
      = (do let u ← $ᵗ (R t); let g ← $ᵗ (∀ i, R i); pure (Function.update g t u)) := rfl
  rw [h1, evalDist_bind, h2, OracleComp.evalDist_uniformSample_bind_update_dep t,
    ← evalDist_bind]

set_option maxHeartbeats 2000000 in
/-- **Mixed lazy random oracle = eager challenge-table sampling (cache-parametrized).**

Simulating any computation over `oSpec + fsChallengeOracle` through the canonical combined
implementation (lazy random oracle on the challenge side) from `(a, c)`, and observing the joint
`(output, oSpec-state)` marginal (the final cache is discarded), is distributionally equal to:
eagerly sample a uniform full challenge table `g`, then simulate with challenge queries answered
deterministically from the overlay `tableExtendingDep c g`. This is the lazy-vs-eager equivalence
`fsChallenge_lazy_eq_eager` lifted across the mixed `oSpec + fsChallengeOracle` simulation, and is
the form in which the cache disappears from the HVZK coupling kernel. -/
theorem evalDist_simulateQ_canonicalFSImpl_run_eq_eager
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {α : Type}
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α)
    (a : σ) (c : (fsChallengeOracle StmtIn pSpec).QueryCache) :
    𝒟[(fun p : α × σ × (fsChallengeOracle StmtIn pSpec).QueryCache => (p.1, p.2.1)) <$>
        (simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl) oa).run (a, c)]
      = 𝒟[do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) (tableExtendingDep c g)) oa).run a] := by
  classical
  haveI : Nonempty ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q) := ⟨fun q => Classical.arbitrary _⟩
  induction oa using OracleComp.inductionOn generalizing a c with
  | pure x =>
    have hlhs : ((fun p : α × σ × (fsChallengeOracle StmtIn pSpec).QueryCache =>
          (p.1, p.2.1)) <$>
        (simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl)
          (pure x : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α)).run (a, c))
        = (pure (x, a) : ProbComp (α × σ)) := by
      rw [simulateQ_pure]
      change (fun p : α × σ × (fsChallengeOracle StmtIn pSpec).QueryCache => (p.1, p.2.1)) <$>
        (pure (x, (a, c)) : ProbComp _) = _
      rw [map_pure]
    rw [hlhs]
    have hin : ∀ g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
        (fsChallengeOracle StmtIn pSpec).Range q,
        (simulateQ (impl + fsTableImpl (σ := σ) (tableExtendingDep c g))
          (pure x : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α)).run a
        = (pure (x, a) : ProbComp (α × σ)) := by
      intro g; rw [simulateQ_pure]; rfl
    simp only [hin]
    symm
    refine evalDist_ext fun z => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (by simp), one_mul]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases t with t₁ | t₂
    · -- `oSpec` query: acts on `σ` only; the table sample commutes across it.
      rw [canonicalFSImpl_run_inl, bind_assoc]
      simp only [pure_bind, add_fsTableImpl_run_inl]
      trans 𝒟[(impl t₁).run a >>= fun y =>
        ($ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
          (fsChallengeOracle StmtIn pSpec).Range q)) >>= fun g =>
          (simulateQ (impl + fsTableImpl (σ := σ) (tableExtendingDep c g)) (k y.1)).run y.2]
      · rw [evalDist_bind, evalDist_bind]
        refine congrArg _ (funext fun y => ?_)
        exact ih y.1 y.2 c
      · exact (OracleComp.evalDist_bind_comm _ _ _).symm
    · -- challenge query: split on cache hit/miss.
      rcases hc : c t₂ with _ | u
      · -- miss: fresh uniform draw + cache write; marginalize the resample away.
        rw [canonicalFSImpl_run_inr, canonicalFSChallengeImpl_run_none hc, bind_assoc]
        simp only [pure_bind, bind_map_left, add_fsTableImpl_run_inr]
        set ψ : ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q) → ProbComp (α × σ) := fun g' =>
          (simulateQ (impl + fsTableImpl (σ := σ) (tableExtendingDep c g'))
            (k (tableExtendingDep c g' t₂))).run a
          with hψ
        have hfun : ∀ u : (fsChallengeOracle StmtIn pSpec).Range t₂,
            (fun g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
                (fsChallengeOracle StmtIn pSpec).Range q =>
              (simulateQ (impl + fsTableImpl (σ := σ) (tableExtendingDep (c.cacheQuery t₂ u) g))
                (k u)).run a)
            = fun g => ψ (Function.update g t₂ u) := by
          intro u
          funext g
          simp only [hψ]
          rw [tableExtendingDep_cacheQuery, ← tableExtendingDep_update_of_none c g hc u]
          simp only [Function.update_self]
        trans 𝒟[do
          let u ← $ᵗ ((fsChallengeOracle StmtIn pSpec).Range t₂)
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          ψ (Function.update g t₂ u)]
        · rw [evalDist_bind, evalDist_bind]
          refine congrArg _ (funext fun u => ?_)
          rw [ih u a (c.cacheQuery t₂ u)]
          rw [hfun u]
        · rw [evalDist_uniformSample_bind_update_bind_dep
            (ι' := (fsChallengeOracle StmtIn pSpec).Domain)
            (R := (fsChallengeOracle StmtIn pSpec).Range) t₂ ψ]
      · -- hit: the cached value is read back on both sides; no sampling.
        rw [canonicalFSImpl_run_inr, canonicalFSChallengeImpl_run_some hc, bind_assoc]
        simp only [pure_bind, add_fsTableImpl_run_inr]
        have htbl : ∀ g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q,
            tableExtendingDep c g t₂ = u := by
          intro g; simp [tableExtendingDep, hc]
        simp only [htbl]
        exact ih u a c

/-- Empty-cache form of the mixed lazy = eager bridge: starting from the empty challenge cache,
the overlay is the bare uniform table. -/
theorem evalDist_simulateQ_canonicalFSImpl_run_empty_eq_eager
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {α : Type}
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) (a : σ) :
    𝒟[(fun p : α × σ × (fsChallengeOracle StmtIn pSpec).QueryCache => (p.1, p.2.1)) <$>
        (simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl) oa).run (a, ∅)]
      = 𝒟[do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) g) oa).run a] := by
  rw [evalDist_simulateQ_canonicalFSImpl_run_eq_eager impl oa a ∅]
  refine congrArg _ ?_
  refine congrArg _ (funext fun g => ?_)
  rw [tableExtendingDep_empty]

/-- Output-marginal (`run'`) form of the mixed lazy = eager bridge from the empty cache. -/
theorem evalDist_simulateQ_canonicalFSImpl_run'_empty_eq_eager
    (impl : QueryImpl oSpec (StateT σ ProbComp)) {α : Type}
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) (a : σ) :
    𝒟[(simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl) oa).run' (a, ∅)]
      = 𝒟[do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) g) oa).run' a] := by
  have h1 : (simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl) oa).run' (a, ∅)
      = Prod.fst <$> ((fun p : α × σ × (fsChallengeOracle StmtIn pSpec).QueryCache =>
          (p.1, p.2.1)) <$>
          (simulateQ (canonicalFSImpl (StmtIn := StmtIn) impl) oa).run (a, ∅)) := by
    rw [Functor.map_map]
    rfl
  have h2 : (do
        let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
          (fsChallengeOracle StmtIn pSpec).Range q)
        (simulateQ (impl + fsTableImpl (σ := σ) g) oa).run' a)
      = Prod.fst <$> (do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) g) oa).run a) := by
    rw [map_bind]
    exact rfl
  rw [h1, h2]
  conv_lhs => rw [evalDist_map]
  conv_rhs => rw [evalDist_map]
  rw [evalDist_simulateQ_canonicalFSImpl_run_empty_eq_eager impl oa a]

/-! ## Reduction of the coupling kernel to its cache-free eager form

Applying the mixed bridge to the Fiat-Shamir side of `canonicalFSPerStateCoupling` removes the
lazy random oracle and its cache entirely: what remains is the **eager** residual below, comparing
the honest execution with challenges read deterministically from a pre-sampled uniform table
against the interactive run with fresh-uniform verifier challenges. -/

/-- Commute an output map past `StateT.run'`. -/
private lemma stateT_run'_map {σ' α β : Type} (f : α → β) (M : StateT σ' ProbComp α) (s : σ') :
    (f <$> M).run' s = f <$> M.run' s := by
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- **The cache-free eager coupling residual.** The form of the per-`oSpec`-state coupling left
after the mixed lazy = eager bridge has eliminated the challenge cache: on the Fiat-Shamir side a
full uniform challenge table `g` is sampled once and the explicit honest execution reads its
challenges (prover side and verifier re-derivation alike) deterministically from `g`; on the
interactive side the verifier draws each challenge fresh-uniform. Both sides are message-bundle
marginals at a fixed starting `oSpec`-state `a`.

This residual is TRUE: across an honest run the per-round table reads are at pairwise-distinct
keys (`fsKey_ne_of_round_ne`), so they are independent fresh uniforms — matching the interactive
draws — and the verifier re-reads exactly the prover's keys, so the re-derived transcript agrees
and the message marginal never fails out. -/
def canonicalFSPerStateEagerCoupling
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) : Prop :=
  ∀ a : σ,
    𝒟[Option.map (fun r : (FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
          StmtOut => r.1.1) <$>
        (do
          let g ← $ᵗ ((q : (fsChallengeOracle StmtIn pSpec).Domain) →
            (fsChallengeOracle StmtIn pSpec).Range q)
          (simulateQ (impl + fsTableImpl (σ := σ) g)
            (R.fiatShamirHonestExecution stmt wit).run).run' a)]
      = 𝒟[Option.map (msgProjFS (pSpec := pSpec)) <$>
          StateT.run'
            (simulateQ (impl.addLift challengeQueryImpl)
              ((Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
                  result.1.1)) <$> (R.run stmt wit).run)
              : StateT σ ProbComp (Option (FullTranscript pSpec))) a]

set_option maxHeartbeats 1000000 in
/-- **The coupling kernel reduces to its cache-free eager form.** Given the eager residual
`canonicalFSPerStateEagerCoupling`, the per-`oSpec`-state coupling kernel
`canonicalFSPerStateCoupling` holds: the Fiat-Shamir side is rewritten by the mixed
lazy = eager bridge (`evalDist_simulateQ_canonicalFSImpl_run'_empty_eq_eager`), eliminating the
lazy random oracle and its cache. -/
theorem canonicalFSPerStateCoupling_of_eagerCoupling
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (h : canonicalFSPerStateEagerCoupling impl R stmt wit) :
    canonicalFSPerStateCoupling impl R stmt wit := by
  intro a
  refine Eq.trans ?_ (h a)
  rw [show (impl.addLift (canonicalFSChallengeImpl (StmtIn := StmtIn) (pSpec := pSpec))
        : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
            (StateT (σ × (fsChallengeOracle StmtIn pSpec).QueryCache) ProbComp))
      = canonicalFSImpl (StmtIn := StmtIn) impl from rfl]
  rw [stateT_run'_map]
  conv_lhs => rw [evalDist_map,
    evalDist_simulateQ_canonicalFSImpl_run'_empty_eq_eager impl
      (R.fiatShamirHonestExecution stmt wit).run a]
  conv_rhs => rw [evalDist_map]

/-! ## Verifier collapse in the eager world

Under the eager table implementation `impl + fsTableImpl g`, the Fiat-Shamir verifier's
transcript re-derivation `deriveTranscriptSRAux`/`deriveTranscriptFS` makes no probabilistic or
stateful steps at all: every challenge query is answered deterministically by the table `g`, so
the whole derivation collapses to `pure` of the explicit deterministic transcript
`derivedTranscriptAux g`. This is the verifier half of the eager coupling residual: it re-reads
exactly the keys the honest prover read, so (given prover-side prefix consistency) it
reconstructs the prover's transcript on the nose. -/

/-- The transcript determined by re-deriving challenges from a fixed Fiat-Shamir challenge table
`g`: the deterministic value of `MessagesUpTo.deriveTranscriptSRAux` when every challenge query is
answered by `g`. -/
def derivedTranscriptAux
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) (j : Fin (k + 1)) :
    pSpec.Transcript (j.castLE (by omega)) :=
  Fin.induction (n := k)
    (fun i => i.elim0)
    (fun i ih =>
      match hDir : pSpec.dir (i.castLE (by omega)) with
      | .V_to_P =>
        ih.concat (g ⟨⟨i.castLE (by omega), hDir⟩, (stmt, messages.take i.castSucc)⟩)
      | .P_to_V => ih.concat (messages ⟨i, hDir⟩))
    j

/-- A Fiat-Shamir challenge query issued inside the sum-spec computation and simulated through
the eager-table implementation collapses to a `pure` table read (no state change). -/
theorem simulateQ_add_fsTableImpl_query_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (key : (fsChallengeOracle StmtIn pSpec).Domain) (a : σ) :
    (simulateQ (impl + fsTableImpl (σ := σ) g)
      (query (spec := fsChallengeOracle StmtIn pSpec)
        (m := OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) key)).run a
      = pure (g key, a) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **Eager verifier collapse.** Through the eager-table implementation, the Fiat-Shamir partial
transcript derivation is a `pure` computation returning the deterministic table-derived
transcript: no randomness is consumed and the `oSpec` state is untouched. -/
theorem simulateQ_add_fsTableImpl_deriveTranscriptSRAux_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) (a : σ) :
    (simulateQ (impl + fsTableImpl (σ := σ) g)
      (MessagesUpTo.deriveTranscriptSRAux (oSpec := oSpec) stmt k messages j)).run a
      = pure (derivedTranscriptAux g stmt k messages j, a) := by
  induction j using Fin.induction with
  | zero =>
    simp only [MessagesUpTo.deriveTranscriptSRAux, derivedTranscriptAux, Fin.induction_zero]
    rw [simulateQ_pure]
    rfl
  | succ i ihj =>
    simp only [MessagesUpTo.deriveTranscriptSRAux, derivedTranscriptAux] at ihj ⊢
    rw [Fin.induction_succ, Fin.induction_succ]
    rw [simulateQ_bind, StateT.run_bind, ihj]
    simp only [pure_bind]
    split <;> rename_i hDir <;> split <;> rename_i hDir' <;>
      first
        | exact Direction.noConfusion (hDir.symm.trans hDir')
        | (rw [simulateQ_pure]; rfl)
        | (rw [simulateQ_bind, StateT.run_bind,
            simulateQ_add_fsTableImpl_query_run impl g _ a]
           simp only [pure_bind]
           rw [simulateQ_pure]
           rfl)

/-- Full-length form of the eager verifier collapse: re-deriving the entire transcript from the
final message bundle through the eager-table implementation is `pure` of the table-derived full
transcript. -/
theorem simulateQ_add_fsTableImpl_deriveTranscriptFS_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (g : (q : (fsChallengeOracle StmtIn pSpec).Domain) →
      (fsChallengeOracle StmtIn pSpec).Range q)
    (stmt : StmtIn) (messages : pSpec.Messages) (a : σ) :
    (simulateQ (impl + fsTableImpl (σ := σ) g)
      (Messages.deriveTranscriptFS (oSpec := oSpec) stmt messages)).run a
      = pure (derivedTranscriptAux g stmt (Fin.last n) messages (Fin.last n), a) :=
  simulateQ_add_fsTableImpl_deriveTranscriptSRAux_run impl g stmt (Fin.last n) messages
    (Fin.last n) a

end Reduction

namespace ProtocolSpec

/-- Extracting the messages of a transcript extended by a `V_to_P` challenge leaves the message
bundle's content unchanged: `toMessagesUpTo` commutes with challenge-`concat` as the message-side
`extend`. The `V_to_P` companion of `toMessagesUpTo_concat`. -/
theorem toMessagesUpTo_extend {n : ℕ} {pSpec : ProtocolSpec n} {m : Fin n}
    (h : pSpec.dir m = .V_to_P)
    (T : Transcript m.castSucc pSpec) (ch : pSpec.Challenge ⟨m, h⟩) :
    (Transcript.concat ch T).toMessagesUpTo = T.toMessagesUpTo.extend h := by
  funext j
  obtain ⟨i, hi⟩ := j
  simp only [Transcript.toMessagesUpTo, Transcript.concat, MessagesUpTo.extend,
    MessagesUpTo.concat']
  revert hi
  induction i using Fin.lastCases with
  | last =>
    intro hi
    exact Direction.noConfusion (hi.symm.trans h)
  | cast k =>
    intro _
    simp [Fin.snoc_castSucc, Fin.dconcat_castSucc]

namespace MessagesUpTo

/-- Extending a message bundle across a challenge round does not change its full prefix: taking
back the original length recovers the original bundle. Together with `take_concat_self` this is
the prefix-consistency that makes the Fiat-Shamir verifier's re-derivation read exactly the keys
the honest prover queried. -/
theorem take_extend_self {n : ℕ} {pSpec : ProtocolSpec n} {k : Fin n}
    (m : MessagesUpTo k.castSucc pSpec) (h : pSpec.dir k = .V_to_P) :
    (m.extend h).take (⟨k.val, by omega⟩ : Fin ((k.val + 1) + 1)) = m := by
  funext j
  obtain ⟨i, hi⟩ := j
  simp only [MessagesUpTo.take, MessagesUpTo.extend, MessagesUpTo.concat']
  exact congrFun (Fin.dconcat_castSucc
    (motive := fun x : Fin (k.val + 1) =>
      pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
        pSpec.«Type» (Fin.castLE (by omega) x))
    (fun i hi => m ⟨i, hi⟩) _ i) _

/-- Concatenating a message onto a bundle does not change its full prefix: taking back the
original length recovers the original bundle. -/
theorem take_concat_self {n : ℕ} {pSpec : ProtocolSpec n} {k : Fin n}
    (m : MessagesUpTo k.castSucc pSpec) (h : pSpec.dir k = .P_to_V)
    (msg : pSpec.Message ⟨k, h⟩) :
    (m.concat h msg).take (⟨k.val, by omega⟩ : Fin ((k.val + 1) + 1)) = m := by
  funext j
  obtain ⟨i, hi⟩ := j
  simp only [MessagesUpTo.take, MessagesUpTo.concat, MessagesUpTo.concat']
  exact congrFun (Fin.dconcat_castSucc
    (motive := fun x : Fin (k.val + 1) =>
      pSpec.dir (Fin.castLE (by omega) x) = Direction.P_to_V →
        pSpec.«Type» (Fin.castLE (by omega) x))
    (fun i hi => m ⟨i, hi⟩) _ i) _

end MessagesUpTo

end ProtocolSpec

#print axioms Reduction.fsKey_ne_of_round_ne
#print axioms Reduction.fsKey_ne_of_round_lt
#print axioms Reduction.FSCacheBelow.cacheQuery
#print axioms Reduction.canonicalFSChallengeImpl_run_none
#print axioms Reduction.FSCacheBelow.canonicalFSChallengeImpl_run
#print axioms Reduction.canonicalFSImpl_run_inl
#print axioms Reduction.canonicalFSImpl_run_inr
#print axioms Reduction.addLift_challengeQueryImpl_run_inl
#print axioms Reduction.addLift_challengeQueryImpl_run_inr
#print axioms Reduction.evalDist_uniformSample_bind_update_bind_dep
#print axioms Reduction.evalDist_simulateQ_canonicalFSImpl_run_eq_eager
#print axioms Reduction.evalDist_simulateQ_canonicalFSImpl_run_empty_eq_eager
#print axioms Reduction.evalDist_simulateQ_canonicalFSImpl_run'_empty_eq_eager
#print axioms Reduction.canonicalFSPerStateCoupling_of_eagerCoupling
#print axioms Reduction.simulateQ_add_fsTableImpl_query_run
#print axioms Reduction.simulateQ_add_fsTableImpl_deriveTranscriptSRAux_run
#print axioms Reduction.simulateQ_add_fsTableImpl_deriveTranscriptFS_run
#print axioms ProtocolSpec.toMessagesUpTo_extend
#print axioms ProtocolSpec.MessagesUpTo.take_extend_self
#print axioms ProtocolSpec.MessagesUpTo.take_concat_self
