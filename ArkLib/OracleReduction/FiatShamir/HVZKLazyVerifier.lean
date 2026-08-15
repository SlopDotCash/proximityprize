/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKLazyImpl

/-!
# The LAZY verifier leg — full-transcript Fiat-Shamir coupling (#116)

This file proves the **lazy `deriveTranscriptFS` cache-HIT replay value lemma** and assembles the
full-transcript coupling for the lazy verifier leg.

After `runToRoundFS` populates the lazy cache with the prover's challenges, the FS verifier reads
them back via `deriveTranscriptFS` (all cache HITS at the prover's keys), reconstructing the
prover's actual full transcript. We then couple that reconstructed transcript, in distribution, to
the interactive `runToRound` transcript.

The genuinely novel keystone here is `deriveTranscriptSRAux_lazy_run` (sublemma 1): mirroring
`StateRestorationTransport`'s `deriveTranscriptSRAux_simulateQ_run`, but for the LAZY impl and with
the derived transcript value *pinned* to the messages `m` plus the cached challenges (cache HITS via
`fsChallengeLazy_run_hit`), leaving the cache unchanged.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]

/-- A combined query under `ambientProd impl + fsLazyProd` at the FS oracle, on a cache HIT, replays
the stored challenge and leaves *both* state components untouched.  The lazy-product analogue of
`simulateQ_lazyProd_query_run_miss` for the hit case. -/
theorem simulateQ_lazyProd_query_run_hit
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (s : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (u : (fsChallengeOracle StmtIn pSpec).Range q) (hhit : cache q = some u) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (query (spec := fsChallengeOracle StmtIn pSpec) q :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q))) (s, cache)
      = pure (u, s, cache) := by
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
  simp only [fsChallengeLazy_run_hit q cache u hhit, _root_.map_pure, pure_bind, id_eq]

/-! ## Prefix coherence of `MessagesUpTo.take` under `concat` / `extend`

The round-`k` `concat`/`extend` only touches the round-`k` entry; on every strict-prefix index it
agrees with the original messages.  Both reduce to `dconcat`'s `castSucc` projection. -/

/-- The round-`k` `concat` agrees with `messages` on every strict-prefix (`castSucc`) index. -/
theorem concat_castSucc {k : Fin n} (messages : pSpec.MessagesUpTo k.castSucc)
    (h : pSpec.dir k = Direction.P_to_V) (msg : pSpec.Message ⟨k, h⟩)
    (i : Fin k.val) (hdir : pSpec.dir (i.castLE (by omega)) = Direction.P_to_V) :
    (messages.concat h msg) ⟨i.castSucc, by
      simpa only [Fin.val_castSucc, Fin.castLE] using hdir⟩
        = messages ⟨i, hdir⟩ := by
  obtain ⟨a, ha⟩ := i
  unfold MessagesUpTo.concat MessagesUpTo.concat'
  simp only [Fin.dconcat_castSucc]

/-- The round-`k` `extend` agrees with `messages` on every strict-prefix (`castSucc`) index. -/
theorem extend_castSucc {k : Fin n} (messages : pSpec.MessagesUpTo k.castSucc)
    (h : pSpec.dir k = Direction.V_to_P)
    (i : Fin k.val) (hdir : pSpec.dir (i.castLE (by omega)) = Direction.P_to_V) :
    (messages.extend h) ⟨i.castSucc, by
      simpa only [Fin.val_castSucc, Fin.castLE] using hdir⟩
        = messages ⟨i, hdir⟩ := by
  obtain ⟨a, ha⟩ := i
  unfold MessagesUpTo.extend MessagesUpTo.concat'
  simp only [Fin.dconcat_castSucc]

/-- Prefix preservation for `concat`: taking a prefix `p` with `p ≤ k` of `messages.concat h msg`
agrees pointwise with the same-valued prefix of `messages`. -/
theorem take_concat_castLE {k : Fin n} (messages : pSpec.MessagesUpTo k.castSucc)
    (h : pSpec.dir k = Direction.P_to_V) (msg : pSpec.Message ⟨k, h⟩)
    (p : Fin (k.castSucc.val + 1))
    (hcast : k.succ.val + 1 ≥ k.castSucc.val + 1) :
    (messages.concat h msg).take (p.castLE hcast) = messages.take p := by
  funext ⟨⟨a, ha⟩, hdir⟩
  have hak : a < k.val := by
    simp only [Fin.val_castLE] at ha
    have := p.isLt; simp only [Fin.val_castSucc] at this; omega
  exact concat_castSucc messages h msg ⟨a, hak⟩ hdir

/-- Prefix preservation for `extend`. -/
theorem take_extend_castLE {k : Fin n} (messages : pSpec.MessagesUpTo k.castSucc)
    (h : pSpec.dir k = Direction.V_to_P)
    (p : Fin (k.castSucc.val + 1))
    (hcast : k.succ.val + 1 ≥ k.castSucc.val + 1) :
    (messages.extend h).take (p.castLE hcast) = messages.take p := by
  funext ⟨⟨a, ha⟩, hdir⟩
  have hak : a < k.val := by
    simp only [Fin.val_castLE] at ha
    have := p.isLt; simp only [Fin.val_castSucc] at this; omega
  exact extend_castSucc messages h ⟨a, hak⟩ hdir

/-- Taking the full prefix (`Fin.last`) is the identity. -/
theorem take_last {k : Fin (n + 1)} (messages : pSpec.MessagesUpTo k) :
    messages.take (Fin.last k.val) = messages := by
  funext ⟨⟨a, ha⟩, hdir⟩
  rfl

/-- `take` depends only on the underlying value of its `Fin` argument (proof-irrelevance bridge).
The target types `MessagesUpTo (p.castLE)` / `MessagesUpTo (q.castLE)` coincide (same value), so this
is a plain equality. -/
theorem take_congr {k : Fin (n + 1)} (messages : pSpec.MessagesUpTo k)
    {p q : Fin (k.val + 1)} (hpq : p.val = q.val) :
    HEq (messages.take p) (messages.take q) := by
  have : p = q := Fin.ext hpq
  rw [this]

/-! Full-take forms (`take_extend_self`/`take_concat_self` — the just-inserted round's key uses the
full input messages) are upstream's `ProtocolSpec.MessagesUpTo.take_extend_self` /
`ProtocolSpec.MessagesUpTo.take_concat_self` (`FiatShamir/HVZKKernelInfra.lean`); here they are
recovered when needed via `take_extend_castLE`/`take_concat_castLE` + `take_last`. -/

/-! ## Sublemma 1: the lazy `deriveTranscriptFS` cache-HIT replay value lemma

Mirrors `ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux_simulateQ_run`, but for the LAZY
product impl `ambientProd impl + fsLazyProd`, and pins the derived transcript value: at every
V_to_P round the recursion reads the cached challenge back (HIT), at every P_to_V round it splices
in the message.  The cache is left unchanged. -/

/-- **The reconstructed partial transcript** built from messages `m` and a cache, by the same
`Fin.induction` shape as `deriveTranscriptSRAux`: at a V_to_P round read the cache (defaulting if
absent), at a P_to_V round splice in the message. -/
noncomputable def reconstructAux (stmt : StmtIn) (k : Fin (n + 1))
    (messages : pSpec.MessagesUpTo k)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) (j : Fin (k + 1)) :
    pSpec.Transcript (j.castLE (by omega)) :=
  Fin.induction (n := k)
    (fun i => i.elim0)
    (fun i ih =>
      match hDir : pSpec.dir (i.castLE (by omega)) with
      | .V_to_P =>
        ih.concat ((cache ⟨⟨i.castLE (by omega), hDir⟩,
          (stmt, messages.take i.castSucc)⟩).getD
            (Classical.arbitrary (pSpec.Challenge ⟨i.castLE (by omega), hDir⟩)))
      | .P_to_V => ih.concat (messages ⟨i, hDir⟩))
    j

/-- `reconstructAux` at a `succ` index that is a V_to_P round: concatenate the cached challenge. -/
theorem reconstructAux_succ_vtop (stmt : StmtIn) (k : Fin (n + 1))
    (messages : pSpec.MessagesUpTo k)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) (i : Fin k)
    (hDir : pSpec.dir (i.castLE (by omega)) = Direction.V_to_P) :
    reconstructAux (StmtIn := StmtIn) stmt k messages cache i.succ
      = (reconstructAux (StmtIn := StmtIn) stmt k messages cache i.castSucc).concat
          ((cache ⟨⟨i.castLE (by omega), hDir⟩,
            (stmt, messages.take i.castSucc)⟩).getD
              (Classical.arbitrary (pSpec.Challenge ⟨i.castLE (by omega), hDir⟩))) := by
  conv_lhs => rw [reconstructAux, Fin.induction_succ]
  split
  · next hDir' => rfl
  · next hDir' => rw [hDir] at hDir'; exact absurd hDir' (by decide)

/-- `reconstructAux` at a `succ` index that is a P_to_V round: concatenate the message. -/
theorem reconstructAux_succ_ptov (stmt : StmtIn) (k : Fin (n + 1))
    (messages : pSpec.MessagesUpTo k)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) (i : Fin k)
    (hDir : pSpec.dir (i.castLE (by omega)) = Direction.P_to_V) :
    reconstructAux (StmtIn := StmtIn) stmt k messages cache i.succ
      = (reconstructAux (StmtIn := StmtIn) stmt k messages cache i.castSucc).concat
          (messages ⟨i, hDir⟩) := by
  conv_lhs => rw [reconstructAux, Fin.induction_succ]
  split
  · next hDir' => rw [hDir] at hDir'; exact absurd hDir' (by decide)
  · next hDir' => rfl

/-- **Sublemma 1 (lazy `deriveTranscriptSRAux` value lemma).** Under the lazy product impl, with a
cache that contains (at the round-keyed FS keys built from `messages.take`) the prover's challenges,
`deriveTranscriptSRAux` is read-only deterministic and returns exactly `reconstructAux`, leaving the
cache unchanged. The hypothesis `hcache` says every V_to_P key the recursion hits is cached. -/
theorem deriveTranscriptSRAux_lazy_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) (s : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (hcache : ∀ (i : Fin k) (hDir : pSpec.dir (i.castLE (by omega)) = Direction.V_to_P),
      (i : ℕ) < (j : ℕ) →
        cache ⟨⟨i.castLE (by omega), hDir⟩, (stmt, messages.take i.castSucc)⟩ ≠ none) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (MessagesUpTo.deriveTranscriptSRAux (oSpec := oSpec) stmt k messages j)) (s, cache)
      = pure (reconstructAux (StmtIn := StmtIn) stmt k messages cache j, s, cache) := by
  induction j using Fin.induction with
  | zero =>
    simp only [MessagesUpTo.deriveTranscriptSRAux, reconstructAux, Fin.induction_zero,
      simulateQ_pure, StateT.run_pure]
  | succ i ih =>
    have hih := ih (fun i' hDir' hlt => hcache i' hDir' (by
      simp only [Fin.val_succ, Fin.coe_castSucc] at hlt ⊢; omega))
    simp only [MessagesUpTo.deriveTranscriptSRAux] at hih ⊢
    rw [Fin.induction_succ, simulateQ_bind, StateT.run_bind, hih, pure_bind]
    split
    · next hDir =>
      rw [reconstructAux_succ_vtop _ _ _ _ _ hDir]
      have hne : cache ⟨⟨i.castLE (by omega), hDir⟩, (stmt, messages.take i.castSucc)⟩ ≠ none :=
        hcache i hDir (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega)
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
      rw [simulateQ_bind, StateT.run_bind, simulateQ_lazyProd_query_run_hit impl _ s cache u hu,
        pure_bind, simulateQ_pure, StateT.run_pure]
      simp only [hu, Option.getD_some]
    · next hDir =>
      rw [reconstructAux_succ_ptov _ _ _ _ _ hDir, simulateQ_pure, StateT.run_pure]

/-- The full-transcript reconstruction (at `Fin.last`) from messages `m` and a cache. -/
noncomputable def reconstruct (stmt : StmtIn) (messages : pSpec.Messages)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec)) : pSpec.FullTranscript :=
  reconstructAux (StmtIn := StmtIn) stmt (Fin.last n) messages cache
    (Fin.last (Fin.last n).val)

/-- **Sublemma 1, full-transcript form (lazy `deriveTranscriptFS` value lemma).** Under the lazy
product impl, with a cache that holds the prover's challenge at every V_to_P round key (built from
`messages.take`), the FS verifier's transcript derivation `deriveTranscriptFS` is read-only
deterministic and returns exactly the reconstructed full transcript `reconstruct`. -/
theorem deriveTranscriptFS_lazy_run
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmt : StmtIn) (messages : pSpec.Messages) (s : σ)
    (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (hcache : ∀ (i : Fin n) (hDir : pSpec.dir (i.castLE (by omega)) = Direction.V_to_P),
      cache ⟨⟨i.castLE (by omega), hDir⟩, (stmt, messages.take i.castSucc)⟩ ≠ none) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmt messages)) (s, cache)
      = pure (reconstruct (StmtIn := StmtIn) stmt messages cache, s, cache) := by
  show StateT.run (simulateQ _
      (MessagesUpTo.deriveTranscriptSRAux (oSpec := oSpec) stmt (Fin.last n) messages
        (Fin.last (Fin.last n).val))) (s, cache) = _
  rw [deriveTranscriptSRAux_lazy_run impl stmt (Fin.last n) messages
    (Fin.last (Fin.last n).val) s cache (fun i hDir _ => hcache i hDir)]
  rfl

/-! ## Sublemma 2: the lazy `runToRoundFS` cache stores the prover's challenges (all keys cached)

In the support of the lazy-product `runToRoundFS j` run from the empty cache, the output cache holds
*some* value at every V_to_P round key `⟨⟨i, hDir⟩, (stmt, M.take i.castSucc)⟩` for `i < j`, where
`M` is the output messages.  This discharges the `hcache` hypothesis of `deriveTranscriptFS_lazy_run`
at `j = Fin.last n`.  The key step uses prefix-coherence: `processRoundFS` only ever appends, so a
prefix `take i.castSucc` is stable, and the round-`j` key is inserted with messages equal to the
output's `take j.castSucc` (`take_extend_self`). -/

variable (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)

/-- The round-`j` key the prover inserts (V_to_P) is, after the step, cached in the output cache;
moreover any key already cached in the input remains cached.  Support-level statement for one
`processRoundFS j` step. -/
theorem processRoundFS_lazy_cached_step
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (j : Fin n)
    (m : pSpec.MessagesUpTo j.castSucc) (st : P.PrvState j.castSucc)
    (σ' : σ) (cache : QueryCache (fsChallengeOracle StmtIn pSpec))
    (hmiss : ∀ (hDir : pSpec.dir j = Direction.V_to_P),
      cache ⟨⟨j, hDir⟩, (stmt, m)⟩ = none)
    (z : _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hz : z ∈ support (StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (P.processRoundFS j (pure (m, stmt, st)))) (σ', cache))) :
    -- every input-cached key stays cached; the round-`j` V_to_P key becomes cached; and any
    -- prefix `take p` (p ≤ j) of the output messages equals that prefix of the input messages `m`.
    (∀ q, cache q ≠ none → z.2.2 q ≠ none)
      ∧ (∀ (hDir : pSpec.dir j = Direction.V_to_P), z.2.2 ⟨⟨j, hDir⟩, (stmt, m)⟩ ≠ none)
      ∧ ∀ (p : Fin (j.castSucc.val + 1)),
          z.1.1.take (p.castLE (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
            = m.take p := by
  revert hz
  simp only [Prover.processRoundFS, pure_bind]
  split
  · next hDir =>
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_pure, StateT.run_pure,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image]
    rintro ⟨i, ⟨x, _, rfl⟩, i_1, hi1, hzp⟩
    rw [simulateQ_lazyProd_query_run_miss impl ⟨⟨j, hDir⟩, (stmt, m)⟩ x.2 cache
        (hmiss hDir)] at hi1
    simp only [support_map, Set.mem_image] at hi1
    obtain ⟨c, _, rfl⟩ := hi1
    simp only [support_pure, Set.mem_singleton_iff] at hzp
    subst hzp
    simp only []
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      by_cases hqk : q = ⟨⟨j, hDir⟩, (stmt, m)⟩
      · subst hqk; simp
      · rw [QueryCache.cacheQuery_of_ne _ _ hqk]; exact hq
    · intro hDir'
      have : hDir' = hDir := rfl
      subst this; simp
    · exact fun p => take_extend_castLE m hDir p _
  · next hDir =>
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      ← OracleComp.liftComp_eq_liftM, QueryImpl.simulateQ_add_liftComp_left,
      simulateQ_ambientProd_run impl _ σ' cache, simulateQ_pure, StateT.run_pure,
      support_bind, support_map, Set.mem_iUnion, Set.mem_image]
    rintro ⟨i, ⟨x, _, rfl⟩, hzp⟩
    simp only [support_pure, Set.mem_singleton_iff] at hzp
    subst hzp
    refine ⟨fun q hq => hq, fun hDir' => absurd hDir' (by rw [hDir]; decide), ?_⟩
    exact fun p => take_concat_castLE m hDir _ p _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
/-- **Run-level cached-keys lemma.** In the support of the lazy-product `runToRoundFS j` run from the
empty cache, the output cache holds *some* value at every V_to_P round key `⟨⟨i, hDir⟩, (stmt,
M.take i.castSucc)⟩` for `i < j`, where `M` is the output messages.  By `Fin.induction`: the
inductive step transports the IH's cached keys through `processRoundFS_lazy_cached_step` (keys stay
cached; prefixes are stable) and adds the round-`j` key. -/
theorem runToRoundFS_lazy_cached
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (wit : WitIn)
    (j : Fin (n + 1)) (σ' : σ)
    (z : _ × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hz : z ∈ support (StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (P.runToRoundFS j stmt (P.input (stmt, wit)))) (σ', ∅))) :
    ∀ (i : Fin n) (hDir : pSpec.dir i = Direction.V_to_P) (hlt : (i : ℕ) < (j : ℕ)),
      z.2.2 ⟨⟨i, hDir⟩,
        (stmt, z.1.1.take (⟨i.val, by omega⟩ : Fin (j.val + 1)))⟩ ≠ none := by
  induction j using Fin.induction with
  | zero => intro i hDir hlt; exact absurd hlt (by simp)
  | succ j ih =>
    rw [runToRoundFS_succ] at hz
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    -- the carried `stmtIn` and the cache invariant for the intermediate result `w`.
    have hwst : w.1.2.1 = stmt :=
      runToRoundFS_stmt_inv (P := P) (fsImpl := fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (ambImpl := ambientProd (StmtIn := StmtIn) pSpec impl) (stmt := stmt)
        (st0 := P.input (stmt, wit)) (j := j.castSucc) (s0 := (σ', ∅)) (z := w) (hz := hw)
    have hcb : CacheBelow (StmtIn := StmtIn) (pSpec := pSpec) j.castSucc w.2.2 :=
      runToRoundFS_lazy_cacheBelow P impl stmt wit j.castSucc ∅ σ' (cacheBelow_empty 0) w hw
    -- step lemma on `w → z`, using `hwst` to rewrite the carried stmt to `stmt`.
    have hw1 : w.1 = (w.1.1, stmt, w.1.2.2) := by rw [← hwst]
    have hstep := processRoundFS_lazy_cached_step P impl stmt j w.1.1 w.1.2.2 w.2.1 w.2.2
      (fun hDir => cacheBelow_miss_at_round j hDir stmt w.1.1 hcb) z (by
        rw [hw1, show w.2 = (w.2.1, w.2.2) from rfl] at hz; exact hz)
    obtain ⟨hkeep, hnew, hpref⟩ := hstep
    have hjcs : (j.castSucc.val : ℕ) = j.val := by simp [Fin.val_castSucc]
    have hjss : (j.succ.val : ℕ) = j.val + 1 := by simp [Fin.val_succ]
    intro i hDir hlt
    rw [Fin.val_succ] at hlt
    by_cases hij : (i : ℕ) < (j : ℕ)
    · -- old key: cached in `w`, stays cached; prefix stable.
      have hihw := ih w hw i hDir (by simpa using hij)
      have hpi := hpref ⟨i.val, by have := hjcs; omega⟩
      apply hkeep
      -- the goal's carried messages `z.M.take ⟨i.val⟩` equals `w.M.take ⟨i.val⟩` (via `hpi`, routed
      -- through `take_congr` to bridge the index-proof mismatch); rewrite and conclude by `hihw`.
      have hMeq : z.1.1.take (⟨i.val, by omega⟩ : Fin (j.succ.val + 1))
          = w.1.1.take (⟨i.val, by have := hjcs; omega⟩ : Fin (j.castSucc.val + 1)) :=
        eq_of_heq ((take_congr z.1.1
          (p := (⟨i.val, by omega⟩ : Fin (j.succ.val + 1)))
          (q := ((⟨i.val, by have := hjcs; omega⟩ : Fin (j.castSucc.val + 1)).castLE
            (by have := hjcs; have := hjss; omega) : Fin (j.succ.val + 1)))
          (by simp [Fin.val_castLE])).trans (heq_of_eq hpi))
      rw [hMeq]; exact hihw
    · -- new round `i = j`: cached by the step lemma.
      have hij' : (i : ℕ) = (j : ℕ) := by omega
      have hieq : i = j := by apply Fin.ext; simpa using hij'
      have hidir : pSpec.dir j = Direction.V_to_P := by rw [← hieq]; exact hDir
      have hkey := hnew hidir
      have hpj := hpref ⟨i.val, by have := hjcs; omega⟩
      -- `hkey : z.cache ⟨⟨j,hidir⟩, (stmt, w.1.1)⟩ ≠ none`.  Substitute `i = j` so the messages types
      -- align, then `z.M.take ⟨i.val⟩ = w.M.take ⟨i.val⟩ = w.1.1` (full take).
      subst hieq
      have hMeq : z.1.1.take (⟨i.val, by omega⟩ : Fin (i.succ.val + 1)) = w.1.1 :=
        eq_of_heq ((take_congr z.1.1
          (p := (⟨_, by omega⟩ : Fin (i.succ.val + 1)))
          (q := ((⟨_, by have := hjcs; omega⟩ : Fin (i.castSucc.val + 1)).castLE
            (by have := hjcs; have := hjss; omega) : Fin (i.succ.val + 1)))
          (by simp [Fin.val_castLE])).trans ((heq_of_eq hpj).trans
            ((take_congr w.1.1 (p := ⟨_, by have := hjcs; omega⟩)
              (q := Fin.last i.castSucc.val) (by simp only [Fin.val_last]; omega)).trans
              (heq_of_eq (take_last w.1.1)))))
      rw [hMeq]; exact hkey

/-! ## The lazy verifier-leg reconstruction lemma (obligation I, combined)

Combining sublemma 1 (`deriveTranscriptFS_lazy_run`) with sublemma 2 (`runToRoundFS_lazy_cached`):
for *any* output `(M, _, σ', cache)` of the lazy `runToRoundFS (Fin.last n)` run from the empty
cache, the FS verifier's transcript derivation `deriveTranscriptFS` run under the same lazy impl from
that `cache` is read-only deterministic and returns exactly `reconstruct stmt M cache` — i.e. the
verifier reads back the prover's challenges (cache HITs) and reconstructs the prover's full
transcript, leaving the cache unchanged.  This is precisely the lazy verifier leg: after the prover
populated the cache, the verifier's re-derivation is a pure replay. -/
theorem deriveTranscriptFS_lazy_run_of_runOutput
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (stmt : StmtIn) (wit : WitIn) (σ' : σ)
    (z : (pSpec.MessagesUpTo (Fin.last n) × StmtIn × P.PrvState (Fin.last n))
        × (σ × QueryCache (fsChallengeOracle StmtIn pSpec)))
    (hz : z ∈ support (StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl
          + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
      (P.runToRoundFS (Fin.last n) stmt (P.input (stmt, wit)))) (σ', ∅)))
    (s : σ) :
    StateT.run (simulateQ
        (ambientProd (StmtIn := StmtIn) pSpec impl + fsLazyProd (StmtIn := StmtIn) (σ := σ) pSpec)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmt z.1.1)) (s, z.2.2)
      = pure (reconstruct (StmtIn := StmtIn) (pSpec := pSpec) stmt z.1.1 z.2.2, s, z.2.2) := by
  refine deriveTranscriptFS_lazy_run (pSpec := pSpec) impl stmt z.1.1 s z.2.2 (fun i hDir => ?_)
  -- the `hcache` hypothesis is exactly the run-level cached-keys lemma at `j = Fin.last n`
  -- (every V_to_P round `i < n` is cached at the prover's key `(stmt, M.take i.castSucc)`).
  have hlt : (i : ℕ) < ((Fin.last n) : Fin (n + 1)).val := by rw [Fin.val_last]; exact i.isLt
  exact runToRoundFS_lazy_cached P impl stmt wit (Fin.last n) σ' z hz i hDir hlt

-- Axiom audit of the deliverables.
#print axioms deriveTranscriptSRAux_lazy_run
#print axioms processRoundFS_lazy_cached_step
#print axioms take_concat_castLE
#print axioms take_extend_castLE
#print axioms concat_castSucc
#print axioms extend_castSucc
#print axioms deriveTranscriptFS_lazy_run
#print axioms runToRoundFS_lazy_cached
#print axioms deriveTranscriptFS_lazy_run_of_runOutput

end Reduction
