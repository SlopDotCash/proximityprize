/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Flag
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents

/-!
# The log–cache–flag correspondence (CO25 Lemma 5.8, the support-level carrier)

The engine output (`Lemma58Flag.lean`) bounds the probability of the ghost flag; the paper
event `EPaper` lives on the *query log* of the logged run. This file connects them at the
support level. The three log-indexed folds:

* `stepCache` / `cacheOfLog` — the cache is a deterministic fold of the log (first
  occurrence wins; hits change nothing);
* `ConsistentFrom` — every logged answer agrees with the cache at its position (the lazy
  oracle memoizes, so its logs are consistent);
* `AnchoredFrom` — some logged step was fresh and its sampled answer's capacity hit an
  existing slot or its own query's capacity (`collisionStep`).

The master run induction (`support_flagged_logged`) shows every support element of the
flagged run of the logged program satisfies: final cache = fold of the log, the log is
consistent, and the final flag is *exactly* `initial ∨ AnchoredFrom`. The pure
combinatorial part (`¬Anchored ∧ Consistent → ¬EPaper`, via the dedup characterization)
follows in this file's later sections.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace DuplexSpongeFS.EagerLazyDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- A single log entry of the combined oracle. -/
abbrev DSEntry (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
    (duplexSpongeChallengeOracle StmtIn U).Range t

/-- Fold one log entry onto a cache: first occurrence caches, repeats change nothing. -/
def stepCache (c : DSCache StmtIn U) : DSEntry StmtIn U → DSCache StmtIn U
  | ⟨.inl q, u⟩ =>
      match c.1 q with
      | none => (c.1.cacheQuery q u, c.2)
      | some _ => c
  | ⟨.inr (.inl a), b⟩ =>
      match c.2.find? (fun w => w.1 = a) with
      | none => (c.1, c.2.concat (a, b))
      | some _ => c
  | ⟨.inr (.inr b), a⟩ =>
      match c.2.find? (fun w => w.2 = b) with
      | none => (c.1, c.2.concat (a, b))
      | some _ => c

/-- A log entry agrees with a cache: if its query is cached, the logged answer is the
cached one. -/
def entryConsistent (c : DSCache StmtIn U) : DSEntry StmtIn U → Prop
  | ⟨.inl q, u⟩ => ∀ u', c.1 q = some u' → u = u'
  | ⟨.inr (.inl a), b⟩ => ∀ w, c.2.find? (fun w => w.1 = a) = some w → b = w.2
  | ⟨.inr (.inr b), a⟩ => ∀ w, c.2.find? (fun w => w.2 = b) = some w → a = w.1

/-- The whole log is consistent with the running cache. -/
def ConsistentFrom (c : DSCache StmtIn U) : List (DSEntry StmtIn U) → Prop
  | [] => True
  | e :: ℓ => entryConsistent c e ∧ ConsistentFrom (stepCache c e) ℓ

/-- Some entry of the log is an anchored collision against the running cache. -/
def AnchoredFrom (c : DSCache StmtIn U) : List (DSEntry StmtIn U) → Prop
  | [] => False
  | e :: ℓ => collisionStep e.1 c e.2 ∨ AnchoredFrom (stepCache c e) ℓ

/-- **The per-step support facts**: each reachable one-step outcome of the flagged oracle
has the folded cache, a consistent entry, and the exact flag update. -/
theorem lazyDSImplFlagged_step_support
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s),
      us.2.1 = stepCache s.1 ⟨t, us.1⟩ ∧ entryConsistent s.1 ⟨t, us.1⟩ ∧
        (us.2.2 ↔ (s.2 ∨ collisionStep t s.1 us.1)) := by
  classical
  obtain ⟨⟨ch, cp⟩, fl⟩ := s
  intro us hus
  rw [lazyDSImplFlagged_run] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, hw, rfl⟩ := hus
  refine ⟨?_, ?_, Iff.rfl⟩ <;> rcases t with q | sIn | sOut
  · -- hash arm, cache shape
    rcases hcq : ch q with _ | u
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_none _ hcq, Functor.map_map] at hw
      have hw' : w ∈ support ((fun a => (a, (ch.cacheQuery q a, cp))) <$>
          ($ᵗ (Vector U SpongeSize.C))) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨u, _, rfl⟩ := hw'
      simp [stepCache, hcq]
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_some _ hcq, map_pure] at hw
      have hw2 : w = ((u : Vector U SpongeSize.C), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcq]
  · rcases hcfind : cp.find? (fun w => w.1 = sIn) with _ | w₀
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_none cp hcfind,
        Functor.map_map] at hw
      have hw' : w ∈ support ((fun b => (b, (ch, cp.concat (sIn, b)))) <$>
          LazyPermBridge.sampleUnused (LazyPermBridge.unusedValuesList cp)) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨b, _, rfl⟩ := hw'
      simp [stepCache, hcfind]
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.2 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcfind]
  · rcases hcfind : cp.find? (fun w => w.2 = sOut) with _ | w₀
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_none cp hcfind,
        Functor.map_map] at hw
      have hw' : w ∈ support ((fun a => (a, (ch, cp.concat (a, sOut)))) <$>
          LazyPermBridge.sampleUnused (LazyPermBridge.unusedKeysList cp)) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨a, _, rfl⟩ := hw'
      simp [stepCache, hcfind]
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.1 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcfind]
  · -- hash arm, consistency
    rcases hcq : ch q with _ | u
    · intro u' hu'
      replace hu' : ch q = some u' := hu'
      rw [hcq] at hu'
      exact absurd hu' (by simp)
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_some _ hcq, map_pure] at hw
      have hw2 : w = ((u : Vector U SpongeSize.C), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro u' hu'
      replace hu' : ch q = some u' := hu'
      rw [hcq] at hu'
      exact Option.some_inj.mp hu'
  · rcases hcfind : cp.find? (fun w => w.1 = sIn) with _ | w₀
    · intro w' hw'
      replace hw' : cp.find? (fun w => w.1 = sIn) = some w' := hw'
      rw [hcfind] at hw'
      exact absurd hw' (by simp)
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.2 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro w' hw'
      replace hw' : cp.find? (fun w => w.1 = sIn) = some w' := hw'
      rw [hcfind] at hw'
      rw [Option.some_inj.mp hw']
  · rcases hcfind : cp.find? (fun w => w.2 = sOut) with _ | w₀
    · intro w' hw'
      replace hw' : cp.find? (fun w => w.2 = sOut) = some w' := hw'
      rw [hcfind] at hw'
      exact absurd hw' (by simp)
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.1 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro w' hw'
      replace hw' : cp.find? (fun w => w.2 = sOut) = some w' := hw'
      rw [hcfind] at hw'
      rw [Option.some_inj.mp hw']

/-- **The master run correspondence**: every support element of the flagged run of the
logged program has its final cache equal to the fold of its log, a consistent log, and a
final flag exactly `initial ∨ AnchoredFrom`. -/
theorem support_flagged_logged {α : Type}
    (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (c₀ : DSCache StmtIn U) (fl₀ : Prop) :
    ∀ xs ∈ support ((simulateQ lazyDSImplFlagged
        ((simulateQ loggingOracle P).run)).run (c₀, fl₀)),
      xs.2.1 = xs.1.2.foldl stepCache c₀ ∧
      ConsistentFrom c₀ xs.1.2 ∧
      (xs.2.2 ↔ (fl₀ ∨ AnchoredFrom c₀ xs.1.2)) := by
  induction P using OracleComp.inductionOn generalizing c₀ fl₀ with
  | pure a =>
      intro xs hxs
      rw [show ((simulateQ loggingOracle (pure a :
            OracleComp (duplexSpongeChallengeOracle StmtIn U) α)).run)
          = pure (a, ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))) from by
        simp [simulateQ_pure]] at hxs
      rw [simulateQ_pure, StateT.run_pure] at hxs
      have hxs2 : xs = ((a, ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))),
          (c₀, fl₀)) := by
        have hxs' : xs ∈ support ((pure ((a,
            ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))),
            (c₀, fl₀)) : ProbComp _)) := hxs
        rw [support_pure] at hxs'
        exact hxs'
      subst hxs2
      exact ⟨rfl, trivial, by tauto⟩
  | query_bind t k ih =>
      intro xs hxs
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hxs
      rw [simulateQ_bind, StateT.run_bind] at hxs
      rw [show (simulateQ lazyDSImplFlagged
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run (c₀, fl₀)
          = (lazyDSImplFlagged t).run (c₀, fl₀) from by
        refine congrArg (fun z => StateT.run z (c₀, fl₀)) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map]] at hxs
      obtain ⟨us, hus, hxs2⟩ := (mem_support_bind_iff _ _ _).1 hxs
      obtain ⟨hcache, hcons, hflag⟩ := lazyDSImplFlagged_step_support t (c₀, fl₀) us hus
      rw [simulateQ_map, StateT.run_map] at hxs2
      simp only [support_map, Set.mem_image] at hxs2
      obtain ⟨w, hw, rfl⟩ := hxs2
      obtain ⟨ih1, ih2, ih3⟩ := ih us.1 us.2.1 us.2.2 w hw
      refine ⟨?_, ⟨hcons, ?_⟩, ?_⟩
      · rw [List.foldl_cons, ← hcache]
        exact ih1
      · rw [← hcache]
        exact ih2
      · rw [show AnchoredFrom c₀
            ((⟨t, us.1⟩ : DSEntry StmtIn U) :: w.1.2)
            = (collisionStep t c₀ us.1 ∨ AnchoredFrom (stepCache c₀ ⟨t, us.1⟩) w.1.2)
          from rfl, ← hcache]
        rw [ih3, hflag]
        tauto

/-! ## The entry-class structure (pure list combinatorics)

CO25's redundancy certificates partition entries into classes of size at most two:
a hash entry is its own class; a permutation entry is classed with its opposite-direction
swap. The dedup procedure keeps exactly the first occurrence of each class. -/

/-- The opposite-direction form of an entry (hash entries are self-paired). -/
def swapEntry : DSEntry StmtIn U → DSEntry StmtIn U
  | ⟨.inl q, u⟩ => ⟨.inl q, u⟩
  | ⟨.inr (.inl a), b⟩ => ⟨.inr (.inr b), a⟩
  | ⟨.inr (.inr b), a⟩ => ⟨.inr (.inl a), b⟩

@[simp] lemma swapEntry_swapEntry (e : DSEntry StmtIn U) :
    swapEntry (swapEntry e) = e := by
  rcases e with ⟨t, ans⟩
  rcases t with q | sIn | sOut <;> rfl

/-- Class membership: equal or the swap. -/
def sameClass (e e' : DSEntry StmtIn U) : Prop :=
  e' = e ∨ e' = swapEntry e

lemma sameClass_refl (e : DSEntry StmtIn U) : sameClass e e := Or.inl rfl

lemma sameClass_symm {e e' : DSEntry StmtIn U} (h : sameClass e e') : sameClass e' e := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (swapEntry_swapEntry e).symm

lemma sameClass_trans {e₁ e₂ e₃ : DSEntry StmtIn U}
    (h₁ : sameClass e₁ e₂) (h₂ : sameClass e₂ e₃) : sameClass e₁ e₃ := by
  rcases h₁ with rfl | rfl
  · exact h₂
  · rcases h₂ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (swapEntry_swapEntry e₁)

/-- The paper redundancy predicate is exactly "an earlier class member exists". -/
lemma redundantEntryDSPaper_iff_sameClass
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin log.length) :
    DuplexSpongeFS.Paper.redundantEntryDSPaper log idx
      ↔ ∃ j' < idx, sameClass log[idx] log[j'] := by
  unfold DuplexSpongeFS.Paper.redundantEntryDSPaper
  rcases hidx : log[idx] with ⟨t, ans⟩
  rcases t with q | sIn | sOut
  · constructor
    · rintro ⟨j', hj', hej'⟩
      exact ⟨j', hj', Or.inl hej'⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', hcl⟩
      · exact ⟨j', hj', hcl⟩
  · constructor
    · rintro ⟨j', hj', hej'⟩
      rcases hej' with h | h
      · exact ⟨j', hj', Or.inl h⟩
      · exact ⟨j', hj', Or.inr h⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', Or.inl hcl⟩
      · exact ⟨j', hj', Or.inr hcl⟩
  · constructor
    · rintro ⟨j', hj', hej'⟩
      rcases hej' with h | h
      · exact ⟨j', hj', Or.inl h⟩
      · exact ⟨j', hj', Or.inr h⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', Or.inl hcl⟩
      · exact ⟨j', hj', Or.inr hcl⟩

/-! ## Fold monotonicity primitives -/

/-- The permutation cache only grows (as a sublist) along one fold step. -/
theorem stepCache_perm_sublist (c : DSCache StmtIn U) (e : DSEntry StmtIn U) :
    c.2.Sublist (stepCache c e).2 := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a | b
  · rcases hcq : c.1 q with _ | u <;> simp [stepCache, hcq]
  · rcases hf : c.2.find? (fun w => w.1 = a) with _ | w <;>
      simp only [stepCache, hf]
    · rw [List.concat_eq_append]; exact List.sublist_append_left _ _
    · exact List.Sublist.refl _
  · rcases hf : c.2.find? (fun w => w.2 = b) with _ | w <;>
      simp only [stepCache, hf]
    · rw [List.concat_eq_append]; exact List.sublist_append_left _ _
    · exact List.Sublist.refl _

/-- The hash cache only grows: an already-cached answer survives one fold step. -/
theorem stepCache_hash_mono (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    (stepCache c e).1 q = some u := by
  rcases e with ⟨t, ans⟩
  rcases t with q' | a | b
  · rcases hcq : c.1 q' with _ | u' <;> simp only [stepCache, hcq]
    · rcases eq_or_ne q q' with rfl | hne
      · rw [hcq] at h; exact absurd h (by simp)
      · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne]; exact h
    · exact h
  · rcases hf : c.2.find? (fun w => w.1 = a) with _ | w <;> simp only [stepCache, hf] <;> exact h
  · rcases hf : c.2.find? (fun w => w.2 = b) with _ | w <;> simp only [stepCache, hf] <;> exact h

/-- The permutation cache only grows along the whole fold. -/
theorem foldl_stepCache_perm_sublist (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U)) :
    c.2.Sublist (L.foldl stepCache c).2 := by
  induction L generalizing c with
  | nil => exact List.Sublist.refl _
  | cons e ℓ ih =>
      rw [List.foldl_cons]
      exact (stepCache_perm_sublist c e).trans (ih (stepCache c e))

/-! ## Key-existence characterization of the fold (consistency-free) -/

/-- Whether a permutation cache already holds the forward key `a`. -/
def hasFwdKey (c : DSCache StmtIn U) (a : CanonicalSpongeState U) : Prop :=
  ∃ w ∈ c.2, w.1 = a

/-- Whether a permutation cache already holds the inverse key `b`. -/
def hasInvKey (c : DSCache StmtIn U) (b : CanonicalSpongeState U) : Prop :=
  ∃ w ∈ c.2, w.2 = b

/-- The forward key inserted by an entry (`none` for a hash entry). -/
def entryFwdKey : DSEntry StmtIn U → Option (CanonicalSpongeState U)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl a), _⟩ => some a
  | ⟨.inr (.inr _), a⟩ => some a

/-- The inverse key inserted by an entry (`none` for a hash entry). For a forward entry
`⟨inr (inl a), b⟩` the inserted pair is `(a, b)` so the inverse key is its answer `b`; for an
inverse entry `⟨inr (inr b), a⟩` the inserted pair is `(a, b)` so the inverse key is its
query `b`. -/
def entryInvKey : DSEntry StmtIn U → Option (CanonicalSpongeState U)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl _), b⟩ => some b
  | ⟨.inr (.inr b), _⟩ => some b

/-- One fold step can only create the inverse key it inserts (sound direction only). -/
theorem hasInvKey_stepCache_imp (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    (b : CanonicalSpongeState U) (h : hasInvKey (stepCache c e) b) :
    hasInvKey c b ∨ entryInvKey e = some b := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · -- hash entry: perm cache unchanged
    left
    obtain ⟨w, hw, hwb⟩ := h
    rcases hcq : c.1 q with _ | u
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwb⟩
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwb⟩
  · -- forward entry inserts pair (a', ans); inverse key = ans
    rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwb'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwb'⟩
  · -- inverse entry inserts pair (ans, b'); inverse key = b'
    rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwb'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwb'⟩

/-- One fold step can only create the forward key it inserts: if a key is present after the
step but not before, the step's entry inserts exactly that key. (The reverse is false for
cache *hits* without a consistency assumption, so only this sound direction is stated.) -/
theorem hasFwdKey_stepCache_imp (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    (a : CanonicalSpongeState U) (h : hasFwdKey (stepCache c e) a) :
    hasFwdKey c a ∨ entryFwdKey e = some a := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · -- hash entry: perm cache unchanged
    left
    obtain ⟨w, hw, hwa⟩ := h
    rcases hcq : c.1 q with _ | u
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwa⟩
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwa⟩
  · -- forward entry inserts pair (a', ans)
    rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwa'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwa'⟩
  · -- inverse entry inserts pair (ans, b')
    rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwa'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwa'⟩

/-- A forward key present after the whole fold was either present at the start or inserted
by some entry of the log. -/
theorem hasFwdKey_foldl_imp (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    (a : CanonicalSpongeState U) (h : hasFwdKey (L.foldl stepCache c) a) :
    hasFwdKey c a ∨ ∃ e ∈ L, entryFwdKey e = some a := by
  induction L generalizing c with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rw [List.foldl_cons] at h
      rcases ih (stepCache c e) h with h' | ⟨e', he', hk'⟩
      · rcases hasFwdKey_stepCache_imp c e a h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-- An inverse key present after the whole fold was present at the start or inserted by
some entry of the log. -/
theorem hasInvKey_foldl_imp (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    (b : CanonicalSpongeState U) (h : hasInvKey (L.foldl stepCache c) b) :
    hasInvKey c b ∨ ∃ e ∈ L, entryInvKey e = some b := by
  induction L generalizing c with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rw [List.foldl_cons] at h
      rcases ih (stepCache c e) h with h' | ⟨e', he', hk'⟩
      · rcases hasInvKey_stepCache_imp c e b h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-! ## Dedup preserves every class (piece A1) -/

open DuplexSpongeFS.Paper in
/-- **Dedup is a system of class representatives**: every entry of the raw log has a
class-representative surviving in the dedup output. (The output is also pairwise
class-distinct, so it is exactly one representative per class.) -/
theorem mem_imp_sameClass_mem_removeRedundant
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (e : DSEntry StmtIn U) (he : e ∈ log) :
    ∃ e' ∈ (removeRedundantEntryDSPaper log).1, sameClass e e' := by
  letI : Decidable (∃ idx : Fin log.length,
      DuplexSpongeFS.Paper.redundantEntryDSPaper log idx) := Classical.propDecidable _
  rw [removeRedundantEntryDSPaper]
  by_cases h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
  · rw [dif_pos h]
    set i := (Classical.choose h).val with hi
    have hilt : i < log.length := (Classical.choose h).isLt
    by_cases hmem : e ∈ log.eraseIdx i
    · obtain ⟨e'', hmem'', hcl''⟩ :=
        mem_imp_sameClass_mem_removeRedundant (log.eraseIdx i) e hmem
      exact ⟨e'', hmem'', hcl''⟩
    · -- e ∈ log but not in eraseIdx i: every occurrence of e is at index i, so e = log[i]
      have hek : e = log[i] := by
        obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
        by_cases hki : k = i
        · subst hki; exact hke.symm
        · exact absurd (List.mem_eraseIdx_iff_getElem.mpr ⟨k, hk, hki, hke⟩) hmem
      -- log[i] is redundant: it has an earlier same-class witness at j' ≠ i
      have hred : redundantEntryDSPaper log (Classical.choose h) := Classical.choose_spec h
      obtain ⟨j', hj', hclj'⟩ :=
        (redundantEntryDSPaper_iff_sameClass log (Classical.choose h)).mp hred
      have hj'i : (j' : ℕ) ≠ i := by
        rw [hi]; exact Nat.ne_of_lt hj'
      have hwitmem : log[(j' : ℕ)] ∈ log.eraseIdx i :=
        List.mem_eraseIdx_iff_getElem.mpr ⟨(j' : ℕ), j'.isLt, hj'i, rfl⟩
      obtain ⟨e'', hmem'', hcl''⟩ :=
        mem_imp_sameClass_mem_removeRedundant (log.eraseIdx i) log[(j' : ℕ)] hwitmem
      refine ⟨e'', hmem'', ?_⟩
      -- sameClass e log[j'] from hclj' (sameClass log[i] log[j']) and e = log[i]
      have hcl_e : sameClass e log[(j' : ℕ)] := by
        rw [hek]; exact hclj'
      exact sameClass_trans hcl_e hcl''
  · rw [dif_neg h]
    exact ⟨e, he, sameClass_refl e⟩
termination_by log.length
decreasing_by
  all_goals
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega

/-! ## Key pair pins the class -/

/-- An entry whose inserted pair is `(a, b)` is class-equal to the forward entry
`⟨inr (inl a), b⟩`: it is either that entry or its inverse swap. -/
theorem sameClass_of_entryKeys
    {e' : DSEntry StmtIn U} {a b : CanonicalSpongeState U}
    (hf : entryFwdKey e' = some a) (hi : entryInvKey e' = some b) :
    sameClass (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) e' := by
  rcases e' with ⟨t, ans⟩
  rcases t with q | a' | b'
  · simp only [entryFwdKey] at hf; exact absurd hf (by simp)
  · -- forward ⟨inr (inl a'), ans⟩: fwd-key a', inv-key ans
    simp only [entryFwdKey] at hf
    simp only [entryInvKey] at hi
    rw [Option.some_inj] at hf hi
    subst hf; subst hi
    exact Or.inl rfl
  · -- inverse ⟨inr (inr b'), ans⟩: fwd-key ans, inv-key b'
    simp only [entryFwdKey] at hf
    simp only [entryInvKey] at hi
    rw [Option.some_inj] at hf hi
    subst hf; subst hi
    -- e' = ⟨inr (inr b), a⟩ = swapEntry ⟨inr (inl a), b⟩
    exact Or.inr rfl

/-! ## Capacity-freshness from non-anchoredness (piece B) -/

/-- Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision. -/
theorem not_anchoredFrom_cons {c : DSCache StmtIn U} {e : DSEntry StmtIn U}
    {ℓ : List (DSEntry StmtIn U)} (h : ¬ AnchoredFrom c (e :: ℓ)) :
    ¬ collisionStep e.1 c e.2 ∧ ¬ AnchoredFrom (stepCache c e) ℓ := by
  rw [AnchoredFrom, not_or] at h
  exact h

/-- A fresh forward step that is not an anchored collision yields an answer capacity that is
neither an existing slot nor the query's own capacity. -/
theorem fwd_fresh_cap_new {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w => w.1 = a) = none)
    (hnc : ¬ collisionStep (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U).1 c
            (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U).2) :
    b.capacitySegment ∉ slotList c ∧ b.capacitySegment ≠ a.capacitySegment := by
  simp only [collisionStep, hfresh, true_and, not_or] at hnc
  exact hnc

/-- A fresh inverse step that is not an anchored collision yields an answer capacity that is
neither an existing slot nor the query's own capacity. -/
theorem inv_fresh_cap_new {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w => w.2 = b) = none)
    (hnc : ¬ collisionStep (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U).1 c
            (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U).2) :
    a.capacitySegment ∉ slotList c ∧ a.capacitySegment ≠ b.capacitySegment := by
  simp only [collisionStep, hfresh, true_and, not_or] at hnc
  exact hnc

/-- A fresh hash step that is not an anchored collision yields an answer that is not an
existing slot. -/
theorem hash_fresh_ans_new {c : DSCache StmtIn U}
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (hfresh : c.1 q = none)
    (hnc : ¬ collisionStep (⟨.inl q, u⟩ : DSEntry StmtIn U).1 c
            (⟨.inl q, u⟩ : DSEntry StmtIn U).2) :
    u ∉ slotList c := by
  simp only [collisionStep, hfresh, true_and] at hnc
  exact hnc

/-! ## Dedup recursion infrastructure (sublist + membership transport) -/

open DuplexSpongeFS.Paper in
/-- The paper dedup output is a sublist of its input (each step erases one entry). -/
theorem removeRedundantEntryDSPaper_sublist
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (removeRedundantEntryDSPaper log).1.Sublist log := by
  letI : Decidable (∃ idx : Fin log.length,
      DuplexSpongeFS.Paper.redundantEntryDSPaper log idx) := Classical.propDecidable _
  rw [removeRedundantEntryDSPaper]
  by_cases h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
  · rw [dif_pos h]
    exact (removeRedundantEntryDSPaper_sublist
      (log.eraseIdx (Classical.choose h).val)).trans (List.eraseIdx_sublist _ _)
  · rw [dif_neg h]
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

open DuplexSpongeFS.Paper in
/-- Every entry of the dedup'd base trace was already an entry of the original log. -/
theorem mem_of_mem_removeRedundantEntryDSPaper
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e : DSEntry StmtIn U} (he : e ∈ (removeRedundantEntryDSPaper log).1) :
    e ∈ log :=
  (removeRedundantEntryDSPaper_sublist log).subset he

open DuplexSpongeFS.Paper in
/-- A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a
class with any earlier one. -/
theorem noRedundant_pairwise_classDistinct
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : NoRedundantEntryDSPaper base)
    (i j : Fin base.length) (hij : i < j) :
    ¬ sameClass base[j] base[i] := by
  intro hcl
  exact h j ((redundantEntryDSPaper_iff_sameClass base j).mpr ⟨i, hij, hcl⟩)

open DuplexSpongeFS.Paper in
/-- The dedup output is pairwise class-distinct. -/
theorem removeRedundantEntryDSPaper_pairwise_classDistinct
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (i j : Fin (removeRedundantEntryDSPaper log).1.length) (hij : i < j) :
    ¬ sameClass (removeRedundantEntryDSPaper log).1[j]
        (removeRedundantEntryDSPaper log).1[i] :=
  noRedundant_pairwise_classDistinct (removeRedundantEntryDSPaper log).2 i j hij

/-! ## Slot-list membership of cached capacities -/

/-- Both capacities of a cached permutation pair are slots. -/
theorem mem_slotList_of_mem_perm (c : DSCache StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (hp : p ∈ c.2) :
    p.1.capacitySegment ∈ slotList c ∧ p.2.capacitySegment ∈ slotList c := by
  classical
  constructor <;>
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, ?_⟩)
    simp

/-- A capacity cached early stays a slot of every later fold cache. -/
theorem mem_slotList_foldl_of_mem_perm (c : DSCache StmtIn U)
    (L : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (hp : p ∈ c.2) :
    p.1.capacitySegment ∈ slotList (L.foldl stepCache c) ∧
      p.2.capacitySegment ∈ slotList (L.foldl stepCache c) :=
  mem_slotList_of_mem_perm _ ((foldl_stepCache_perm_sublist c L).subset hp)

/-! ## Forward/inverse key uniqueness along a non-anchored fold

Forward-key uniqueness is NOT a pure property of `stepCache`: an inverse-fresh step inserts
its sampled answer as a new forward key, which could a priori coincide with an existing one.
But that coincidence is exactly an anchored collision (the answer's capacity equals an
existing slot's), so along a *non-anchored* fold the forward keys stay distinct. -/

/-- The forward keys of the permutation cache are distinct. -/
def FwdKeysNodup (c : DSCache StmtIn U) : Prop := (c.2.map Prod.fst).Nodup

lemma not_hasFwdKey_of_find?_none {c : DSCache StmtIn U} {a : CanonicalSpongeState U}
    (h : c.2.find? (fun w => w.1 = a) = none) : a ∉ c.2.map Prod.fst := by
  intro hmem
  obtain ⟨w, hw, hwa⟩ := List.mem_map.mp hmem
  exact absurd (by simpa using List.find?_eq_none.mp h w hw) (by simp [hwa])

/-- A state whose capacity is not a slot is not a cached forward key. -/
lemma not_mem_fwdKeys_of_cap_not_slot (c : DSCache StmtIn U)
    {x : CanonicalSpongeState U} (h : x.capacitySegment ∉ slotList c) :
    x ∉ c.2.map Prod.fst := by
  intro hmem
  obtain ⟨w, hw, hwx⟩ := List.mem_map.mp hmem
  exact h (hwx ▸ (mem_slotList_of_mem_perm c hw).1)

/-- One non-anchored fold step preserves forward-key distinctness. -/
theorem stepCache_fwdNodup (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    (hnc : ¬ collisionStep e.1 c e.2) (h : FwdKeysNodup c) :
    FwdKeysNodup (stepCache c e) := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · rcases hcq : c.1 q with _ | u <;> simpa [stepCache, hcq, FwdKeysNodup] using h
  · rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · simp only [stepCache, hf, FwdKeysNodup, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil]
      rw [← List.concat_eq_append]
      exact (List.nodup_concat _ _).mpr ⟨not_hasFwdKey_of_find?_none hf, h⟩
    · simpa [stepCache, hf, FwdKeysNodup] using h
  · rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · -- inverse-fresh inserts pair (ans, b'); forward key = ans. ¬anchored ⟹ ans.cap ∉ slot
      have hcap : ans.capacitySegment ∉ slotList c := by
        simp only [collisionStep, hf, true_and, not_or] at hnc
        exact hnc.1
      simp only [stepCache, hf, FwdKeysNodup, List.concat_eq_append, List.map_append,
        List.map_cons, List.map_nil]
      rw [← List.concat_eq_append]
      exact (List.nodup_concat _ _).mpr ⟨not_mem_fwdKeys_of_cap_not_slot c hcap, h⟩
    · simpa [stepCache, hf, FwdKeysNodup] using h

/-- Forward-key distinctness is preserved along a whole non-anchored fold. -/
theorem foldl_stepCache_fwdNodup (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    (hna : ¬ AnchoredFrom c L) (h : FwdKeysNodup c) :
    FwdKeysNodup (L.foldl stepCache c) := by
  induction L generalizing c with
  | nil => exact h
  | cons e ℓ ih =>
      obtain ⟨hnc, hna'⟩ := not_anchoredFrom_cons hna
      rw [List.foldl_cons]
      exact ih (stepCache c e) hna' (stepCache_fwdNodup c e hnc h)

/-! ## Pair provenance and the consistency glue (piece A2c) -/

/-- **Pair provenance (one step)**: a pair in the cache after a step was already there or
was inserted by the step's entry, whose key-pair then matches it. No hypotheses. -/
theorem stepCache_pair_provenance (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (hp : p ∈ (stepCache c e).2) :
    p ∈ c.2 ∨ (entryFwdKey e = some p.1 ∧ entryInvKey e = some p.2) := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · rcases hcq : c.1 q with _ | u <;>
      · left; simpa [stepCache, hcq] using hp
  · rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · simp only [stepCache, hf, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · subst hp; exact Or.inr ⟨rfl, rfl⟩
    · left; simpa [stepCache, hf] using hp
  · rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · simp only [stepCache, hf, List.concat_eq_append, List.mem_append,
        List.mem_singleton] at hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · subst hp; exact Or.inr ⟨rfl, rfl⟩
    · left; simpa [stepCache, hf] using hp

/-- **Pair provenance (whole fold)**: a pair in the final cache was in the start cache or
inserted by some log entry whose key-pair matches it. -/
theorem foldl_pair_provenance (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U}
    (hp : p ∈ (L.foldl stepCache c).2) :
    p ∈ c.2 ∨ ∃ e ∈ L, entryFwdKey e = some p.1 ∧ entryInvKey e = some p.2 := by
  induction L generalizing c with
  | nil => exact Or.inl hp
  | cons e ℓ ih =>
      rw [List.foldl_cons] at hp
      rcases ih (stepCache c e) hp with hp' | ⟨e', he', hk'⟩
      · rcases stepCache_pair_provenance c e hp' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-- A consistent forward hit puts the entry's exact pair in the cache: if the running cache
already holds the forward key `a` and the entry `⟨inr (inl a), b⟩` is consistent with it,
then `(a, b)` is itself a cached pair. -/
theorem consistent_fwd_hit_pair_mem (c : DSCache StmtIn U) (a b : CanonicalSpongeState U)
    (hcons : entryConsistent c (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U))
    (hhit : hasFwdKey c a) :
    (a, b) ∈ c.2 := by
  obtain ⟨w, hw, hwa⟩ := hhit
  rcases hf : c.2.find? (fun w => w.1 = a) with _ | w₀
  · exact absurd ((List.find?_eq_none).mp hf w hw) (by simp [hwa])
  · have hmem₀ : w₀ ∈ c.2 := List.mem_of_find?_eq_some hf
    have hkey₀ : w₀.1 = a := by simpa using List.find?_some hf
    have hb : b = w₀.2 := hcons w₀ hf
    have : (a, b) = w₀ := Prod.ext hkey₀.symm hb
    rw [this]; exact hmem₀

/-- **Piece (A2c)**: in a fold from empty over `L`, a consistent forward entry
`⟨inr (inl a), b⟩` whose forward key is already cached has an earlier same-class entry in
`L`. -/
theorem fwd_hit_sameClass_mem (L : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (hcons : entryConsistent (L.foldl stepCache ((∅, []) : DSCache StmtIn U))
      (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U))
    (hhit : hasFwdKey (L.foldl stepCache ((∅, []) : DSCache StmtIn U)) a) :
    ∃ e' ∈ L, sameClass (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) e' := by
  have hpair : (a, b) ∈ (L.foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    consistent_fwd_hit_pair_mem _ a b hcons hhit
  rcases foldl_pair_provenance (∅, []) L hpair with hp | ⟨e', he', hf', hi'⟩
  · simp at hp
  · exact ⟨e', he', sameClass_of_entryKeys hf' hi'⟩

/-- A consistent inverse hit puts the entry's exact pair in the cache. -/
theorem consistent_inv_hit_pair_mem (c : DSCache StmtIn U) (a b : CanonicalSpongeState U)
    (hcons : entryConsistent c (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U))
    (hhit : hasInvKey c b) :
    (a, b) ∈ c.2 := by
  obtain ⟨w, hw, hwb⟩ := hhit
  rcases hf : c.2.find? (fun w => w.2 = b) with _ | w₀
  · exact absurd ((List.find?_eq_none).mp hf w hw) (by simp [hwb])
  · have hmem₀ : w₀ ∈ c.2 := List.mem_of_find?_eq_some hf
    have hkey₀ : w₀.2 = b := by simpa using List.find?_some hf
    have ha : a = w₀.1 := hcons w₀ hf
    have : (a, b) = w₀ := Prod.ext ha hkey₀.symm
    rw [this]; exact hmem₀

/-- **Piece (A2c), inverse arm**: in a fold from empty over `L`, a consistent inverse entry
`⟨inr (inr b), a⟩` whose inverse key is already cached has an earlier same-class entry. -/
theorem inv_hit_sameClass_mem (L : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (hcons : entryConsistent (L.foldl stepCache ((∅, []) : DSCache StmtIn U))
      (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U))
    (hhit : hasInvKey (L.foldl stepCache ((∅, []) : DSCache StmtIn U)) b) :
    ∃ e' ∈ L, sameClass (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U) e' := by
  have hpair : (a, b) ∈ (L.foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    consistent_inv_hit_pair_mem _ a b hcons hhit
  rcases foldl_pair_provenance (∅, []) L hpair with hp | ⟨e', he', hf', hi'⟩
  · simp at hp
  · -- e' is same-class with the forward query ⟨inr inl a, b⟩, whose swap is our entry
    have h1 : sameClass (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) e' :=
      sameClass_of_entryKeys hf' hi'
    have h2 : sameClass (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)
        (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) := Or.inr rfl
    exact ⟨e', he', sameClass_trans h2 h1⟩

/-! ## Per-position extraction from the fold predicates -/

/-- `ConsistentFrom` gives entry-consistency at every split point against the fold cache of
the prefix. -/
theorem consistentFrom_split (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U) (L₂ : List (DSEntry StmtIn U))
    (h : ConsistentFrom c (L₁ ++ e :: L₂)) :
    entryConsistent (L₁.foldl stepCache c) e := by
  induction L₁ generalizing c with
  | nil => exact h.1
  | cons e₁ ℓ ih =>
      rw [List.cons_append, ConsistentFrom] at h
      rw [List.foldl_cons]
      exact ih (stepCache c e₁) h.2

/-- `¬ AnchoredFrom` gives non-collision at every split point against the fold cache of the
prefix. -/
theorem not_anchoredFrom_split (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U) (L₂ : List (DSEntry StmtIn U))
    (h : ¬ AnchoredFrom c (L₁ ++ e :: L₂)) :
    ¬ collisionStep e.1 (L₁.foldl stepCache c) e.2 := by
  induction L₁ generalizing c with
  | nil => exact (not_anchoredFrom_cons h).1
  | cons e₁ ℓ ih =>
      rw [List.cons_append] at h
      rw [List.foldl_cons]
      exact ih (stepCache c e₁) (not_anchoredFrom_cons h).2

/-! ## Order embedding of the dedup base trace into the raw log (assembly step s1) -/

open DuplexSpongeFS.Paper in
/-- The dedup base trace embeds into the raw log by a strictly monotone index map that
preserves entries. The order-preserving correspondence used to relate base-trace indices to
raw-fold positions. -/
theorem removeRedundant_orderEmbedding
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ,
      (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]? :=
  List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp
    (removeRedundantEntryDSPaper_sublist log)

/-! ## Freshness of non-redundant permutation entries (assembly step s2) -/

/-- **A non-redundant forward entry is fresh.** If `⟨inr (inl a), b⟩` occurs in a consistent
log with no earlier same-class entry, its forward key is not yet cached at its position. -/
theorem fwd_entry_fresh (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U)
    (L₂ : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (he : e = (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ e :: L₂))
    (hnr : ∀ e' ∈ L₁, ¬ sameClass e e') :
    ¬ hasFwdKey (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)) a := by
  intro hhit
  have hc := consistentFrom_split ((∅, []) : DSCache StmtIn U) L₁ e L₂ hcons
  rw [he] at hc
  obtain ⟨e', he', hcl⟩ := fwd_hit_sameClass_mem L₁ a b hc hhit
  exact hnr e' he' (by rw [he]; exact hcl)

/-- **A non-redundant inverse entry is fresh.** -/
theorem inv_entry_fresh (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U)
    (L₂ : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (he : e = (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ e :: L₂))
    (hnr : ∀ e' ∈ L₁, ¬ sameClass e e') :
    ¬ hasInvKey (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)) b := by
  intro hhit
  have hc := consistentFrom_split ((∅, []) : DSCache StmtIn U) L₁ e L₂ hcons
  rw [he] at hc
  obtain ⟨e', he', hcl⟩ := inv_hit_sameClass_mem L₁ a b hc hhit
  exact hnr e' he' (by rw [he]; exact hcl)

/-! ## Raw split at a base-trace position (assembly step s1→s2 bridge) -/

/-- A list splits at any in-range position into prefix, element, suffix. -/
theorem list_split_at {α : Type*} (l : List α) (p : ℕ) (hp : p < l.length) :
    l = l.take p ++ l[p] :: l.drop (p + 1) := by
  conv_lhs => rw [← List.take_append_drop p l]
  congr 1
  rw [List.drop_eq_getElem_cons hp]

/-- An earlier-indexed element lies in the prefix `take p`. -/
theorem getElem_mem_take {α : Type*} (l : List α) {p q : ℕ} (hq : q < p)
    (hp : p < l.length) : l[q]'(by omega) ∈ l.take p := by
  have hqt : q < (l.take p).length := by rw [List.length_take]; omega
  have h := List.getElem_mem hqt
  rwa [List.getElem_take] at h

/-- **Raw split at a base position.** For a base-trace index `j`, writing `pⱼ = f j` for the
order embedding, the raw log splits as `L₁ ++ baseTrace[j] :: L₂` with `|L₁| = pⱼ`, and every
earlier base entry `baseTrace[j']` (`j' < j`) lies in the prefix `L₁`. -/
theorem base_raw_split
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix : ℕ, (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (j : ℕ) (hj : j < (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1.length) :
    ∃ (hpj : f j < log.length),
      log = log.take (f j) ++ log[f j] :: log.drop (f j + 1) ∧
      log[f j] = (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1[j] ∧
      ∀ j' < j, ∀ (hj' : j' < (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1.length),
        (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1[j'] ∈ log.take (f j) := by
  classical
  set base := (DuplexSpongeFS.Paper.removeRedundantEntryDSPaper log).1 with hbase
  -- f j < log.length because base[j]? = log[f j]? is `some`
  have hfj : log[f j]? = some base[j] := by rw [← hf j, List.getElem?_eq_getElem hj]
  have hpj : f j < log.length := by
    rw [List.getElem?_eq_some_iff] at hfj; exact hfj.1
  refine ⟨hpj, list_split_at log (f j) hpj, ?_, ?_⟩
  · have := List.getElem?_eq_getElem hpj
    rw [hfj] at this; exact (Option.some_inj.mp this).symm
  · intro j' hj'j hj'
    -- f j' < f j by strict monotonicity, and base[j'] = log[f j']
    have hmono : f j' < f j := f.strictMono hj'j
    have hfj' : log[f j']? = some base[j'] := by rw [← hf j', List.getElem?_eq_getElem hj']
    have hfj'len : f j' < log.length := by
      rw [List.getElem?_eq_some_iff] at hfj'; exact hfj'.1
    have hbe : log[f j']'hfj'len = base[j'] := by
      have := List.getElem?_eq_getElem hfj'len; rw [hfj'] at this; exact (Option.some_inj.mp this).symm
    rw [← hbe]
    exact getElem_mem_take log hmono hpj

/-! ## First-occurrence property of NoRedundant logs (assembly step w1, base case)

NOTE: an arbitrary sublist order embedding need not map a base entry to its FIRST occurrence
in the raw log (a repeated value can embed at a later position), so `base_raw_split` with the
existential embedding does not by itself give "no earlier same-class". The correct route uses
that a `NoRedundant` list has the first-occurrence property at every position, plus the fact
(the remaining recursion lemma) that the dedup output's positions in the raw log are first
occurrences. This brick supplies the first half. -/

open DuplexSpongeFS.Paper in
/-- In a `NoRedundant` log, no earlier entry is the same class as a later one (raw `ℕ`
positions). The first-occurrence property, directly from the redundancy characterization. -/
theorem noRedundant_raw_no_earlier_sameClass
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : NoRedundantEntryDSPaper log) {p q : ℕ} (hq : q < p) (hp : p < log.length) :
    ¬ sameClass (log[p]) (log[q]'(by omega)) := by
  intro hcl
  refine h ⟨p, hp⟩ ((redundantEntryDSPaper_iff_sameClass log ⟨p, hp⟩).mpr ?_)
  exact ⟨⟨q, by omega⟩, hq, hcl⟩

/-! ## Dedup positions are first occurrences (assembly step w1, the recursion crux) -/

/-- The `getElem?` position map of `eraseIdx`: deleting index `i` shifts later positions by
one, for all indices. -/
theorem getElem?_eraseIdx_map {α : Type*} (l : List α) (i x : ℕ) :
    (l.eraseIdx i)[x]? = l[if x < i then x else x + 1]? := by
  rcases lt_or_ge x (l.eraseIdx i).length with hx | hx
  · rw [List.getElem?_eq_getElem hx, List.getElem_eraseIdx hx]
    split <;> rw [List.getElem?_eq_getElem]
  · rw [List.getElem?_eq_none hx]
    rcases lt_or_ge i l.length with hi | hi
    · rw [List.length_eraseIdx_of_lt hi] at hx
      exact (List.getElem?_eq_none (by split <;> omega)).symm
    · rw [List.eraseIdx_of_length_le hi] at hx
      exact (List.getElem?_eq_none (by split <;> omega)).symm

open DuplexSpongeFS.Paper in
/-- **Dedup positions are first occurrences.** There is an order embedding `f` of the dedup
base trace into the raw log such that each base entry sits at a raw position with no earlier
same-class raw entry. The well-founded recursion over `removeRedundantEntryDSPaper`. -/
theorem removeRedundant_firstOcc
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    ∃ f : ℕ ↪o ℕ,
      (∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?) ∧
      (∀ ix p (e ep : DSEntry StmtIn U),
        (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
        p < f ix → ¬ sameClass e ep) := by
  letI : Decidable (∃ idx : Fin log.length,
      DuplexSpongeFS.Paper.redundantEntryDSPaper log idx) := Classical.propDecidable _
  by_cases h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
  · set i := (Classical.choose h).val with hi
    have hilt : i < log.length := (Classical.choose h).isLt
    obtain ⟨f', hf'eq, hf'fo⟩ := removeRedundant_firstOcc (log.eraseIdx i)
    have hbase : removeRedundantEntryDSPaper log
        = removeRedundantEntryDSPaper (log.eraseIdx i) := by
      conv_lhs => rw [removeRedundantEntryDSPaper, dif_pos h]
    let gEmb : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (fun j => if j < i then j else j + 1)
      (by intro a b hab; dsimp only; split <;> split <;> omega)
    have hgEmb : ∀ x, gEmb x = if x < i then x else x + 1 := fun _ => rfl
    have hmapval : ∀ x, (log.eraseIdx i)[x]? = log[gEmb x]? := by
      intro x; rw [getElem?_eraseIdx_map, hgEmb]
    refine ⟨f'.trans gEmb, ?_, ?_⟩
    · intro ix; rw [hbase, hf'eq ix]; exact hmapval (f' ix)
    · intro ix p e ep hbe hlogp hpf
      rw [hbase] at hbe
      have core : ∀ r r' er, gEmb r' = r → log[r]? = some er → r' < f' ix →
          ¬ sameClass e er := by
        intro r r' er hgr hlogr hr'f
        have hlog'r : (log.eraseIdx i)[r']? = some er := by rw [hmapval r', hgr]; exact hlogr
        exact hf'fo ix r' e er hbe hlog'r hr'f
      intro hcl
      have hpf' : p < (if f' ix < i then f' ix else f' ix + 1) := by rw [← hgEmb]; exact hpf
      rcases eq_or_ne p i with rfl | hpi
      · have hred : redundantEntryDSPaper log (Classical.choose h) := Classical.choose_spec h
        obtain ⟨q, hq, hqcl⟩ :=
          (redundantEntryDSPaper_iff_sameClass log (Classical.choose h)).mp hred
        have hqi : (q : ℕ) < i := hq
        have hf'ge : i ≤ f' ix := by by_contra hlt; push_neg at hlt; rw [if_pos hlt] at hpf'; omega
        have hqf : (q : ℕ) < f' ix := by omega
        have hlogi : log[i]? = some ep := hlogp
        have hlogq : log[(q : ℕ)]? = some (log[(q : ℕ)]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        have hepi : ep = log[i]'hilt := by
          rw [List.getElem?_eq_getElem hilt] at hlogi; exact (Option.some_inj.mp hlogi).symm
        have hgq : gEmb (q : ℕ) = (q : ℕ) := by rw [hgEmb, if_pos hqi]
        have hclq : sameClass e (log[(q : ℕ)]'(by omega)) := by
          refine sameClass_trans hcl ?_; rw [hepi]; exact hqcl
        exact core (q : ℕ) (q : ℕ) (log[(q : ℕ)]'(by omega)) hgq hlogq hqf hclq
      · set p' := if p < i then p else p - 1 with hp'def
        have hgp : gEmb p' = p := by
          rw [hgEmb]
          rcases lt_or_ge p i with hlt | hge
          · rw [hp'def, if_pos hlt, if_pos hlt]
          · have hgt : i < p := lt_of_le_of_ne hge (Ne.symm hpi)
            rw [hp'def, if_neg (by omega : ¬ p < i), if_neg (by omega : ¬ p - 1 < i)]; omega
        have hp'f : p' < f' ix := by
          have : gEmb p' < gEmb (f' ix) := by rw [hgp, hgEmb]; exact hpf'
          exact gEmb.lt_iff_lt.mp this
        exact core p p' ep hgp hlogp hp'f hcl
  · have hnr : NoRedundantEntryDSPaper log := fun idx => not_exists.mp h idx
    have hself : removeRedundantEntryDSPaper log = ⟨log, hnr⟩ :=
      removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log hnr
    refine ⟨OrderEmbedding.ofStrictMono id strictMono_id, ?_, ?_⟩
    · intro ix; rw [hself]; rfl
    · intro ix p e ep hbe hlogp hpf
      rw [hself] at hbe
      have hix : ix < log.length := by
        rw [List.getElem?_eq_some_iff] at hbe; exact hbe.1
      have hp : p < log.length := by
        rw [List.getElem?_eq_some_iff] at hlogp; exact hlogp.1
      have he : e = log[ix]'hix := by
        rw [List.getElem?_eq_getElem hix] at hbe; exact (Option.some_inj.mp hbe).symm
      have hep : ep = log[p]'hp := by
        rw [List.getElem?_eq_getElem hp] at hlogp; exact (Option.some_inj.mp hlogp).symm
      rw [he, hep]
      exact noRedundant_raw_no_earlier_sameClass hnr (by simpa using hpf) hix
termination_by log.length
decreasing_by
  have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
  have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
    List.length_eraseIdx_add_one hlt
  omega

/-! ## w1 wiring and constructive anchoring (final assembly foundations) -/

open DuplexSpongeFS.Paper in
/-- **w1**: a base entry has no earlier same-class entry in its raw prefix. Directly from the
first-occurrence embedding: every earlier raw entry is at a position `< f j`, where the
first-occurrence property forbids same-class. -/
theorem base_no_earlier_sameClass
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j : ℕ) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (e' : DSEntry StmtIn U) (he' : e' ∈ log.take (f j)) :
    ¬ sameClass (removeRedundantEntryDSPaper log).1[j] e' := by
  obtain ⟨p, hp, hpx⟩ := List.getElem_of_mem he'
  rw [List.length_take] at hp
  rw [List.getElem_take] at hpx
  have hbe : (removeRedundantEntryDSPaper log).1[j]? =
      some (removeRedundantEntryDSPaper log).1[j] := List.getElem?_eq_getElem hj
  have hlogp : log[p]? = some e' := by
    rw [← hpx]; exact List.getElem?_eq_getElem (by omega : p < log.length)
  exact hfo j p _ e' hbe hlogp (by omega)

/-- **Constructive anchoring**: a collision at a split point makes the whole fold anchored. -/
theorem anchoredFrom_of_split (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U) (L₂ : List (DSEntry StmtIn U))
    (hcol : collisionStep e.1 (L₁.foldl stepCache c) e.2) :
    AnchoredFrom c (L₁ ++ e :: L₂) := by
  induction L₁ generalizing c with
  | nil => exact Or.inl hcol
  | cons e₁ ℓ ih =>
      rw [List.cons_append]
      refine Or.inr (ih (stepCache c e₁) ?_)
      rwa [List.foldl_cons] at hcol

/-! ## Base permutation-entry anchoring producers (final assembly workhorses) -/

lemma find?_fst_none_of_not_hasFwdKey {c : DSCache StmtIn U} {a : CanonicalSpongeState U}
    (h : ¬ hasFwdKey c a) : c.2.find? (fun w => w.1 = a) = none := by
  rw [List.find?_eq_none]
  intro w hw
  simp only [decide_eq_true_eq]
  intro hwa
  exact h ⟨w, hw, hwa⟩

lemma find?_snd_none_of_not_hasInvKey {c : DSCache StmtIn U} {b : CanonicalSpongeState U}
    (h : ¬ hasInvKey c b) : c.2.find? (fun w => w.2 = b) = none := by
  rw [List.find?_eq_none]
  intro w hw
  simp only [decide_eq_true_eq]
  intro hwb
  exact h ⟨w, hw, hwb⟩

open DuplexSpongeFS.Paper in
/-- **Forward-arm anchoring producer.** If a forward base entry `⟨inr (inl a), b⟩` has its
answer capacity in the slot list of its raw prefix fold (or equal to its query capacity),
the whole consistent log is anchored. -/
theorem base_fwd_anchored
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j : ℕ) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (a b : CanonicalSpongeState U)
    (hbj : (removeRedundantEntryDSPaper log).1[j] = (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U))
    (hcap : b.capacitySegment ∈ slotList ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U))
        ∨ b.capacitySegment = a.capacitySegment) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨hpj, hsplit, hbjf, _hearlier⟩ := base_raw_split log f hf j hj
  set L₁ := log.take (f j) with hL₁
  set L₂ := log.drop (f j + 1) with hL₂
  have he : log[f j] = (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) := by rw [hbjf, hbj]
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ log[f j] :: L₂) := by
    rw [← hsplit]; exact hcons
  have hnr : ∀ e' ∈ L₁, ¬ sameClass (log[f j]) e' := by
    intro e' he''; rw [hbjf]; exact base_no_earlier_sameClass log f hf hfo j hj e' he''
  have hfresh : ¬ hasFwdKey (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)) a :=
    fwd_entry_fresh L₁ (log[f j]) L₂ a b he hcons' hnr
  -- the collision at the split point
  have hcol : collisionStep (log[f j]).1 (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U))
      (log[f j]).2 := by
    rw [he]
    refine ⟨find?_fst_none_of_not_hasFwdKey hfresh, hcap⟩
  have := anchoredFrom_of_split ((∅, []) : DSCache StmtIn U) L₁ (log[f j]) L₂ hcol
  rwa [← hsplit] at this

open DuplexSpongeFS.Paper in
/-- **Inverse-arm anchoring producer.** Symmetric to `base_fwd_anchored` for an inverse base
entry `⟨inr (inr b), a⟩`. -/
theorem base_inv_anchored
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j : ℕ) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (a b : CanonicalSpongeState U)
    (hbj : (removeRedundantEntryDSPaper log).1[j] = (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U))
    (hcap : a.capacitySegment ∈ slotList ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U))
        ∨ a.capacitySegment = b.capacitySegment) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨hpj, hsplit, hbjf, _hearlier⟩ := base_raw_split log f hf j hj
  set L₁ := log.take (f j) with hL₁
  set L₂ := log.drop (f j + 1) with hL₂
  have he : log[f j] = (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U) := by rw [hbjf, hbj]
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ log[f j] :: L₂) := by
    rw [← hsplit]; exact hcons
  have hnr : ∀ e' ∈ L₁, ¬ sameClass (log[f j]) e' := by
    intro e' he''; rw [hbjf]; exact base_no_earlier_sameClass log f hf hfo j hj e' he''
  have hfresh : ¬ hasInvKey (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)) b :=
    inv_entry_fresh L₁ (log[f j]) L₂ a b he hcons' hnr
  have hcol : collisionStep (log[f j]).1 (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U))
      (log[f j]).2 := by
    rw [he]
    refine ⟨find?_snd_none_of_not_hasInvKey hfresh, hcap⟩
  have := anchoredFrom_of_split ((∅, []) : DSCache StmtIn U) L₁ (log[f j]) L₂ hcol
  rwa [← hsplit] at this

/-! ## Hash-arm anchoring producer (final assembly, hash) -/

/-- **Hash-cache provenance (one step).** A hash answer present after a step was already
cached or was inserted by the step's (hash) entry. -/
theorem stepCache_hash_provenance (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : (stepCache c e).1 q = some u) :
    c.1 q = some u ∨ e = (⟨.inl q, u⟩ : DSEntry StmtIn U) := by
  rcases e with ⟨t, ans⟩
  rcases t with q' | a | b
  · rcases hcq : c.1 q' with _ | u'
    · simp only [stepCache, hcq] at h
      by_cases hqq : q = q'
      · subst hqq
        rw [OracleSpec.QueryCache.cacheQuery_self] at h
        exact Or.inr (by rw [Option.some_inj.mp h])
      · rw [OracleSpec.QueryCache.cacheQuery, Function.update_of_ne hqq] at h
        exact Or.inl h
    · left; simpa [stepCache, hcq] using h
  · rcases hf : c.2.find? (fun w => w.1 = a) with _ | w <;> · left; simpa [stepCache, hf] using h
  · rcases hf : c.2.find? (fun w => w.2 = b) with _ | w <;> · left; simpa [stepCache, hf] using h

/-- **Hash-cache provenance (whole fold).** -/
theorem foldl_hash_provenance (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : (L.foldl stepCache c).1 q = some u) :
    c.1 q = some u ∨ ∃ e ∈ L, e = (⟨.inl q, u⟩ : DSEntry StmtIn U) := by
  induction L generalizing c with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rw [List.foldl_cons] at h
      rcases ih (stepCache c e) h with h' | ⟨e', he', hk'⟩
      · rcases stepCache_hash_provenance c e h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-- **A non-redundant hash entry is fresh.** A consistent hash hit forces the cached answer
to equal the entry's, making the inserting entry same-class (equal); so a non-redundant hash
entry cannot be a hit. -/
theorem hash_entry_fresh (L₁ : List (DSEntry StmtIn U)) (e : DSEntry StmtIn U)
    (L₂ : List (DSEntry StmtIn U)) (q : StmtIn) (u : Vector U SpongeSize.C)
    (he : e = (⟨.inl q, u⟩ : DSEntry StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ e :: L₂))
    (hnr : ∀ e' ∈ L₁, ¬ sameClass e e') :
    (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)).1 q = none := by
  by_contra hne
  obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp hne
  have hc := consistentFrom_split ((∅, []) : DSCache StmtIn U) L₁ e L₂ hcons
  rw [he] at hc
  have huu : u = u' := hc u' hu'
  rcases foldl_hash_provenance ((∅, []) : DSCache StmtIn U) L₁ hu' with h0 | ⟨e', he'mem, he'eq⟩
  · simp at h0
  · refine hnr e' he'mem ?_
    rw [he, he'eq, huu]; exact sameClass_refl _

open DuplexSpongeFS.Paper in
/-- **Hash-arm anchoring producer.** A hash base entry whose answer is an existing slot
anchors the consistent log. -/
theorem base_hash_anchored
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j : ℕ) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (q : StmtIn) (u : Vector U SpongeSize.C)
    (hbj : (removeRedundantEntryDSPaper log).1[j] = (⟨.inl q, u⟩ : DSEntry StmtIn U))
    (hcap : u ∈ slotList ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U))) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨hpj, hsplit, hbjf, _hearlier⟩ := base_raw_split log f hf j hj
  set L₁ := log.take (f j) with hL₁
  set L₂ := log.drop (f j + 1) with hL₂
  have he : log[f j] = (⟨.inl q, u⟩ : DSEntry StmtIn U) := by rw [hbjf, hbj]
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U) (L₁ ++ log[f j] :: L₂) := by
    rw [← hsplit]; exact hcons
  have hnr : ∀ e' ∈ L₁, ¬ sameClass (log[f j]) e' := by
    intro e' he''; rw [hbjf]; exact base_no_earlier_sameClass log f hf hfo j hj e' he''
  have hfresh : (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U)).1 q = none :=
    hash_entry_fresh L₁ (log[f j]) L₂ q u he hcons' hnr
  have hcol : collisionStep (log[f j]).1 (L₁.foldl stepCache ((∅, []) : DSCache StmtIn U))
      (log[f j]).2 := by
    rw [he]; exact ⟨hfresh, hcap⟩
  have := anchoredFrom_of_split ((∅, []) : DSCache StmtIn U) L₁ (log[f j]) L₂ hcol
  rwa [← hsplit] at this

/-! ## Fresh entries cache their data (slot-persistence foundations) -/

/-- A fresh forward entry's pair ends up in the final fold cache. -/
theorem fresh_fwd_inserts (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (L₂ : List (DSEntry StmtIn U))
    (hfresh : ¬ hasFwdKey (L₁.foldl stepCache c) a) :
    (a, b) ∈ ((L₁ ++ (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) :: L₂).foldl stepCache c).2 := by
  rw [List.foldl_append, List.foldl_cons]
  set c1 := L₁.foldl stepCache c with hc1
  have hfind : c1.2.find? (fun w => w.1 = a) = none := find?_fst_none_of_not_hasFwdKey hfresh
  have hstep : (stepCache c1 (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U)).2 = c1.2.concat (a, b) := by
    simp [stepCache, hfind]
  have hmem : (a, b) ∈ (stepCache c1 (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U)).2 := by
    rw [hstep, List.concat_eq_append]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact (foldl_stepCache_perm_sublist (stepCache c1 (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U)) L₂).subset hmem

/-- A fresh inverse entry's pair ends up in the final fold cache. -/
theorem fresh_inv_inserts (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (a b : CanonicalSpongeState U)
    (L₂ : List (DSEntry StmtIn U))
    (hfresh : ¬ hasInvKey (L₁.foldl stepCache c) b) :
    (a, b) ∈ ((L₁ ++ (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U) :: L₂).foldl stepCache c).2 := by
  rw [List.foldl_append, List.foldl_cons]
  set c1 := L₁.foldl stepCache c with hc1
  have hfind : c1.2.find? (fun w => w.2 = b) = none := find?_snd_none_of_not_hasInvKey hfresh
  have hstep : (stepCache c1 (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)).2 = c1.2.concat (a, b) := by
    simp [stepCache, hfind]
  have hmem : (a, b) ∈ (stepCache c1 (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)).2 := by
    rw [hstep, List.concat_eq_append]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact (foldl_stepCache_perm_sublist (stepCache c1 (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)) L₂).subset hmem

/-- A cached hash answer is a slot. -/
theorem mem_slotList_of_hash_cached (c : DSCache StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    u ∈ slotList c := by
  classical
  refine List.mem_append_left _ ?_
  rw [List.mem_filterMap]
  exact ⟨q, by rw [Finset.mem_toList]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h]; rfl⟩, h⟩

/-! ## Earlier base entry's capacities are slots of a later prefix fold -/

open DuplexSpongeFS.Paper in
/-- The inner split of `take (f j)` at an earlier position `f j'`. -/
private theorem take_inner_split
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (e : DSEntry StmtIn U)
    (fj fj' : ℕ) (hlt : fj' < fj) (hfj : fj ≤ log.length)
    (hval : log[fj']'(by omega) = e) :
    log.take fj = log.take fj' ++ e :: (log.take fj).drop (fj' + 1) := by
  have hk : fj' < (log.take fj).length := by rw [List.length_take]; omega
  conv_lhs => rw [← List.take_append_drop fj' (log.take fj)]
  rw [List.take_take, min_eq_left (le_of_lt hlt)]
  congr 1
  rw [List.drop_eq_getElem_cons hk, List.getElem_take, hval]

open DuplexSpongeFS.Paper in
/-- **Slot-persistence (forward).** An earlier forward base entry's pair is cached in the
later entry's prefix fold, so both its capacities are slots. -/
theorem base_earlier_fwd_slots
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j j' : ℕ) (hjj : j' < j) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (a' b' : CanonicalSpongeState U)
    (hbj' : (removeRedundantEntryDSPaper log).1[j']'(by omega)
      = (⟨.inr (.inl a'), b'⟩ : DSEntry StmtIn U)) :
    (a', b') ∈ ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 := by
  have hj' : j' < (removeRedundantEntryDSPaper log).1.length := by omega
  obtain ⟨hpj', hsplit', hbjf', _⟩ := base_raw_split log f hf j' hj'
  have he' : log[f j'] = (⟨.inr (.inl a'), b'⟩ : DSEntry StmtIn U) := by rw [hbjf', hbj']
  -- freshness of base[j'] in the global log
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U)
      (log.take (f j') ++ log[f j'] :: log.drop (f j' + 1)) := by rw [← hsplit']; exact hcons
  have hnr' : ∀ e'' ∈ log.take (f j'), ¬ sameClass (log[f j']) e'' := by
    intro e'' he''; rw [hbjf']; exact base_no_earlier_sameClass log f hf hfo j' hj' e'' he''
  have hfresh : ¬ hasFwdKey ((log.take (f j')).foldl stepCache ((∅, []) : DSCache StmtIn U)) a' :=
    fwd_entry_fresh (log.take (f j')) (log[f j']) (log.drop (f j' + 1)) a' b' he' hcons' hnr'
  -- f j' < f j, and the inner split of take (f j) at f j'
  have hfjj : f j' < f j := f.strictMono hjj
  have hfjlen : f j ≤ log.length := by
    have hb : (removeRedundantEntryDSPaper log).1[j]? = some (removeRedundantEntryDSPaper log).1[j] :=
      List.getElem?_eq_getElem hj
    rw [hf j] at hb
    rw [List.getElem?_eq_some_iff] at hb
    exact le_of_lt hb.1
  have hsplit_inner : log.take (f j)
      = log.take (f j') ++ (⟨.inr (.inl a'), b'⟩ : DSEntry StmtIn U) :: (log.take (f j)).drop (f j' + 1) :=
    take_inner_split log _ (f j) (f j') hfjj hfjlen (by rw [he'])
  rw [hsplit_inner]
  exact fresh_fwd_inserts ((∅, []) : DSCache StmtIn U) (log.take (f j')) a' b'
    ((log.take (f j)).drop (f j' + 1)) hfresh

/-! ## Slot-persistence: inverse and hash arms -/

/-- The hash cache only grows along the whole fold. -/
theorem foldl_stepCache_hash_mono (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    (L.foldl stepCache c).1 q = some u := by
  induction L generalizing c with
  | nil => exact h
  | cons e ℓ ih => rw [List.foldl_cons]; exact ih (stepCache c e) (stepCache_hash_mono c e h)

/-- A fresh hash entry's answer ends up cached in the final fold. -/
theorem fresh_hash_inserts (c : DSCache StmtIn U)
    (L₁ : List (DSEntry StmtIn U)) (q : StmtIn) (u : Vector U SpongeSize.C)
    (L₂ : List (DSEntry StmtIn U))
    (hfresh : (L₁.foldl stepCache c).1 q = none) :
    ((L₁ ++ (⟨.inl q, u⟩ : DSEntry StmtIn U) :: L₂).foldl stepCache c).1 q = some u := by
  rw [List.foldl_append, List.foldl_cons]
  set c1 := L₁.foldl stepCache c with hc1
  have hstep : (stepCache c1 (⟨.inl q, u⟩ : DSEntry StmtIn U)).1 q = some u := by
    simp only [stepCache, hfresh, OracleSpec.QueryCache.cacheQuery, Function.update_self]
  exact foldl_stepCache_hash_mono (stepCache c1 (⟨.inl q, u⟩ : DSEntry StmtIn U)) L₂ hstep

open DuplexSpongeFS.Paper in
/-- **Slot-persistence (inverse).** -/
theorem base_earlier_inv_slots
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j j' : ℕ) (hjj : j' < j) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (a' b' : CanonicalSpongeState U)
    (hbj' : (removeRedundantEntryDSPaper log).1[j']'(by omega)
      = (⟨.inr (.inr b'), a'⟩ : DSEntry StmtIn U)) :
    (a', b') ∈ ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 := by
  have hj' : j' < (removeRedundantEntryDSPaper log).1.length := by omega
  obtain ⟨hpj', hsplit', hbjf', _⟩ := base_raw_split log f hf j' hj'
  have he' : log[f j'] = (⟨.inr (.inr b'), a'⟩ : DSEntry StmtIn U) := by rw [hbjf', hbj']
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U)
      (log.take (f j') ++ log[f j'] :: log.drop (f j' + 1)) := by rw [← hsplit']; exact hcons
  have hnr' : ∀ e'' ∈ log.take (f j'), ¬ sameClass (log[f j']) e'' := by
    intro e'' he''; rw [hbjf']; exact base_no_earlier_sameClass log f hf hfo j' hj' e'' he''
  have hfresh : ¬ hasInvKey ((log.take (f j')).foldl stepCache ((∅, []) : DSCache StmtIn U)) b' :=
    inv_entry_fresh (log.take (f j')) (log[f j']) (log.drop (f j' + 1)) a' b' he' hcons' hnr'
  have hfjj : f j' < f j := f.strictMono hjj
  have hfjlen : f j ≤ log.length := by
    have hb : (removeRedundantEntryDSPaper log).1[j]? = some (removeRedundantEntryDSPaper log).1[j] :=
      List.getElem?_eq_getElem hj
    rw [hf j] at hb; rw [List.getElem?_eq_some_iff] at hb; exact le_of_lt hb.1
  have hsplit_inner : log.take (f j)
      = log.take (f j') ++ (⟨.inr (.inr b'), a'⟩ : DSEntry StmtIn U) :: (log.take (f j)).drop (f j' + 1) :=
    take_inner_split log _ (f j) (f j') hfjj hfjlen (by rw [he'])
  rw [hsplit_inner]
  exact fresh_inv_inserts ((∅, []) : DSCache StmtIn U) (log.take (f j')) a' b'
    ((log.take (f j)).drop (f j' + 1)) hfresh

open DuplexSpongeFS.Paper in
/-- **Slot-persistence (hash).** -/
theorem base_earlier_hash_slot
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (f : ℕ ↪o ℕ)
    (hf : ∀ ix, (removeRedundantEntryDSPaper log).1[ix]? = log[f ix]?)
    (hfo : ∀ ix p (e ep : DSEntry StmtIn U),
      (removeRedundantEntryDSPaper log).1[ix]? = some e → log[p]? = some ep →
      p < f ix → ¬ sameClass e ep)
    (j j' : ℕ) (hjj : j' < j) (hj : j < (removeRedundantEntryDSPaper log).1.length)
    (q' : StmtIn) (u' : Vector U SpongeSize.C)
    (hbj' : (removeRedundantEntryDSPaper log).1[j']'(by omega)
      = (⟨.inl q', u'⟩ : DSEntry StmtIn U)) :
    u' ∈ slotList ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)) := by
  have hj' : j' < (removeRedundantEntryDSPaper log).1.length := by omega
  obtain ⟨hpj', hsplit', hbjf', _⟩ := base_raw_split log f hf j' hj'
  have he' : log[f j'] = (⟨.inl q', u'⟩ : DSEntry StmtIn U) := by rw [hbjf', hbj']
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U)
      (log.take (f j') ++ log[f j'] :: log.drop (f j' + 1)) := by rw [← hsplit']; exact hcons
  have hnr' : ∀ e'' ∈ log.take (f j'), ¬ sameClass (log[f j']) e'' := by
    intro e'' he''; rw [hbjf']; exact base_no_earlier_sameClass log f hf hfo j' hj' e'' he''
  have hfresh : ((log.take (f j')).foldl stepCache ((∅, []) : DSCache StmtIn U)).1 q' = none :=
    hash_entry_fresh (log.take (f j')) (log[f j']) (log.drop (f j' + 1)) q' u' he' hcons' hnr'
  have hfjj : f j' < f j := f.strictMono hjj
  have hfjlen : f j ≤ log.length := by
    have hb : (removeRedundantEntryDSPaper log).1[j]? = some (removeRedundantEntryDSPaper log).1[j] :=
      List.getElem?_eq_getElem hj
    rw [hf j] at hb; rw [List.getElem?_eq_some_iff] at hb; exact le_of_lt hb.1
  have hsplit_inner : log.take (f j)
      = log.take (f j') ++ (⟨.inl q', u'⟩ : DSEntry StmtIn U) :: (log.take (f j)).drop (f j' + 1) :=
    take_inner_split log _ (f j) (f j') hfjj hfjlen (by rw [he'])
  rw [hsplit_inner]
  exact mem_slotList_of_hash_cached _ (fresh_hash_inserts ((∅, []) : DSCache StmtIn U)
    (log.take (f j')) q' u' ((log.take (f j)).drop (f j' + 1)) hfresh)

/-! ## The disjunct case-bash: each EPaper arm produces an anchored collision -/

open DuplexSpongeFS.Paper in
/-- **E_h arm.** A hash-capacity duplicate among dedup entries anchors the consistent log. -/
theorem anchored_of_E_h
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (hEh : capacitySegmentDupHashPaper log) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨f, hf, hfo⟩ := removeRedundant_firstOcc log
  obtain ⟨j, capSeg, stmt, hbj, j', hj'j, stmt', hdisj⟩ := hEh
  have hcap : capSeg ∈ slotList ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)) := by
    rcases hdisj with hb' | ⟨sI1, sO1, hb', hc1⟩ | ⟨sO2, sI2, hb', hc2⟩
      | ⟨sI3, sO3, hb', hc3⟩ | ⟨sO4, sI4, hb', hc4⟩
    · exact base_earlier_hash_slot log hcons f hf hfo j j' hj'j j.isLt stmt' capSeg hb'
    · rw [← hc1]
      exact (mem_slotList_of_mem_perm _
        (base_earlier_fwd_slots log hcons f hf hfo j j' hj'j j.isLt sI1 sO1 hb')).2
    · rw [← hc2]
      exact (mem_slotList_of_mem_perm _
        (base_earlier_inv_slots log hcons f hf hfo j j' hj'j j.isLt sI2 sO2 hb')).1
    · rw [← hc3]
      exact (mem_slotList_of_mem_perm _
        (base_earlier_fwd_slots log hcons f hf hfo j j' hj'j j.isLt sI3 sO3 hb')).1
    · rw [← hc4]
      exact (mem_slotList_of_mem_perm _
        (base_earlier_inv_slots log hcons f hf hfo j j' hj'j j.isLt sI4 sO4 hb')).2
  exact base_hash_anchored log hcons f hf hfo j j.isLt stmt capSeg hbj hcap

open DuplexSpongeFS.Paper in
/-- **E_p arm.** A forward-permutation capacity duplicate anchors the consistent log. -/
theorem anchored_of_E_p
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (hEp : capacitySegmentDupPermPaper log) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨f, hf, hfo⟩ := removeRedundant_firstOcc log
  obtain ⟨j, capSeg, ⟨sI, sO, hbj, hcapseg⟩, hdisj⟩ := hEp
  -- anchor on base[j] = ⟨inr inl sI, sO⟩, answer cap sO.cap = capSeg
  refine base_fwd_anchored log hcons f hf hfo j j.isLt sI sO hbj ?_
  -- produce: sO.cap ∈ slotList (take f j) ∨ sO.cap = sI.cap
  rcases hdisj with ⟨j', hj'j, stmt', hb'⟩ | ⟨j', hj'j, sI1, sO1, hb', hc1⟩
    | ⟨j', hj'j, sO2, sI2, hb', hc2⟩ | ⟨j', hj'j, sI3, sO3, hb', hc3⟩
    | ⟨j', hj'j, sO4, sI4, hb', hc4⟩
  · refine Or.inl ?_; rw [hcapseg]
    exact base_earlier_hash_slot log hcons f hf hfo j j' hj'j j.isLt stmt' capSeg hb'
  · refine Or.inl ?_; rw [hcapseg]
    exact hc1 ▸ (mem_slotList_of_mem_perm _
      (base_earlier_fwd_slots log hcons f hf hfo j j' hj'j j.isLt sI1 sO1 hb')).2
  · rcases lt_or_eq_of_le hj'j with hlt | heq
    · refine Or.inl ?_; rw [hcapseg]
      exact hc2 ▸ (mem_slotList_of_mem_perm _
        (base_earlier_inv_slots log hcons f hf hfo j j' hlt j.isLt sI2 sO2 hb')).1
    · exact absurd (hbj.symm.trans (heq ▸ hb')) (by simp)
  · rcases lt_or_eq_of_le hj'j with hlt | heq
    · refine Or.inl ?_; rw [hcapseg]
      exact hc3 ▸ (mem_slotList_of_mem_perm _
        (base_earlier_fwd_slots log hcons f hf hfo j j' hlt j.isLt sI3 sO3 hb')).1
    · have hbeq : (⟨.inr (.inl sI), sO⟩ : DSEntry StmtIn U) = ⟨.inr (.inl sI3), sO3⟩ :=
        hbj.symm.trans (heq ▸ hb')
      have hsI : sI = sI3 := Sum.inl.inj (Sum.inr.inj (congrArg Sigma.fst hbeq))
      exact Or.inr (by rw [hcapseg, ← hc3, hsI])
  · rcases lt_or_eq_of_le hj'j with hlt | heq
    · refine Or.inl ?_; rw [hcapseg]
      exact hc4 ▸ (mem_slotList_of_mem_perm _
        (base_earlier_inv_slots log hcons f hf hfo j j' hlt j.isLt sI4 sO4 hb')).2
    · exact absurd (hbj.symm.trans (heq ▸ hb')) (by simp)

open DuplexSpongeFS.Paper in
/-- **E_pinv arm.** An inverse-permutation capacity duplicate (B1-repaired) anchors the log. -/
theorem anchored_of_E_pinv
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (hEpi : capacitySegmentDupPermInvPaper log) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨f, hf, hfo⟩ := removeRedundant_firstOcc log
  obtain ⟨j, capSeg, ⟨sO, sI, hbj, hcapseg⟩, hdisj⟩ := hEpi
  refine base_inv_anchored log hcons f hf hfo j j.isLt sI sO hbj ?_
  -- produce: sI.cap ∈ slotList (take f j) ∨ sI.cap = sO.cap
  rcases hdisj with ⟨j', hj'j, stmt', hb'⟩ | ⟨j', hj'j, sI1, sO1, hb', hc1⟩
    | ⟨j', hj'j, sO2, sI2, hb', hc2⟩ | ⟨j', hj'j, sI3, sO3, hb', hc3⟩
    | ⟨j', hj'j, q, a, hb', hc5⟩
  · refine Or.inl ?_; rw [hcapseg]
    exact base_earlier_hash_slot log hcons f hf hfo j j' hj'j j.isLt stmt' capSeg hb'
  · refine Or.inl ?_; rw [hcapseg]
    exact hc1 ▸ (mem_slotList_of_mem_perm _
      (base_earlier_fwd_slots log hcons f hf hfo j j' hj'j j.isLt sI1 sO1 hb')).2
  · refine Or.inl ?_; rw [hcapseg]
    exact hc2 ▸ (mem_slotList_of_mem_perm _
      (base_earlier_inv_slots log hcons f hf hfo j j' hj'j j.isLt sO2 sI2 hb')).1
  · rcases lt_or_eq_of_le hj'j with hlt | heq
    · refine Or.inl ?_; rw [hcapseg]
      exact hc3 ▸ (mem_slotList_of_mem_perm _
        (base_earlier_fwd_slots log hcons f hf hfo j j' hlt j.isLt sI3 sO3 hb')).1
    · exact absurd (hbj.symm.trans (heq ▸ hb')) (by simp)
  · rcases lt_or_eq_of_le hj'j with hlt | heq
    · refine Or.inl ?_; rw [hcapseg]
      exact hc5 ▸ (mem_slotList_of_mem_perm _
        (base_earlier_inv_slots log hcons f hf hfo j j' hlt j.isLt a q hb')).2
    · -- j' = j: base[j] = ⟨inr inr q, a⟩ = ⟨inr inr sO, sI⟩, so q = sO; sO.cap = capSeg = sI.cap
      have hbeq : (⟨.inr (.inr sO), sI⟩ : DSEntry StmtIn U) = ⟨.inr (.inr q), a⟩ :=
        hbj.symm.trans (heq ▸ hb')
      have hq : sO = q := Sum.inr.inj (Sum.inr.inj (congrArg Sigma.fst hbeq))
      exact Or.inr (by rw [hcapseg, ← hc5, hq])

open DuplexSpongeFS.Paper in
/-- **E_func arm.** A function violation among dedup entries is impossible in a non-anchored
consistent log: the earlier entry caches the forward key, contradicting the freshness of the
later forward base entry. (The contradiction yields `AnchoredFrom` vacuously.) -/
theorem anchored_of_E_func
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    (hEf : notFunctionPaper log) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log := by
  obtain ⟨f, hf, hfo⟩ := removeRedundant_firstOcc log
  obtain ⟨j, sIn, sOut, hbj, j', hj'j, sO1, hor⟩ := hEf
  -- base[j] = ⟨inr inl sIn, sOut⟩ is fresh at f j: ¬ hasFwdKey at its prefix fold
  obtain ⟨hpj, hsplit, hbjf, _⟩ := base_raw_split log f hf j j.isLt
  have he : log[f j] = (⟨.inr (.inl sIn), sOut⟩ : DSEntry StmtIn U) := by rw [hbjf]; exact hbj
  have hcons' : ConsistentFrom ((∅, []) : DSCache StmtIn U)
      (log.take (f j) ++ log[f j] :: log.drop (f j + 1)) := by rw [← hsplit]; exact hcons
  have hnr : ∀ e' ∈ log.take (f j), ¬ sameClass (log[f j]) e' := by
    intro e' he'; rw [hbjf]; exact base_no_earlier_sameClass log f hf hfo j j.isLt e' he'
  have hfresh : ¬ hasFwdKey ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)) sIn :=
    fwd_entry_fresh (log.take (f j)) (log[f j]) (log.drop (f j + 1)) sIn sOut he hcons' hnr
  -- but the earlier entry caches the forward key sIn
  have hkey : hasFwdKey ((log.take (f j)).foldl stepCache ((∅, []) : DSCache StmtIn U)) sIn := by
    rcases hor with hb' | ⟨sO2, hb'⟩
    · exact ⟨(sIn, sO1), base_earlier_fwd_slots log hcons f hf hfo j j' hj'j j.isLt sIn sO1 hb', rfl⟩
    · exact ⟨(sIn, sO2), base_earlier_inv_slots log hcons f hf hfo j j' hj'j j.isLt sIn sO2 hb', rfl⟩
  exact absurd hkey hfresh

/-! ## Assembly: the paper bound conditional on the dedup reduction -/

open DuplexSpongeFS.Paper in
/-- The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent
with the empty cache that satisfies the paper bad event `EPaper` contains an anchored
collision against the empty cache. -/
abbrev EPaperReduction (StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq (CanonicalSpongeState U)]
    [Fintype StmtIn] [Fintype U] : Prop :=
  ∀ (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)),
    ConsistentFrom ((∅, []) : DSCache StmtIn U) log →
    EPaper log →
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log

open DuplexSpongeFS.Paper in
/-- **`EPaperReduction` is a theorem.** A consistent log exhibiting the paper bad event
`EPaper` is anchored. The full disjunct case-bash over the four CO25 §5.6 arms. -/
theorem ePaperReduction_holds : EPaperReduction StmtIn U := by
  intro log hcons hEP
  rcases hEP with (hh | hp | hpinv) | hfunc
  · exact anchored_of_E_h log hcons hh
  · exact anchored_of_E_p log hcons hp
  · exact anchored_of_E_pinv log hcons hpinv
  · exact anchored_of_E_func log hcons hfunc


open DuplexSpongeFS.Paper in
/-- **The eager paper bound, conditional on the dedup reduction.** For any `T`-query
adversary, the probability that the logged trace of the eager lazy carrier exhibits
`EPaper`, in real form, is at most `(7T² − 3T)/(2|U|^C)`. -/
theorem probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction
    (hred : EPaperReduction StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
        (simulateQ lazyDSImpl ((simulateQ loggingOracle P).run)).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]).toReal
      ≤ DuplexSpongeFS.BirthdayBound.lemma5_8Bound U T := by
  classical
  set Q := (simulateQ loggingOracle P).run with hQ
  have hQbound : IsTotalQueryBound Q T :=
    (OracleComp.isTotalQueryBound_run_simulateQ_loggingOracle_iff P T).mpr hT
  -- Step 1: rewrite the EPaper probability as an EPaper-on-logged-value probability of the
  -- flagged run, via `run'` and the forgetting bridge.
  have heq : Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        EPaper z.2 |
        (simulateQ lazyDSImpl Q).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]
      = Pr[ fun xs : (α × QueryLog (duplexSpongeChallengeOracle StmtIn U))
              × (DSCache StmtIn U × Prop) => EPaper xs.1.2 |
          (simulateQ lazyDSImplFlagged Q).run ((∅, []), False)] := by
    rw [StateT.run'_eq, probEvent_map,
      lazyDSImpl_run_map_flagged Q (∅, []) False, probEvent_map]
    rfl
  rw [heq]
  -- Step 2: monotone step `EPaper xs.1.2 → final flag`, then the engine output.
  refine le_trans (ENNReal.toReal_mono ?_ (probEvent_mono fun xs hxs hEP => ?_))
    (probEvent_flag_final_toReal_le_lemma5_8Bound Q T hQbound)
  · -- the flag probability is finite
    exact ne_of_lt (lt_of_le_of_lt probEvent_le_one ENNReal.one_lt_top)
  · -- the support fact: a consistent EPaper log forces the final flag
    obtain ⟨_, hcons, hflag⟩ := support_flagged_logged P (∅, []) False xs hxs
    rw [hflag]
    exact Or.inr (hred xs.1.2 hcons hEP)

open DuplexSpongeFS.Paper in
/-- **CO25 Lemma 5.8, unconditional (eager lazy carrier).** For any `T`-query adversary, the
probability that the logged trace of the eager lazy carrier exhibits the paper bad event
`EPaper`, in real form, is at most `(7T² − 3T)/(2|U|^C)` — with NO remaining hypothesis, the
dedup reduction `EPaperReduction` now being a theorem (`ePaperReduction_holds`). -/
theorem probEvent_EPaper_toReal_le_lemma5_8Bound
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
        (simulateQ lazyDSImpl ((simulateQ loggingOracle P).run)).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]).toReal
      ≤ DuplexSpongeFS.BirthdayBound.lemma5_8Bound U T :=
  probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction ePaperReduction_holds P T hT

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support
#print axioms DuplexSpongeFS.EagerLazyDS.support_flagged_logged
#print axioms DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct
#print axioms DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp
#print axioms DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys
#print axioms DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_fwdNodup
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_stepCache_fwdNodup
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_pair_provenance
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_pair_provenance
#print axioms DuplexSpongeFS.EagerLazyDS.consistent_fwd_hit_pair_mem
#print axioms DuplexSpongeFS.EagerLazyDS.fwd_hit_sameClass_mem
#print axioms DuplexSpongeFS.EagerLazyDS.consistent_inv_hit_pair_mem
#print axioms DuplexSpongeFS.EagerLazyDS.inv_hit_sameClass_mem
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_split
#print axioms DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_split
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundant_orderEmbedding
#print axioms DuplexSpongeFS.EagerLazyDS.fwd_entry_fresh
#print axioms DuplexSpongeFS.EagerLazyDS.inv_entry_fresh
#print axioms DuplexSpongeFS.EagerLazyDS.base_raw_split
#print axioms DuplexSpongeFS.EagerLazyDS.noRedundant_raw_no_earlier_sameClass
#print axioms DuplexSpongeFS.EagerLazyDS.getElem?_eraseIdx_map
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundant_firstOcc
#print axioms DuplexSpongeFS.EagerLazyDS.base_no_earlier_sameClass
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_split
#print axioms DuplexSpongeFS.EagerLazyDS.base_fwd_anchored
#print axioms DuplexSpongeFS.EagerLazyDS.base_inv_anchored
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_hash_provenance
#print axioms DuplexSpongeFS.EagerLazyDS.hash_entry_fresh
#print axioms DuplexSpongeFS.EagerLazyDS.base_hash_anchored
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_fwd_inserts
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_inv_inserts
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash_cached
#print axioms DuplexSpongeFS.EagerLazyDS.base_earlier_fwd_slots
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_hash_inserts
#print axioms DuplexSpongeFS.EagerLazyDS.base_earlier_inv_slots
#print axioms DuplexSpongeFS.EagerLazyDS.base_earlier_hash_slot
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_E_h
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_E_p
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_E_pinv
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_E_func
#print axioms DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound
#print axioms DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons
#print axioms DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new
#print axioms DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new
#print axioms DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction
