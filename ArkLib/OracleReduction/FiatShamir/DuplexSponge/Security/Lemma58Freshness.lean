/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58CacheProvenance
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine

/-!
# Freshness at class-first slots (issue #316, `EPaperReduction` step 2)

On a consistent log, the cache lookup at a class-first slot **misses**: if the key were
cached, provenance supplies an earlier creating entry; consistency forces our entry's answer
to equal the cached one, making our entry equal to the creator (hash / forward) or its
`swapEntry` (inverse creator) — contradicting first-of-class.

Main results:
* `consistentFrom_prefix_getElem` — consistency localizes: entry `k` is consistent with the
  prefix fold;
* `fresh_at_firstOfClass_hash` / `_perm` / `_permInv` — the three freshness cases.

These are exactly the step-2 deliverables of the finishing plan posted on #316; steps 3–4
(the `E_func` vacuity and the `E_dup` → `collisionStep` extraction) consume them together
with the step-1 dedup pullback.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.EagerLazyDS

open DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- Consistency localizes: on a consistent log, entry `k` is consistent with the cache
folded over the strict prefix before `k`. -/
theorem consistentFrom_prefix_getElem (c₀ : DSCache StmtIn U)
    (log : List (DSEntry StmtIn U)) (h : ConsistentFrom c₀ log)
    (k : ℕ) (hk : k < log.length) :
    entryConsistent ((log.take k).foldl stepCache c₀) log[k] := by
  induction log generalizing c₀ k with
  | nil => exact absurd hk (by simp)
  | cons e ℓ ih =>
      obtain ⟨he, hℓ⟩ := h
      cases k with
      | zero => simpa using he
      | succ k =>
          have hk' : k < ℓ.length := by simpa using hk
          simpa [List.take_succ_cons, List.foldl_cons] using
            ih (stepCache c₀ e) hℓ k hk'

/-- **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache
misses. -/
theorem fresh_at_firstOfClass_hash
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (he : log[k] = ⟨.inl q, u⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).1 q = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨u', hu'⟩
  -- provenance: the record comes from a prefix entry
  rcases cacheFold_hash_mem _ _ hu' with h0 | hmem
  · simp at h0
  · -- consistency pins our answer to the cached one
    have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
    rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
    have hu : u = u' := hc u' hu'
    subst hu
    -- the prefix entry equals ours — contradicting first-of-class
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hgetj : log[j]'hjlog = ⟨.inl q, u⟩ := by
      simp only [List.getElem_take] at hjE
      exact hjE
    have := (hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)).1
    exact this (hgetj.trans he.symm)

/-- **Freshness (forward case)**: at a class-first slot holding a forward permutation
entry, the pair cache has no record with that forward key. -/
theorem fresh_at_firstOfClass_perm
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {sIn b : CanonicalSpongeState U}
    (he : log[k] = ⟨.inr (.inl sIn), b⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2.find?
      (fun w => w.1 = sIn) = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨w, hw⟩
  obtain ⟨w1, w2⟩ := w
  have hwmem : (w1, w2) ∈ ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    List.mem_of_find?_eq_some hw
  have hwkey : w1 = sIn := by
    have := List.find?_some hw
    simpa using this
  subst hwkey
  -- consistency pins our answer to the cached value
  have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
  rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
  have hb : b = w2 := hc (w1, w2) hw
  subst hb
  -- provenance: the pair comes from a forward or inverse prefix entry
  rcases cacheFold_pair_mem _ _ hwmem with h0 | hmem | hmem
  · simp at h0
  · -- forward creator: same entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.1 (by show log[j]'hjlog = log[k]; rw [hjE, he])
  · -- inverse creator: the mirror entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.2 (by show log[j]'hjlog = mirrorOf log[k]; rw [hjE, he, Paper.mirrorOf_fwd])

/-- **Freshness (inverse case)**: at a class-first slot holding an inverse permutation
entry, the pair cache has no record with that value key. -/
theorem fresh_at_firstOfClass_permInv
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {sOut a : CanonicalSpongeState U}
    (he : log[k] = ⟨.inr (.inr sOut), a⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2.find?
      (fun w => w.2 = sOut) = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨w, hw⟩
  obtain ⟨w1, w2⟩ := w
  have hwmem : (w1, w2) ∈ ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    List.mem_of_find?_eq_some hw
  have hwkey : w2 = sOut := by
    have := List.find?_some hw
    simpa using this
  subst hwkey
  have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
  rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
  have ha : a = w1 := hc (w1, w2) hw
  subst ha
  rcases cacheFold_pair_mem _ _ hwmem with h0 | hmem | hmem
  · simp at h0
  · -- forward creator: the mirror entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.2 (by show log[j]'hjlog = mirrorOf log[k]; rw [hjE, he, Paper.mirrorOf_inv])
  · -- inverse creator: same entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.1 (by show log[j]'hjlog = log[k]; rw [hjE, he])

/-! ## Cache no-ops (step-1 work-order items (i)+(ii)) -/

/-- A hash entry whose key is cached is a `stepCache` no-op. -/
theorem stepCache_noop_hash {c : DSCache StmtIn U} {q : StmtIn}
    (h : (c.1 q).isSome) (u : Vector U SpongeSize.C) :
    stepCache c ⟨.inl q, u⟩ = c := by
  show (match c.1 q with
    | none => (c.1.cacheQuery q u, c.2)
    | some _ => c) = c
  rcases hq : c.1 q with _ | v
  · rw [hq] at h; cases h
  · rfl

/-- A forward entry whose key is cached is a `stepCache` no-op. -/
theorem stepCache_noop_perm {c : DSCache StmtIn U} {sIn : CanonicalSpongeState U}
    (h : (c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = sIn)).isSome) (b : CanonicalSpongeState U) :
    stepCache c ⟨.inr (.inl sIn), b⟩ = c := by
  show (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = sIn) with
    | none => (c.1, c.2.concat (sIn, b))
    | some _ => c) = c
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = sIn) with _ | v
  · rw [hf] at h; cases h
  · rfl

/-- An inverse entry whose key is cached is a `stepCache` no-op. -/
theorem stepCache_noop_permInv {c : DSCache StmtIn U} {sOut : CanonicalSpongeState U}
    (h : (c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = sOut)).isSome) (a : CanonicalSpongeState U) :
    stepCache c ⟨.inr (.inr sOut), a⟩ = c := by
  show (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = sOut) with
    | none => (c.1, c.2.concat (a, sOut))
    | some _ => c) = c
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = sOut) with _ | v
  · rw [hf] at h; cases h
  · rfl

/-- After folding any entry, that entry's key is cached (fresh ⟹ created; hit ⟹ was there).
The work-order item (i) core: processing an entry guarantees its key. -/
theorem key_cached_after_step_hash (c : DSCache StmtIn U) (q : StmtIn)
    (u : Vector U SpongeSize.C) :
    ((stepCache c ⟨.inl q, u⟩).1 q).isSome := by
  rcases hq : c.1 q with _ | v
  · rw [stepCache_caches_fresh_hash c hq]; exact Option.isSome_some
  · rw [stepCache_noop_hash (by rw [hq]; rfl) u, hq]; exact Option.isSome_some

/-- After folding a forward entry, its forward key is cached. -/
theorem key_cached_after_step_perm (c : DSCache StmtIn U)
    (sIn b : CanonicalSpongeState U) :
    ((stepCache c ⟨.inr (.inl sIn), b⟩).2.find?
      (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn)).isSome := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = sIn) with _ | v
  · have hmem := stepCache_caches_fresh_perm c (b := b) hf
    exact List.find?_isSome.mpr ⟨(sIn, b), hmem, by simp⟩
  · rw [stepCache_noop_perm (by rw [hf]; rfl) b, hf]; exact Option.isSome_some

/-- After folding an inverse entry, its value key is cached. -/
theorem key_cached_after_step_permInv (c : DSCache StmtIn U)
    (sOut a : CanonicalSpongeState U) :
    ((stepCache c ⟨.inr (.inr sOut), a⟩).2.find?
      (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut)).isSome := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = sOut) with _ | v
  · have hmem := stepCache_caches_fresh_permInv c (a := a) hf
    exact List.find?_isSome.mpr ⟨(a, sOut), hmem, by simp⟩
  · rw [stepCache_noop_permInv (by rw [hf]; rfl) a, hf]; exact Option.isSome_some

/-! ## Cross-key caching under consistency (step-1 item (iii) core; the trap-corrected
statements — the pure-cache versions are FALSE at forward/inverse hits, where the cached
pair's other component may differ; `entryConsistent` pins it). -/

/-- After a consistent forward step, the **inverse** key is cached: fresh creates `(a, b)`
(serving the `w.2 = b` lookup); a hit pins `b` to the found pair's value by consistency. -/
theorem swapKey_cached_after_consistent_perm {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hc : entryConsistent c (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U)) :
    ((stepCache c ⟨.inr (.inl a), b⟩).2.find?
      (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = b)).isSome := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = a) with _ | w
  · -- fresh: the created pair (a, b) serves the inverse lookup
    have hmem := stepCache_caches_fresh_perm c (b := b) hf
    exact List.find?_isSome.mpr ⟨(a, b), hmem, by simp⟩
  · -- hit: consistency pins b = w.2; the found pair serves the inverse lookup
    have hb : b = w.2 := hc w hf
    have hwmem : w ∈ c.2 := List.mem_of_find?_eq_some hf
    rw [stepCache_noop_perm (by rw [hf]; rfl) b]
    exact List.find?_isSome.mpr ⟨w, hwmem, by simp [hb]⟩

/-- After a consistent inverse step, the **forward** key is cached: fresh creates `(a, b)`
(serving the `w.1 = a` lookup); a hit pins `a` to the found pair's key by consistency. -/
theorem swapKey_cached_after_consistent_permInv {c : DSCache StmtIn U}
    {b a : CanonicalSpongeState U}
    (hc : entryConsistent c (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)) :
    ((stepCache c ⟨.inr (.inr b), a⟩).2.find?
      (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = a)).isSome := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = b) with _ | w
  · have hmem := stepCache_caches_fresh_permInv c (a := a) hf
    exact List.find?_isSome.mpr ⟨(a, b), hmem, by simp⟩
  · have ha : a = w.1 := hc w hf
    have hwmem : w ∈ c.2 := List.mem_of_find?_eq_some hf
    rw [stepCache_noop_permInv (by rw [hf]; rfl) a]
    exact List.find?_isSome.mpr ⟨w, hwmem, by simp [ha]⟩

/-! ## Exact record caching under consistency -/

/-- After a consistent hash step, the exact logged hash answer is cached. -/
theorem hashRecord_cached_after_consistent {c : DSCache StmtIn U}
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (hc : entryConsistent c (⟨.inl q, u⟩ : DSEntry StmtIn U)) :
    (stepCache c ⟨.inl q, u⟩).1 q = some u := by
  rcases hq : c.1 q with _ | u'
  · exact stepCache_caches_fresh_hash c hq
  · have hu : u = u' := hc u' hq
    rw [stepCache_noop_hash (by rw [hq]; rfl) u, hu, hq]

/-- After a consistent forward step, the exact pair `(input, output)` is cached. -/
theorem pairRecord_cached_after_consistent_perm {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hc : entryConsistent c (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U)) :
    (a, b) ∈ (stepCache c ⟨.inr (.inl a), b⟩).2 := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.1 = a) with _ | w
  · exact stepCache_caches_fresh_perm c (b := b) hf
  · obtain ⟨w1, w2⟩ := w
    have hwa : w1 = a := by
      have := List.find?_some hf
      simpa using this
    have hb : b = w2 := hc (w1, w2) hf
    have hwmem : (w1, w2) ∈ c.2 := List.mem_of_find?_eq_some hf
    rw [stepCache_noop_perm (by rw [hf]; rfl) b]
    cases hwa
    cases hb
    exact hwmem

/-- After a consistent inverse step, the exact pair `(answer, query)` is cached. -/
theorem pairRecord_cached_after_consistent_permInv {c : DSCache StmtIn U}
    {b a : CanonicalSpongeState U}
    (hc : entryConsistent c (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U)) :
    (a, b) ∈ (stepCache c ⟨.inr (.inr b), a⟩).2 := by
  rcases hf : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
      w.2 = b) with _ | w
  · exact stepCache_caches_fresh_permInv c (a := a) hf
  · obtain ⟨w1, w2⟩ := w
    have hwb : w2 = b := by
      have := List.find?_some hf
      simpa using this
    have ha : a = w1 := hc (w1, w2) hf
    have hwmem : (w1, w2) ∈ c.2 := List.mem_of_find?_eq_some hf
    rw [stepCache_noop_permInv (by rw [hf]; rfl) a]
    cases hwb
    cases ha
    exact hwmem

/-! ## `isSome`-persistence through the fold (item (iii) assembly consumers) -/

/-- A cached hash key stays cached through any fold suffix (`isSome` form). -/
theorem hashKey_isSome_foldl_mono (c : DSCache StmtIn U) (ℓ : List (DSEntry StmtIn U))
    {q : StmtIn} (h : (c.1 q).isSome) :
    ((ℓ.foldl stepCache c).1 q).isSome := by
  rcases hq : c.1 q with _ | u
  · rw [hq] at h; cases h
  · rw [foldl_stepCache_hash_mono c ℓ hq]; rfl

/-- A satisfiable pair-cache predicate stays satisfiable through any fold suffix. -/
theorem pairKey_isSome_foldl_mono (c : DSCache StmtIn U) (ℓ : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U → Bool}
    (h : (c.2.find? p).isSome) :
    (((ℓ.foldl stepCache c).2).find? p).isSome := by
  rcases List.find?_isSome.mp h with ⟨w, hwmem, hwp⟩
  exact List.find?_isSome.mpr ⟨w, foldl_stepCache_pair_mono c ℓ hwmem, hwp⟩

/-! ## The eraseIdx transport pair (item (iii) assembly): erasing a no-op step preserves
consistency forwards and anchoredness backwards. -/

/-- Erasing a no-op entry preserves consistency. -/
theorem consistentFrom_eraseIdx_of_noop (c₀ : DSCache StmtIn U)
    (log : List (DSEntry StmtIn U)) (k : ℕ) (hk : k < log.length)
    (hnoop : stepCache ((log.take k).foldl stepCache c₀) log[k]
      = (log.take k).foldl stepCache c₀)
    (h : ConsistentFrom c₀ log) :
    ConsistentFrom c₀ (log.eraseIdx k) := by
  induction log generalizing c₀ k with
  | nil => exact absurd hk (by simp)
  | cons e ℓ ih =>
      obtain ⟨he, hℓ⟩ := h
      cases k with
      | zero =>
          simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hnoop
          rw [List.eraseIdx_cons_zero]
          rwa [hnoop] at hℓ
      | succ k =>
          have hk' : k < ℓ.length := by simpa using hk
          rw [List.eraseIdx_cons_succ]
          refine ⟨he, ih (stepCache c₀ e) k hk' ?_ hℓ⟩
          simpa [List.take_succ_cons, List.foldl_cons] using hnoop

/-- Erasing a no-op entry reflects anchoredness: a collision in the erased log is a
collision in the original. -/
theorem anchoredFrom_of_eraseIdx_of_noop (c₀ : DSCache StmtIn U)
    (log : List (DSEntry StmtIn U)) (k : ℕ) (hk : k < log.length)
    (hnoop : stepCache ((log.take k).foldl stepCache c₀) log[k]
      = (log.take k).foldl stepCache c₀)
    (hA : AnchoredFrom c₀ (log.eraseIdx k)) :
    AnchoredFrom c₀ log := by
  induction log generalizing c₀ k with
  | nil => exact absurd hk (by simp)
  | cons e ℓ ih =>
      cases k with
      | zero =>
          simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at hnoop
          rw [List.eraseIdx_cons_zero] at hA
          exact Or.inr (by rwa [hnoop])
      | succ k =>
          have hk' : k < ℓ.length := by simpa using hk
          rw [List.eraseIdx_cons_succ] at hA
          rcases hA with hcol | hA
          · exact Or.inl hcol
          · refine Or.inr (ih (stepCache c₀ e) k hk' ?_ hA)
            simpa [List.take_succ_cons, List.foldl_cons] using hnoop

/-! ## Class-redundant steps are no-ops under consistency -/

private lemma take_split_getElem {α : Type _} (l : List α) {j k : ℕ}
    (hjlog : j < l.length) (hjk : j < k) :
    l.take k = l.take j ++ l[j]'hjlog :: (l.drop (j + 1)).take (k - j - 1) := by
  have hk : k = j + (1 + (k - j - 1)) := by omega
  conv_lhs => rw [hk, List.take_add]
  congr 1
  rw [List.drop_eq_getElem_cons hjlog,
    show 1 + (k - j - 1) = (k - j - 1) + 1 from by omega, List.take_succ_cons]

private lemma foldl_stepCache_take_from_getElem
    (c₀ : DSCache StmtIn U) (log : List (DSEntry StmtIn U)) {j k : ℕ}
    (hjlog : j < log.length) (hjk : j < k) :
    (log.take k).foldl stepCache c₀ =
      ((log.drop (j + 1)).take (k - j - 1)).foldl stepCache
        (stepCache ((log.take j).foldl stepCache c₀) log[j]) := by
  rw [take_split_getElem log hjlog hjk, List.foldl_append, List.foldl_cons]

open DuplexSpongeFS.Paper in
/-- In a consistent log, a class-redundant slot is a `stepCache` no-op at its prefix fold.
This is the cache-equality bridge from `ClassRedAt` to the no-op erasure transport pair. -/
theorem stepCache_noop_of_classRedAt_consistent
    (c₀ : DSCache StmtIn U)
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom c₀ log)
    {k : ℕ} (hk : k < log.length) (hred : ClassRedAt log k hk) :
    stepCache ((log.take k).foldl stepCache c₀) log[k] =
      ((log.take k).foldl stepCache c₀) := by
  rcases hred with hmem | hmem
  · obtain ⟨j, hjtake, hgetj⟩ := List.mem_iff_getElem.mp hmem
    have hjk : j < k := lt_of_lt_of_le hjtake (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjk hk
    have hsame : log[j] = log[k] := by
      simp only [List.getElem_take] at hgetj
      exact hgetj
    have hfold := foldl_stepCache_take_from_getElem c₀ log hjlog hjk
    rcases hke : log[k] with ⟨t, ans⟩
    rcases t with q | a | b
    · have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).1 q).isSome := by
        rw [hsame, hke]
        exact key_cached_after_step_hash _ q ans
      have hcachedK :
          (((log.take k).foldl stepCache c₀).1 q).isSome := by
        rw [hfold]
        exact hashKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_hash hcachedK ans
    · have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.1 = a)).isSome := by
        rw [hsame, hke]
        exact key_cached_after_step_perm _ a ans
      have hcachedK :
          (((log.take k).foldl stepCache c₀).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.1 = a)).isSome := by
        rw [hfold]
        exact pairKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_perm hcachedK ans
    · have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.2 = b)).isSome := by
        rw [hsame, hke]
        exact key_cached_after_step_permInv _ b ans
      have hcachedK :
          (((log.take k).foldl stepCache c₀).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.2 = b)).isSome := by
        rw [hfold]
        exact pairKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_permInv hcachedK ans
  · obtain ⟨j, hjtake, hgetj⟩ := List.mem_iff_getElem.mp hmem
    have hjk : j < k := lt_of_lt_of_le hjtake (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjk hk
    have hmirror : log[j] = mirrorOf log[k] := by
      simp only [List.getElem_take] at hgetj
      exact hgetj
    have hcj := consistentFrom_prefix_getElem c₀ log hcons j hjlog
    have hfold := foldl_stepCache_take_from_getElem c₀ log hjlog hjk
    rcases hke : log[k] with ⟨t, ans⟩
    rcases t with q | a | b
    · have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).1 q).isSome := by
        rw [hmirror, hke, mirrorOf_hash]
        exact key_cached_after_step_hash _ q ans
      have hcachedK :
          (((log.take k).foldl stepCache c₀).1 q).isSome := by
        rw [hfold]
        exact hashKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_hash hcachedK ans
    · have hcjInv :
          entryConsistent ((log.take j).foldl stepCache c₀)
            (⟨.inr (.inr ans), a⟩ : DSEntry StmtIn U) := by
        simpa [hmirror, hke, mirrorOf_fwd] using hcj
      have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.1 = a)).isSome := by
        rw [hmirror, hke, mirrorOf_fwd]
        exact swapKey_cached_after_consistent_permInv hcjInv
      have hcachedK :
          (((log.take k).foldl stepCache c₀).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.1 = a)).isSome := by
        rw [hfold]
        exact pairKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_perm hcachedK ans
    · have hcjFwd :
          entryConsistent ((log.take j).foldl stepCache c₀)
            (⟨.inr (.inl ans), b⟩ : DSEntry StmtIn U) := by
        simpa [hmirror, hke, mirrorOf_inv] using hcj
      have hcachedJ :
          ((stepCache ((log.take j).foldl stepCache c₀) log[j]).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.2 = b)).isSome := by
        rw [hmirror, hke, mirrorOf_inv]
        exact swapKey_cached_after_consistent_perm hcjFwd
      have hcachedK :
          (((log.take k).foldl stepCache c₀).2.find?
            (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
              w.2 = b)).isSome := by
        rw [hfold]
        exact pairKey_isSome_foldl_mono _ _ hcachedJ
      exact stepCache_noop_permInv hcachedK ans

open DuplexSpongeFS.Paper in
/-- A class-redundant erasure preserves consistency in a consistent log. -/
theorem consistentFrom_eraseIdx_classRed (c₀ : DSCache StmtIn U)
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom c₀ log)
    {k : ℕ} (hk : k < log.length) (hred : ClassRedAt log k hk) :
    ConsistentFrom c₀ (log.eraseIdx k) :=
  consistentFrom_eraseIdx_of_noop c₀ log k hk
    (stepCache_noop_of_classRedAt_consistent c₀ hcons hk hred) hcons

open DuplexSpongeFS.Paper in
/-- A class-redundant erasure reflects anchoredness in a consistent log. -/
theorem anchoredFrom_of_eraseIdx_classRed (c₀ : DSCache StmtIn U)
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom c₀ log)
    {k : ℕ} (hk : k < log.length) (hred : ClassRedAt log k hk)
    (hA : AnchoredFrom c₀ (log.eraseIdx k)) :
    AnchoredFrom c₀ log :=
  anchoredFrom_of_eraseIdx_of_noop c₀ log k hk
    (stepCache_noop_of_classRedAt_consistent c₀ hcons hk hred) hA

open DuplexSpongeFS.Paper in
/-- Consistency survives the full paper dedup pass. -/
theorem consistentFrom_removeRedundantEntryDSPaper (c₀ : DSCache StmtIn U)
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom c₀ log) :
    ConsistentFrom c₀ (removeRedundantEntryDSPaper log).1 :=
  dedup_invariant (fun L => ConsistentFrom c₀ L)
    (fun _ _ hk hred hP => consistentFrom_eraseIdx_classRed c₀ hP hk hred)
    log hcons

open DuplexSpongeFS.Paper in
private theorem anchoredFrom_of_removeRedundantEntryDSPaper_aux (c₀ : DSCache StmtIn U) :
    ∀ (n : ℕ) (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)),
      log.length ≤ n →
      ConsistentFrom c₀ log →
      AnchoredFrom c₀ (removeRedundantEntryDSPaper log).1 →
      AnchoredFrom c₀ log := by
  intro n
  induction n with
  | zero =>
      intro log hlen _ hA
      have hlog : log = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hlog
      have hnr : NoRedundantEntryDSPaper
          ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
        fun idx => absurd idx.isLt (by simp)
      rw [removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper _ hnr] at hA
      exact hA
  | succ n ih =>
      intro log hlen hcons hA
      by_cases hex : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
      · rw [removeRedundantEntryDSPaper_step log hex] at hA
        have hk := (Classical.choose hex).isLt
        have hred : ClassRedAt log (Classical.choose hex).val hk :=
          (classRedAt_iff_redundant log (Classical.choose hex)).mpr
            (Classical.choose_spec hex)
        have hconsErase : ConsistentFrom c₀ (log.eraseIdx (Classical.choose hex).val) :=
          consistentFrom_eraseIdx_classRed c₀ hcons hk hred
        have hlenErase : (log.eraseIdx (Classical.choose hex).val).length ≤ n := by
          have := List.length_eraseIdx_add_one hk
          omega
        exact anchoredFrom_of_eraseIdx_classRed c₀ hcons hk hred
          (ih (log.eraseIdx (Classical.choose hex).val) hlenErase hconsErase hA)
      · rw [removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper _
          (fun idx => not_exists.mp hex idx)] at hA
        exact hA

open DuplexSpongeFS.Paper in
/-- Anchoredness of the paper-deduplicated log reflects back to the original consistent log. -/
theorem anchoredFrom_of_removeRedundantEntryDSPaper (c₀ : DSCache StmtIn U)
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom c₀ log)
    (hA : AnchoredFrom c₀ (removeRedundantEntryDSPaper log).1) :
    AnchoredFrom c₀ log :=
  anchoredFrom_of_removeRedundantEntryDSPaper_aux c₀ log.length log le_rfl hcons hA

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_noop_hash
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_noop_perm
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_noop_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.key_cached_after_step_hash
#print axioms DuplexSpongeFS.EagerLazyDS.key_cached_after_step_perm
#print axioms DuplexSpongeFS.EagerLazyDS.key_cached_after_step_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_perm
#print axioms DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.hashRecord_cached_after_consistent
#print axioms DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_perm
#print axioms DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.hashKey_isSome_foldl_mono
#print axioms DuplexSpongeFS.EagerLazyDS.pairKey_isSome_foldl_mono
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_of_noop
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_of_noop
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_noop_of_classRedAt_consistent
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_classRed
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_classRed
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_removeRedundantEntryDSPaper
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper
