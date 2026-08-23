/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Correspondence

/-!
# Cache provenance for the Lemma 5.8 dedup reduction (issue #316)

The one remaining Lemma-5.8 obligation (`EPaperReduction`,
`Lemma58Correspondence.lean`) is pure list combinatorics: on a consistent log, `EPaper`
forces an anchored collision.  Its extraction argument consumes four cache-fold facts,
proven here:

* **Provenance** (`cacheFold_hash_mem` / `cacheFold_pair_mem`): every record of the folded
  cache comes from a log entry — a cached hash answer from a hash entry, a cached
  permutation pair from a forward entry or its inverse mirror.
* **Persistence** (`stepCache_hash_mono` / `stepCache_pair_mono` + the fold closures):
  `stepCache` never deletes; records survive to every later fold point.
* **Fresh-caching** (`stepCache_caches_fresh_*`): a fresh entry (cache lookup misses)
  creates its record.
* **Slot transport** (`mem_slotList_of_hash` / `mem_slotList_of_pair_fst` /
  `mem_slotList_of_pair_snd`): cached records put their capacities in `slotList` — both
  components for permutation pairs (so query-side capacities of cached permutation entries
  ARE slots; only hash query sides are excluded, matching CO25 Eqs. 25/26's disjuncts).

With these, the extraction plan for `EPaperReduction` is mechanical (posted on #316): pull
the two coinciding dedup entries back to their raw class-first slots (order-preserving,
`dedup_pair_of_firstOfClassAt` machinery); the earlier one is fresh at its slot and caches
(fresh-caching), persists (persistence), lands its capacities in `slotList` (transport);
the later one is fresh at its slot (consistency + first-of-class) and its sampled answer
capacity hits the earlier slot or its own query capacity — exactly `collisionStep`, hence
`AnchoredFrom`.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.EagerLazyDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-! ## Persistence: `stepCache` never deletes -/

/-- A cached hash record survives one fold step. -/
theorem stepCache_hash_mono' (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    (stepCache c e).1 q = some u := by
  rcases e with ⟨t, ans⟩
  rcases t with q' | sIn | sOut
  · show (match c.1 q' with
      | none => (c.1.cacheQuery q' ans, c.2)
      | some _ => c).1 q = some u
    rcases hq' : c.1 q' with _ | u'
    · simp only
      rcases eq_or_ne q q' with rfl | hne
      · rw [h] at hq'; cases hq'
      · simpa [OracleSpec.QueryCache.cacheQuery, Function.update_of_ne hne] using h
    · simpa using h
  · show (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with
      | none => (c.1, c.2.concat (sIn, ans))
      | some _ => c).1 q = some u
    rcases c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) <;> simpa using h
  · show (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with
      | none => (c.1, c.2.concat (ans, sOut))
      | some _ => c).1 q = some u
    rcases c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) <;> simpa using h

/-- A cached permutation pair survives one fold step. -/
theorem stepCache_pair_mono (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (h : p ∈ c.2) :
    p ∈ (stepCache c e).2 := by
  rcases e with ⟨t, ans⟩
  rcases t with q' | sIn | sOut
  · show p ∈ (match c.1 q' with
      | none => (c.1.cacheQuery q' ans, c.2)
      | some _ => c).2
    rcases c.1 q' <;> simpa using h
  · show p ∈ (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with
      | none => (c.1, c.2.concat (sIn, ans))
      | some _ => c).2
    rcases c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with _ | _
    · simp only [List.concat_eq_append]
      exact List.mem_append_left _ h
    · simpa using h
  · show p ∈ (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with
      | none => (c.1, c.2.concat (ans, sOut))
      | some _ => c).2
    rcases c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with _ | _
    · simp only [List.concat_eq_append]
      exact List.mem_append_left _ h
    · simpa using h

/-- Permutation pairs persist through any fold suffix. -/
theorem foldl_stepCache_pair_mono (c : DSCache StmtIn U)
    (ℓ : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (h : p ∈ c.2) :
    p ∈ (ℓ.foldl stepCache c).2 := by
  induction ℓ generalizing c with
  | nil => exact h
  | cons e ℓ ih => exact ih (stepCache c e) (stepCache_pair_mono c e h)

/-! ## Fresh-caching: a missing key gets its record created -/

/-- A fresh hash entry creates its record. -/
theorem stepCache_caches_fresh_hash (c : DSCache StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (hfresh : c.1 q = none) :
    (stepCache c ⟨.inl q, u⟩).1 q = some u := by
  show (match c.1 q with
    | none => (c.1.cacheQuery q u, c.2)
    | some _ => c).1 q = some u
  rw [hfresh]
  simp [OracleSpec.QueryCache.cacheQuery]

/-- A fresh forward permutation entry creates its pair. -/
theorem stepCache_caches_fresh_perm (c : DSCache StmtIn U)
    {sIn b : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) = none) :
    (sIn, b) ∈ (stepCache c ⟨.inr (.inl sIn), b⟩).2 := by
  show (sIn, b) ∈ (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with
    | none => (c.1, c.2.concat (sIn, b))
    | some _ => c).2
  rw [hfresh]
  simp

/-- A fresh inverse permutation entry creates its (answer, query) pair. -/
theorem stepCache_caches_fresh_permInv (c : DSCache StmtIn U)
    {sOut a : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) = none) :
    (a, sOut) ∈ (stepCache c ⟨.inr (.inr sOut), a⟩).2 := by
  show (a, sOut) ∈ (match c.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with
    | none => (c.1, c.2.concat (a, sOut))
    | some _ => c).2
  rw [hfresh]
  simp

/-! ## Provenance: every cache record comes from a log entry -/

/-- Every cached hash answer in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a
hash entry of `ℓ`. -/
theorem cacheFold_hash_mem (c₀ : DSCache StmtIn U) (ℓ : List (DSEntry StmtIn U))
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (h : (ℓ.foldl stepCache c₀).1 q = some u) :
    c₀.1 q = some u ∨ (⟨.inl q, u⟩ : DSEntry StmtIn U) ∈ ℓ := by
  induction ℓ generalizing c₀ with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rcases ih (stepCache c₀ e) h with hstep | hmem
      · -- analyse one step
        rcases e with ⟨t, ans⟩
        rcases t with q' | sIn | sOut
        · revert hstep
          show (match c₀.1 q' with
            | none => (c₀.1.cacheQuery q' ans, c₀.2)
            | some _ => c₀).1 q = some u → _
          rcases hq' : c₀.1 q' with _ | u'
          · intro hstep
            simp only at hstep
            rcases eq_or_ne q q' with rfl | hne
            · simp only [OracleSpec.QueryCache.cacheQuery, Function.update_self] at hstep
              cases hstep
              exact Or.inr (List.mem_cons_self ..)
            · simp only [OracleSpec.QueryCache.cacheQuery,
                Function.update_of_ne hne] at hstep
              exact Or.inl hstep
          · intro hstep
            exact Or.inl hstep
        · revert hstep
          show (match c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with
            | none => (c₀.1, c₀.2.concat (sIn, ans))
            | some _ => c₀).1 q = some u → _
          rcases c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) <;> exact fun h => Or.inl h
        · revert hstep
          show (match c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with
            | none => (c₀.1, c₀.2.concat (ans, sOut))
            | some _ => c₀).1 q = some u → _
          rcases c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) <;> exact fun h => Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ hmem)

/-- Every cached permutation pair in a fold of `ℓ` over `c₀` either was in `c₀` or comes
from a forward entry or an inverse entry of `ℓ` (the pair stores `(forwardKey, value)`;
an inverse entry `⟨p⁻¹ b, a⟩` stores `(a, b)`). -/
theorem cacheFold_pair_mem (c₀ : DSCache StmtIn U) (ℓ : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U}
    (h : p ∈ (ℓ.foldl stepCache c₀).2) :
    p ∈ c₀.2 ∨ (⟨.inr (.inl p.1), p.2⟩ : DSEntry StmtIn U) ∈ ℓ ∨
      (⟨.inr (.inr p.2), p.1⟩ : DSEntry StmtIn U) ∈ ℓ := by
  induction ℓ generalizing c₀ with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rcases ih (stepCache c₀ e) h with hstep | hmem | hmem
      · rcases e with ⟨t, ans⟩
        rcases t with q' | sIn | sOut
        · revert hstep
          show p ∈ (match c₀.1 q' with
            | none => (c₀.1.cacheQuery q' ans, c₀.2)
            | some _ => c₀).2 → _
          rcases c₀.1 q' <;> exact fun h => Or.inl h
        · revert hstep
          show p ∈ (match c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with
            | none => (c₀.1, c₀.2.concat (sIn, ans))
            | some _ => c₀).2 → _
          rcases c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.1 = sIn) with _ | _
          · intro hstep
            simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hstep
            rcases hstep with h | rfl
            · exact Or.inl h
            · exact Or.inr (Or.inl (List.mem_cons_self ..))
          · exact fun h => Or.inl h
        · revert hstep
          show p ∈ (match c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with
            | none => (c₀.1, c₀.2.concat (ans, sOut))
            | some _ => c₀).2 → _
          rcases c₀.2.find? (fun w : CanonicalSpongeState U × CanonicalSpongeState U => w.2 = sOut) with _ | _
          · intro hstep
            simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hstep
            rcases hstep with h | rfl
            · exact Or.inl h
            · exact Or.inr (Or.inr (List.mem_cons_self ..))
          · exact fun h => Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hmem))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hmem))

/-! ## Slot transport: cached records put their capacities in `slotList` -/

/-- A cached hash answer is a slot. -/
theorem mem_slotList_of_hash {c : DSCache StmtIn U}
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    u ∈ slotList c := by
  classical
  unfold slotList
  refine List.mem_append_left _ ?_
  refine List.mem_filterMap.mpr ⟨q, ?_, h⟩
  refine Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ q, ?_⟩)
  rw [h]
  rfl

/-- A cached pair's forward-key capacity is a slot. -/
theorem mem_slotList_of_pair_fst {c : DSCache StmtIn U}
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (h : p ∈ c.2) :
    p.1.capacitySegment ∈ slotList c := by
  classical
  unfold slotList
  refine List.mem_append_right _ ?_
  exact List.mem_flatMap.mpr ⟨p, h, by simp⟩

/-- A cached pair's value capacity is a slot. -/
theorem mem_slotList_of_pair_snd {c : DSCache StmtIn U}
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (h : p ∈ c.2) :
    p.2.capacitySegment ∈ slotList c := by
  classical
  unfold slotList
  refine List.mem_append_right _ ?_
  exact List.mem_flatMap.mpr ⟨p, h, by simp⟩

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono'
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_pair_mono
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_stepCache_pair_mono
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_hash
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_perm
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_permInv
#print axioms DuplexSpongeFS.EagerLazyDS.cacheFold_hash_mem
#print axioms DuplexSpongeFS.EagerLazyDS.cacheFold_pair_mem
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_fst
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_snd
