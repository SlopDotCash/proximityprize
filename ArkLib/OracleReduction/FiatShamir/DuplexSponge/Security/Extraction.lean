/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Freshness

/-!
# Item (v) infrastructure: positional anchoring + certificate-freshness (issue #316)

The three bridge bricks that make the dedup-side disjunct extraction pure per-disjunct
mechanics:

* `swapEntry_eq_mirrorOf` — the Correspondence/Engine vocabulary bridge (the two parallel
  defs on the same sigma agree);
* `firstOfClassAt_of_noRedundant` — the dedup's own `NoRedundantEntryDSPaper` certificate
  gives first-of-class at every index (so the landed `fresh_at_firstOfClass_*` theorems
  apply on the dedup with no pullback);
* `anchoredFrom_of_at` — positional introduction: a `collisionStep` at any single position
  (against the prefix fold) yields `AnchoredFrom`.

With these, item (v) is: per `EPaper` disjunct, the anchor index is fresh (certificate
freshness), the earlier coincidence entry was fresh at ITS index, cached
(`stepCache_caches_fresh_*`), persisted (`foldl_stepCache_*_mono`), its capacity is a slot
(`mem_slotList_of_*`), and the anchor's answer capacity hits it — `collisionStep`, hence
`AnchoredFrom` by `anchoredFrom_of_at`; the `j' = j` cases are `collisionStep`'s self-anchor
disjunct, and `E_func` dies by freshness + pair provenance.
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

/-- The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map. -/
theorem swapEntry_eq_mirrorOf (e : DSEntry StmtIn U) :
    swapEntry e = Paper.mirrorOf e := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a | b <;> rfl

/-- **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives
first-of-class at every index. -/
theorem firstOfClassAt_of_noRedundant
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base) (j : Fin base.length) :
    Paper.FirstOfClassAt base j := by
  intro j' hj'
  by_contra hcon
  push_neg at hcon
  refine hnr j ((redundantEntryDSPaper_iff_sameClass base j).mpr ⟨j', hj', ?_⟩)
  rcases Classical.em (base[j'] = base[j]) with heq | hne
  · exact Or.inl heq
  · have hmir := hcon (fun h => hne h)
    refine Or.inr ?_
    rw [swapEntry_eq_mirrorOf]
    exact hmir

/-- **Positional anchoring**: a `collisionStep` at any position (against the prefix fold)
yields `AnchoredFrom`. -/
theorem anchoredFrom_of_at (c₀ : DSCache StmtIn U)
    (ℓ : List (DSEntry StmtIn U)) (j : Fin ℓ.length)
    (hcol : collisionStep ℓ[j].1 ((ℓ.take j).foldl stepCache c₀) ℓ[j].2) :
    AnchoredFrom c₀ ℓ := by
  induction ℓ generalizing c₀ with
  | nil => exact j.elim0
  | cons e ℓ' ih =>
      rcases j with ⟨jv, hjv⟩
      cases jv with
      | zero =>
          simp only [List.getElem_cons_zero, List.take_zero, List.foldl_nil] at hcol
          exact Or.inl hcol
      | succ jv =>
          have hjv' : jv < ℓ'.length := by simpa using hjv
          refine Or.inr (ih (stepCache c₀ e) ⟨jv, hjv'⟩ ?_)
          simpa [List.take_succ_cons, List.foldl_cons] using hcol

/-! ## Prefix-fold bookkeeping -/

/-- Folding one more prefix entry is one `stepCache` step. -/
theorem foldl_take_succ_eq (l : List (DSEntry StmtIn U)) (j : ℕ) (hj : j < l.length)
    (c₀ : DSCache StmtIn U) :
    (l.take (j + 1)).foldl stepCache c₀
      = stepCache ((l.take j).foldl stepCache c₀) l[j] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj]
  rw [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A satisfiable pair predicate at the `(j'+1)`-prefix fold persists to any larger prefix. -/
theorem pairKey_isSome_take_of_le {l : List (DSEntry StmtIn U)} {j' j : ℕ}
    (hj' : j' + 1 ≤ j) (c₀ : DSCache StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U → Bool}
    (h : (((l.take (j' + 1)).foldl stepCache c₀).2.find? p).isSome) :
    (((l.take j).foldl stepCache c₀).2.find? p).isSome := by
  have hsplit : l.take j
      = l.take (j' + 1) ++ (l.take j).drop (j' + 1) := by
    conv_lhs => rw [← List.take_append_drop (j' + 1) (l.take j)]
    rw [List.take_take, min_eq_left hj']
  rw [hsplit, List.foldl_append]
  exact pairKey_isSome_foldl_mono _ _ h

/-! ## The `E_func` arm is impossible on a certified consistent list -/

/-- **`E_func` refutation**: on a no-redundancy, consistent list, no forward entry can share
its key with an earlier forward query or inverse answer — the earlier entry was fresh at its
slot, cached the pair with that forward key, the record persisted, contradicting the later
entry's certificate freshness. -/
theorem notFunction_data_impossible
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base)
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) base)
    {j : Fin base.length} {stateIn stateOut : CanonicalSpongeState U}
    (hj : base[j] = ⟨.inr (.inl stateIn), stateOut⟩)
    {j' : Fin base.length} (hj'lt : j' < j)
    (hcoin : (∃ stateOut1, base[j'] = ⟨.inr (.inl stateIn), stateOut1⟩)
      ∨ (∃ stateOut2, base[j'] = ⟨.inr (.inr stateOut2), stateIn⟩)) :
    False := by
  -- the later entry is certificate-fresh: its forward key misses at its prefix fold
  have hfresh_j := fresh_at_firstOfClass_perm hcons
    (firstOfClassAt_of_noRedundant hnr j) hj
  -- but the earlier entry caches a pair with that forward key, which persists
  have hsome : (((base.take j).foldl stepCache ((∅, []) : DSCache StmtIn U)).2.find?
      (fun w : CanonicalSpongeState U × CanonicalSpongeState U =>
        w.1 = stateIn)).isSome := by
    have hstep := foldl_take_succ_eq base j' j'.isLt ((∅, []) : DSCache StmtIn U)
    rcases hcoin with ⟨out1, hj'⟩ | ⟨out2, hj'⟩
    · -- earlier forward entry: fresh at j', caches (stateIn, out1)
      have hfresh_j' := fresh_at_firstOfClass_perm hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hmem : (stateIn, out1) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [hstep, show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_perm _ hfresh_j'
      exact pairKey_isSome_take_of_le (by exact_mod_cast hj'lt)
        ((∅, []) : DSCache StmtIn U)
        (List.find?_isSome.mpr ⟨(stateIn, out1), hmem, by simp⟩)
    · -- earlier inverse entry: fresh at j', caches (stateIn, out2)
      have hfresh_j' := fresh_at_firstOfClass_permInv hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hmem : (stateIn, out2) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [hstep, show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_permInv _ hfresh_j'
      exact pairKey_isSome_take_of_le (by exact_mod_cast hj'lt)
        ((∅, []) : DSCache StmtIn U)
        (List.find?_isSome.mpr ⟨(stateIn, out2), hmem, by simp⟩)
  rw [hfresh_j] at hsome
  cases hsome

/-! ## Value-level prefix persistence -/

/-- A hash record at the `(j'+1)`-prefix fold persists (with its value) to any larger
prefix. -/
theorem hashRecord_take_of_le {l : List (DSEntry StmtIn U)} {j' j : ℕ}
    (hj' : j' + 1 ≤ j) (c₀ : DSCache StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (h : ((l.take (j' + 1)).foldl stepCache c₀).1 q = some u) :
    ((l.take j).foldl stepCache c₀).1 q = some u := by
  have hsplit : l.take j = l.take (j' + 1) ++ (l.take j).drop (j' + 1) := by
    conv_lhs => rw [← List.take_append_drop (j' + 1) (l.take j)]
    rw [List.take_take, min_eq_left hj']
  rw [hsplit, List.foldl_append]
  exact foldl_stepCache_hash_mono _ _ h

/-- A pair record at the `(j'+1)`-prefix fold persists to any larger prefix. -/
theorem pairRecord_take_of_le {l : List (DSEntry StmtIn U)} {j' j : ℕ}
    (hj' : j' + 1 ≤ j) (c₀ : DSCache StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U}
    (h : p ∈ ((l.take (j' + 1)).foldl stepCache c₀).2) :
    p ∈ ((l.take j).foldl stepCache c₀).2 := by
  have hsplit : l.take j = l.take (j' + 1) ++ (l.take j).drop (j' + 1) := by
    conv_lhs => rw [← List.take_append_drop (j' + 1) (l.take j)]
    rw [List.take_take, min_eq_left hj']
  rw [hsplit, List.foldl_append]
  exact foldl_stepCache_pair_mono _ _ h

/-! ## The `E_pinv` anchor arm -/

/-- **The `E_pinv` arm anchors a collision** (CO25 Eq. 26 over a certified consistent
list): an inverse entry whose answer capacity coincides with any of the five earlier-
component capacities fires `collisionStep` at its index, hence `AnchoredFrom`. -/
theorem anchored_of_permInv_anchor
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base)
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) base)
    {j : Fin base.length} {stateOut stateIn : CanonicalSpongeState U}
    {capSeg : Vector U SpongeSize.C}
    (hj : base[j] = ⟨.inr (.inr stateOut), stateIn⟩)
    (hcap : stateIn.capacitySegment = capSeg)
    (hcoin :
      (∃ j' < j, ∃ stmt', base[j'] = ⟨.inl stmt', capSeg⟩) ∨
      (∃ j' < j, ∃ sIn1 sOut1, base[j'] = ⟨.inr (.inl sIn1), sOut1⟩ ∧
        sOut1.capacitySegment = capSeg) ∨
      (∃ j' < j, ∃ sIn2 sOut2, base[j'] = ⟨.inr (.inr sOut2), sIn2⟩ ∧
        CanonicalSpongeState.capacitySegment sIn2 = capSeg) ∨
      (∃ j' ≤ j, ∃ sIn3 sOut3, base[j'] = ⟨.inr (.inl sIn3), sOut3⟩ ∧
        sIn3.capacitySegment = capSeg) ∨
      (∃ j' ≤ j, ∃ q a, base[j'] = ⟨.inr (.inr q), a⟩ ∧
        CanonicalSpongeState.capacitySegment q = capSeg)) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) base := by
  classical
  -- the anchor is certificate-fresh
  have hfresh := fresh_at_firstOfClass_permInv hcons
    (firstOfClassAt_of_noRedundant hnr j) hj
  -- fire the positional collision at `j`
  refine anchoredFrom_of_at ((∅, []) : DSCache StmtIn U) base j ?_
  rw [hj]
  refine ⟨hfresh, ?_⟩
  -- the hit conjunct, per disjunct
  rcases hcoin with ⟨j', hj'lt, stmt', hj'⟩ | ⟨j', hj'lt, sIn1, sOut1, hj', hc1⟩ |
    ⟨j', hj'lt, sIn2, sOut2, hj', hc2⟩ | ⟨j', hj'le, sIn3, sOut3, hj', hc3⟩ |
    ⟨j', hj'le, qq, aa, hj', hc4⟩
  · -- earlier hash entry with answer capSeg
    refine Or.inl ?_
    have hfresh' := fresh_at_firstOfClass_hash hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).1 stmt' = some capSeg := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_hash _ hfresh'
    rw [hcap]
    exact mem_slotList_of_hash
      (hashRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier forward entry, answer capacity
    refine Or.inl ?_
    have hfresh' := fresh_at_firstOfClass_perm hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn1, sOut1) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_perm _ hfresh'
    rw [hcap, ← hc1]
    exact mem_slotList_of_pair_snd
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier inverse entry, answer capacity
    refine Or.inl ?_
    have hfresh' := fresh_at_firstOfClass_permInv hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn2, sOut2) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_permInv _ hfresh'
    rw [hcap, ← hc2]
    exact mem_slotList_of_pair_fst
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- forward entry at j' ≤ j, query capacity (j' = j is a constructor clash)
    rcases eq_or_lt_of_le hj'le with heq | hlt
    · subst heq
      rw [hj] at hj'
      simp at hj'
    · refine Or.inl ?_
      have hfresh' := fresh_at_firstOfClass_perm hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hrec : (sIn3, sOut3) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [foldl_take_succ_eq base j' j'.isLt,
          show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_perm _ hfresh'
      rw [hcap, ← hc3]
      exact mem_slotList_of_pair_fst
        (pairRecord_take_of_le (by exact_mod_cast hlt) _ hrec)
  · -- inverse entry at j' ≤ j, query capacity (j' = j is the self-anchor)
    rcases eq_or_lt_of_le hj'le with heq | hlt
    · subst heq
      rw [hj] at hj'
      have hq : qq = stateOut := by
        simpa using congrArg (fun e : DSEntry StmtIn U => e.1) hj'.symm
      refine Or.inr ?_
      rw [hcap, ← hc4, hq]
    · refine Or.inl ?_
      have hfresh' := fresh_at_firstOfClass_permInv hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hrec : (aa, qq) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [foldl_take_succ_eq base j' j'.isLt,
          show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_permInv _ hfresh'
      rw [hcap, ← hc4]
      exact mem_slotList_of_pair_snd
        (pairRecord_take_of_le (by exact_mod_cast hlt) _ hrec)

/-! ## The `E_hash` anchor arm -/

/-- **The `E_hash` arm anchors a collision** (CO25 Eq. 24 over a certified consistent
list): a hash entry whose answer coincides with any of the five strictly-earlier
component capacities fires `collisionStep` at its index. All five disjuncts are
strict (`j' < j`), so unlike the permutation arms there is no self-anchor case. -/
theorem anchored_of_hash_anchor
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base)
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) base)
    {j : Fin base.length} {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hj : base[j] = ⟨.inl stmt, capSeg⟩)
    (hcoin : ∃ j' < j, ∃ stmt',
      base[j'] = ⟨.inl stmt', capSeg⟩ ∨
      (∃ sIn1 sOut1, base[j'] = ⟨.inr (.inl sIn1), sOut1⟩ ∧
        sOut1.capacitySegment = capSeg) ∨
      (∃ sOut2 sIn2, base[j'] = ⟨.inr (.inr sOut2), sIn2⟩ ∧
        sIn2.capacitySegment = capSeg) ∨
      (∃ sIn3 sOut3, base[j'] = ⟨.inr (.inl sIn3), sOut3⟩ ∧
        sIn3.capacitySegment = capSeg) ∨
      (∃ sOut4 sIn4, base[j'] = ⟨.inr (.inr sOut4), sIn4⟩ ∧
        sOut4.capacitySegment = capSeg)) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) base := by
  classical
  have hfresh := fresh_at_firstOfClass_hash hcons
    (firstOfClassAt_of_noRedundant hnr j) hj
  refine anchoredFrom_of_at ((∅, []) : DSCache StmtIn U) base j ?_
  rw [hj]
  refine ⟨hfresh, ?_⟩
  obtain ⟨j', hj'lt, stmt', hcase⟩ := hcoin
  rcases hcase with hj' | ⟨sIn1, sOut1, hj', hc1⟩ | ⟨sOut2, sIn2, hj', hc2⟩ |
    ⟨sIn3, sOut3, hj', hc3⟩ | ⟨sOut4, sIn4, hj', hc4⟩
  · -- earlier hash entry with the same answer
    have hfresh' := fresh_at_firstOfClass_hash hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).1 stmt' = some capSeg := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_hash _ hfresh'
    exact mem_slotList_of_hash
      (hashRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier forward entry, answer capacity
    have hfresh' := fresh_at_firstOfClass_perm hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn1, sOut1) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_perm _ hfresh'
    rw [← hc1]
    exact mem_slotList_of_pair_snd
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier inverse entry, answer capacity
    have hfresh' := fresh_at_firstOfClass_permInv hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn2, sOut2) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_permInv _ hfresh'
    rw [← hc2]
    exact mem_slotList_of_pair_fst
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier forward entry, query capacity
    have hfresh' := fresh_at_firstOfClass_perm hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn3, sOut3) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_perm _ hfresh'
    rw [← hc3]
    exact mem_slotList_of_pair_fst
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier inverse entry, query capacity
    have hfresh' := fresh_at_firstOfClass_permInv hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn4, sOut4) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_permInv _ hfresh'
    rw [← hc4]
    exact mem_slotList_of_pair_snd
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)

/-! ## The `E_p` anchor arm -/

/-- **The `E_p` arm anchors a collision** (CO25 Eq. 25 over a certified consistent
list): a forward entry whose answer capacity coincides with any of the five earlier-
component capacities fires `collisionStep` at its index. The `j' = j` case of
disjunct 4 is the self-anchor (answer capacity = own query capacity); the `j' = j`
cases of disjuncts 3 and 5 are constructor clashes. -/
theorem anchored_of_perm_anchor
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base)
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) base)
    {j : Fin base.length} {stateIn stateOut : CanonicalSpongeState U}
    {capSeg : Vector U SpongeSize.C}
    (hj : base[j] = ⟨.inr (.inl stateIn), stateOut⟩)
    (hcap : stateOut.capacitySegment = capSeg)
    (hcoin :
      (∃ j' < j, ∃ stmt', base[j'] = ⟨.inl stmt', capSeg⟩) ∨
      (∃ j' < j, ∃ sIn1 sOut1, base[j'] = ⟨.inr (.inl sIn1), sOut1⟩ ∧
        sOut1.capacitySegment = capSeg) ∨
      (∃ j' ≤ j, ∃ sOut2 sIn2, base[j'] = ⟨.inr (.inr sOut2), sIn2⟩ ∧
        sIn2.capacitySegment = capSeg) ∨
      (∃ j' ≤ j, ∃ sIn3 sOut3, base[j'] = ⟨.inr (.inl sIn3), sOut3⟩ ∧
        sIn3.capacitySegment = capSeg) ∨
      (∃ j' ≤ j, ∃ sOut4 sIn4, base[j'] = ⟨.inr (.inr sOut4), sIn4⟩ ∧
        sOut4.capacitySegment = capSeg)) :
    AnchoredFrom ((∅, []) : DSCache StmtIn U) base := by
  classical
  have hfresh := fresh_at_firstOfClass_perm hcons
    (firstOfClassAt_of_noRedundant hnr j) hj
  refine anchoredFrom_of_at ((∅, []) : DSCache StmtIn U) base j ?_
  rw [hj]
  refine ⟨hfresh, ?_⟩
  rcases hcoin with ⟨j', hj'lt, stmt', hj'⟩ | ⟨j', hj'lt, sIn1, sOut1, hj', hc1⟩ |
    ⟨j', hj'le, sOut2, sIn2, hj', hc2⟩ | ⟨j', hj'le, sIn3, sOut3, hj', hc3⟩ |
    ⟨j', hj'le, sOut4, sIn4, hj', hc4⟩
  · -- earlier hash entry with answer capSeg
    refine Or.inl ?_
    have hfresh' := fresh_at_firstOfClass_hash hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).1 stmt' = some capSeg := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_hash _ hfresh'
    rw [hcap]
    exact mem_slotList_of_hash
      (hashRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- earlier forward entry, answer capacity
    refine Or.inl ?_
    have hfresh' := fresh_at_firstOfClass_perm hcons
      (firstOfClassAt_of_noRedundant hnr j') hj'
    have hrec : (sIn1, sOut1) ∈ ((base.take (j'.val + 1)).foldl stepCache
        ((∅, []) : DSCache StmtIn U)).2 := by
      rw [foldl_take_succ_eq base j' j'.isLt,
        show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
      exact stepCache_caches_fresh_perm _ hfresh'
    rw [hcap, ← hc1]
    exact mem_slotList_of_pair_snd
      (pairRecord_take_of_le (by exact_mod_cast hj'lt) _ hrec)
  · -- inverse entry at j' ≤ j, answer capacity (j' = j is a constructor clash)
    rcases eq_or_lt_of_le hj'le with heq | hlt
    · subst heq
      rw [hj] at hj'
      simp at hj'
    · refine Or.inl ?_
      have hfresh' := fresh_at_firstOfClass_permInv hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hrec : (sIn2, sOut2) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [foldl_take_succ_eq base j' j'.isLt,
          show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_permInv _ hfresh'
      rw [hcap, ← hc2]
      exact mem_slotList_of_pair_fst
        (pairRecord_take_of_le (by exact_mod_cast hlt) _ hrec)
  · -- forward entry at j' ≤ j, query capacity (j' = j is the self-anchor)
    rcases eq_or_lt_of_le hj'le with heq | hlt
    · subst heq
      rw [hj] at hj'
      have hq : sIn3 = stateIn := by
        simpa using congrArg (fun e : DSEntry StmtIn U => e.1) hj'.symm
      refine Or.inr ?_
      rw [hcap, ← hc3, hq]
    · refine Or.inl ?_
      have hfresh' := fresh_at_firstOfClass_perm hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hrec : (sIn3, sOut3) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [foldl_take_succ_eq base j' j'.isLt,
          show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_perm _ hfresh'
      rw [hcap, ← hc3]
      exact mem_slotList_of_pair_fst
        (pairRecord_take_of_le (by exact_mod_cast hlt) _ hrec)
  · -- inverse entry at j' ≤ j, query capacity (j' = j is a constructor clash)
    rcases eq_or_lt_of_le hj'le with heq | hlt
    · subst heq
      rw [hj] at hj'
      simp at hj'
    · refine Or.inl ?_
      have hfresh' := fresh_at_firstOfClass_permInv hcons
        (firstOfClassAt_of_noRedundant hnr j') hj'
      have hrec : (sIn4, sOut4) ∈ ((base.take (j'.val + 1)).foldl stepCache
          ((∅, []) : DSCache StmtIn U)).2 := by
        rw [foldl_take_succ_eq base j' j'.isLt,
          show (base[(j' : ℕ)]'j'.isLt) = base[j'] from rfl, hj']
        exact stepCache_caches_fresh_permInv _ hfresh'
      rw [hcap, ← hc4]
      exact mem_slotList_of_pair_snd
        (pairRecord_take_of_le (by exact_mod_cast hlt) _ hrec)

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf
#print axioms DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_take_succ_eq
#print axioms DuplexSpongeFS.EagerLazyDS.pairKey_isSome_take_of_le
#print axioms DuplexSpongeFS.EagerLazyDS.notFunction_data_impossible
#print axioms DuplexSpongeFS.EagerLazyDS.hashRecord_take_of_le
#print axioms DuplexSpongeFS.EagerLazyDS.pairRecord_take_of_le
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_permInv_anchor
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_hash_anchor
#print axioms DuplexSpongeFS.EagerLazyDS.anchored_of_perm_anchor
