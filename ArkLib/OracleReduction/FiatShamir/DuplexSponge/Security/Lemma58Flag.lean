/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.EagerLazyDS
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBound

/-!
# The ghost-flagged lazy oracle (CO25 Lemma 5.8, the answer-anchored accounting carrier)

The birthday accounting for `EPaper` must anchor every counted collision on the *sampled*
side of the colliding pair, and must order hash entries against permutation entries
*temporally* — information the joint cache `DSCache` cannot recover (a query-side
coincidence with an earlier sampled slot is legitimate adaptive chaining, never a
random event). This file adds the temporal information as a **ghost `Prop` flag**:

* `collisionStep t c ans` — the step from cache `c` on query `t` was *fresh* and its
  sampled answer's capacity hit an existing slot (or its own query's capacity — the
  no-loop self events of CO25 Eqs. 25/26 at `j' = j`);
* `lazyDSImplFlagged` — runs `lazyDSImpl` verbatim and accumulates
  `flag' = flag ∨ collisionStep`; the cache trajectory and all answers are untouched;
* `lazyDSImpl_run_map_flagged` — the forgetting bridge: the plain run is the projection
  of the flagged run, so any probability statement transports;
* `lazyDSImplFlagged_step_size` — the engine's `hstep_size` for the flagged carrier.

The accumulator engine (`probEvent_simulateQ_stateT_le_sum_of_step`) then bounds
`Pr[final flag]` by the Gauss sum, and the support-level correspondence
(`EPaper log → flag`, separate file) closes Lemma 5.8.

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

/-- **The anchored per-step collision event**: the query was fresh (a genuine sample), and
the sampled answer's capacity landed on an existing capacity slot of the cache — or, for
permutation queries, on its own query's capacity (the `j' = j` no-loop disjuncts of CO25
Eqs. 25/26). Query-side coincidences (an adversary choosing a query whose capacity matches
an existing slot) are deliberately *not* events. -/
def collisionStep (t : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (c : DSCache StmtIn U) :
    (duplexSpongeChallengeOracle StmtIn U).Range t → Prop :=
  match t with
  | .inl q => fun u => c.1 q = none ∧ u ∈ slotList c
  | .inr (.inl sIn) => fun b =>
      c.2.find? (fun w => w.1 = sIn) = none ∧
        (b.capacitySegment ∈ slotList c ∨
          b.capacitySegment = sIn.capacitySegment)
  | .inr (.inr sOut) => fun a =>
      c.2.find? (fun w => w.2 = sOut) = none ∧
        (a.capacitySegment ∈ slotList c ∨
          a.capacitySegment = sOut.capacitySegment)

/-- The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a
`Prop` state component, whether any step so far was an anchored collision. -/
noncomputable def lazyDSImplFlagged :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (DSCache StmtIn U × Prop) ProbComp) :=
  fun t s =>
    (fun (p : _ × DSCache StmtIn U) =>
      (p.1, (p.2, s.2 ∨ collisionStep t s.1 p.1))) <$> (lazyDSImpl t).run s.1

/-- Single-step exposure of the flagged oracle (public; the defeq `show` does not
transport across files). -/
theorem lazyDSImplFlagged_run (t : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s : DSCache StmtIn U × Prop) :
    (lazyDSImplFlagged t).run s
      = (fun (p : _ × DSCache StmtIn U) =>
          (p.1, (p.2, s.2 ∨ collisionStep t s.1 p.1))) <$> (lazyDSImpl t).run s.1 := rfl

/-- **The forgetting bridge**: the plain lazy run is the state projection of the flagged
run — the ghost flag changes nothing observable. -/
theorem lazyDSImpl_run_map_flagged {α : Type}
    (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (c : DSCache StmtIn U) (fl : Prop) :
    (simulateQ lazyDSImpl oa).run c
      = (fun (p : α × (DSCache StmtIn U × Prop)) => (p.1, p.2.1)) <$>
          (simulateQ lazyDSImplFlagged oa).run (c, fl) := by
  induction oa using OracleComp.inductionOn generalizing c fl with
  | pure a =>
      rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      rw [show (simulateQ lazyDSImpl
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run c
          = (lazyDSImpl t).run c from by
        refine congrArg (fun z => StateT.run z c) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rw [show (simulateQ lazyDSImplFlagged
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run (c, fl)
          = (lazyDSImplFlagged t).run (c, fl) from by
        refine congrArg (fun z => StateT.run z (c, fl)) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rw [lazyDSImplFlagged_run t (c, fl)]
      simp only [map_bind]
      refine Eq.trans ?_ (Eq.symm (bind_map_left _ _ _))
      refine congrArg _ (funext fun w => ?_)
      exact ih w.1 w.2 (fl ∨ collisionStep t c w.1)

/-- The engine's `hstep_size` for the flagged carrier: the cache component grows by at
most one per step (the flag is size-free). -/
theorem lazyDSImplFlagged_step_size
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s),
      dsCacheSize us.2.1 ≤ dsCacheSize s.1 + 1 := by
  intro us hus
  rw [lazyDSImplFlagged_run t s] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, hw, rfl⟩ := hus
  exact lazyDSImpl_step_size t s.1 w hw

/-- The flag is sticky: once set, every reachable successor state keeps it. -/
theorem lazyDSImplFlagged_flag_monotone
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop)
    (hfl : s.2) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s), us.2.2 := by
  intro us hus
  rw [lazyDSImplFlagged_run t s] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, _, rfl⟩ := hus
  exact Or.inl hfl

/-! ## Counting bricks for the per-step bound -/

/-- The capacity-fiber preimage count: exactly `|W| · |U|^R` states carry a capacity
from `W`. -/
lemma card_capacityFiber_preimage (W : Finset (Vector U SpongeSize.C)) :
    (Finset.univ.filter
      (fun x : CanonicalSpongeState U => x.capacitySegment ∈ W)).card
      = W.card * Fintype.card U ^ SpongeSize.R := by
  classical
  have hsplit : Finset.univ.filter
      (fun x : CanonicalSpongeState U => x.capacitySegment ∈ W)
      = W.biUnion (fun c => Finset.univ.filter
          (fun x : CanonicalSpongeState U => x.capacitySegment = c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact ⟨fun h => ⟨x.capacitySegment, h, rfl⟩, fun ⟨c, hc, hxc⟩ => hxc ▸ hc⟩
  rw [hsplit, Finset.card_biUnion (fun c₁ _ c₂ _ hne => Finset.disjoint_left.mpr
    (fun x hx₁ hx₂ => hne (((Finset.mem_filter.mp hx₁).2.symm).trans
      (Finset.mem_filter.mp hx₂).2)))]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_)
    (by rw [Finset.sum_const, smul_eq_mul])
  rw [← Fintype.card_subtype]
  exact card_capacityFiber c

/-- The slot list is at most twice the cache size. -/
lemma slotList_length_le (s : DSCache StmtIn U) :
    (slotList s).length ≤ 2 * dsCacheSize s := by
  classical
  obtain ⟨ch, cp⟩ := s
  have h2 : ∀ l : List (CanonicalSpongeState U × CanonicalSpongeState U),
      (l.flatMap (fun p => [p.1.capacitySegment, p.2.capacitySegment])).length
        = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.flatMap_cons, List.length_append, ih,
        List.length_cons, List.length_nil]; omega
  simp only [slotList, dsCacheSize, List.length_append, h2]
  have h1 := List.length_filterMap_le (fun x => ch x)
    ((Finset.univ.filter (fun q : StmtIn => (ch q).isSome)).toList)
  rw [Finset.length_toList] at h1
  omega

section UnusedLength

variable {X : Type} [Fintype X] [DecidableEq X]

open LazyPermBridge in
/-- The unused-values pool keeps at least `|X| - |cache|` elements. -/
lemma le_length_unusedValuesList (cp : List (X × X)) :
    Fintype.card X - cp.length ≤ (unusedValuesList cp).length := by
  classical
  have hlen : (unusedValuesList cp).length
      = (Finset.univ.filter (fun b : X => ¬ b ∈ cp.map Prod.snd)).card := by
    simp [unusedValuesList, Finset.length_toList]
  have hin : (Finset.univ.filter (fun b : X => b ∈ cp.map Prod.snd)).card
      ≤ cp.length := by
    refine le_trans (Finset.card_le_card
      (fun b hb => List.mem_toFinset.mpr (Finset.mem_filter.mp hb).2)) ?_
    exact le_trans (List.toFinset_card_le _) (by simp)
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset X)) (p := fun b : X => b ∈ cp.map Prod.snd)
  rw [Finset.card_univ] at hsplit
  omega

open LazyPermBridge in
/-- The unused-keys pool keeps at least `|X| - |cache|` elements. -/
lemma le_length_unusedKeysList (cp : List (X × X)) :
    Fintype.card X - cp.length ≤ (unusedKeysList cp).length := by
  classical
  have hlen : (unusedKeysList cp).length
      = (Finset.univ.filter (fun a : X => ¬ a ∈ cp.map Prod.fst)).card := by
    simp [unusedKeysList, Finset.length_toList]
  have hin : (Finset.univ.filter (fun a : X => a ∈ cp.map Prod.fst)).card
      ≤ cp.length := by
    refine le_trans (Finset.card_le_card
      (fun a ha => List.mem_toFinset.mpr (Finset.mem_filter.mp ha).2)) ?_
    exact le_trans (List.toFinset_card_le _) (by simp)
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset X)) (p := fun a : X => a ∈ cp.map Prod.fst)
  rw [Finset.card_univ] at hsplit
  omega

open LazyPermBridge in
/-- An exhausted values pool forces the cache to cover the type. -/
lemma card_le_of_unusedValuesList_eq_nil {cp : List (X × X)}
    (h : unusedValuesList cp = []) : Fintype.card X ≤ cp.length := by
  have := le_length_unusedValuesList cp
  rw [h] at this
  simp only [List.length_nil, Nat.le_zero] at this
  omega

open LazyPermBridge in
/-- An exhausted keys pool forces the cache to cover the type. -/
lemma card_le_of_unusedKeysList_eq_nil {cp : List (X × X)}
    (h : unusedKeysList cp = []) : Fintype.card X ≤ cp.length := by
  have := le_length_unusedKeysList cp
  rw [h] at this
  simp only [List.length_nil, Nat.le_zero] at this
  omega

end UnusedLength

/-! ## The per-step bound -/

/-- The per-step bad probability: `(2m+1)·|U|^R / (|U|^N − m)` from cache size `m` — the
union bound over at most `2m+1` anchored capacity targets, each a fiber of `|U|^R` states,
against a sampling pool of at least `|U|^N − m` elements. -/
noncomputable def lemma58StepBound (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (m : ℕ) : ℝ≥0∞ :=
  ((2 * m + 1) * Fintype.card U ^ SpongeSize.R : ℝ≥0∞) /
    ((Fintype.card (CanonicalSpongeState U) : ℝ≥0∞) - m)

lemma lemma58StepBound_monotone : Monotone (lemma58StepBound U) := by
  intro a b hab
  refine ENNReal.div_le_div ?_ (tsub_le_tsub_left (by exact_mod_cast hab) _)
  gcongr

private lemma natCast_sub_le_ennreal (a b : ℕ) :
    ((a : ℝ≥0∞) - b) ≤ ((a - b : ℕ) : ℝ≥0∞) := by
  exact le_of_eq (ENNReal.natCast_sub a b).symm

private lemma lemma58_num_ne_zero (m : ℕ) :
    ((2 * m + 1) * Fintype.card U ^ SpongeSize.R : ℝ≥0∞) ≠ 0 := by
  have : Nonempty U := ⟨0⟩
  refine mul_ne_zero (by positivity) ?_
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The hash-arm arithmetic: `A / |U|^C ≤ stepBound` for `A ≤ 2m`. -/
private lemma div_card_pow_C_le_stepBound {A m : ℕ} (hA : A ≤ 2 * m) :
    (A : ℝ≥0∞) / ((Fintype.card U ^ SpongeSize.C : ℕ) : ℝ≥0∞)
      ≤ lemma58StepBound U m := by
  have hNE : Nonempty U := ⟨0⟩
  have hcu0 : (Fintype.card U : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcut : (Fintype.card U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcss : ((Fintype.card (CanonicalSpongeState U) : ℕ) : ℝ≥0∞)
      = (Fintype.card U : ℝ≥0∞) ^ SpongeSize.N := by
    rw [card_vector_pow, Nat.cast_pow]
  rw [Nat.cast_pow,
    ← ENNReal.mul_div_mul_left (A : ℝ≥0∞)
      ((Fintype.card U : ℝ≥0∞) ^ SpongeSize.C)
      (pow_ne_zero SpongeSize.R hcu0) (ENNReal.pow_ne_top hcut),
    ← pow_add, SpongeSize.R_plus_C_eq_N]
  unfold lemma58StepBound
  rw [hcss]
  refine ENNReal.div_le_div ?_ tsub_le_self
  rw [mul_comm]
  refine mul_le_mul_right' ?_ _
  exact_mod_cast le_trans hA (Nat.le_succ _)

/-- The permutation-arm arithmetic: `A / len ≤ stepBound` for `A` below the numerator and
`len` above the denominator. -/
private lemma div_le_stepBound_of_le {A len m : ℕ}
    (hA : A ≤ (2 * m + 1) * Fintype.card U ^ SpongeSize.R)
    (hlen : Fintype.card (CanonicalSpongeState U) - m ≤ len) :
    (A : ℝ≥0∞) / (len : ℝ≥0∞) ≤ lemma58StepBound U m := by
  unfold lemma58StepBound
  refine ENNReal.div_le_div (by exact_mod_cast hA) ?_
  exact le_trans (natCast_sub_le_ennreal _ _) (by exact_mod_cast hlen)

/-- **The engine's `hstep_bad`**: from an unflagged state with cache size `m`, one step
flags with probability at most `(2m+1)·|U|^R / (|U|^N − m)`. Cache hits never flag; a fresh
hash draw hits one of at most `2m` existing slots; a fresh permutation draw lands in the
capacity fibers of at most `2m + 1` targets (the slots plus its own query's capacity),
inside a pool of at least `|U|^N − m` unused states. -/
theorem lazyDSImplFlagged_step_bad
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop)
    (hfl : ¬ s.2) :
    Pr[ fun us : _ × (DSCache StmtIn U × Prop) => us.2.2 | (lazyDSImplFlagged t).run s]
      ≤ lemma58StepBound U (dsCacheSize s.1) := by
  classical
  have hNE : Nonempty U := ⟨0⟩
  obtain ⟨⟨ch, cp⟩, fl⟩ := s
  simp only at hfl
  have hcpm : cp.length ≤ dsCacheSize ((ch, cp) : DSCache StmtIn U) := by
    simp only [dsCacheSize]; omega
  have hslot : (slotList ((ch, cp) : DSCache StmtIn U)).toFinset.card
      ≤ 2 * dsCacheSize ((ch, cp) : DSCache StmtIn U) :=
    le_trans (List.toFinset_card_le _) (slotList_length_le _)
  rw [lazyDSImplFlagged_run]
  simp only [probEvent_map]
  rcases t with q | sIn | sOut
  · -- hash arm
    rw [lazyDSImpl_run_hash]
    erw [probEvent_map]
    rcases hcq : ch q with _ | u
    · -- fresh hash draw
      rw [QueryImpl.withCaching_run_none _ hcq]
      simp only [probEvent_map]
      rw [show (uniformSampleImpl (spec := StmtIn →ₒ Vector U SpongeSize.C) q
          : ProbComp (Vector U SpongeSize.C)) = $ᵗ (Vector U SpongeSize.C) from rfl]
      refine le_trans (probEvent_mono
        (q := (· ∈ (slotList ((ch, cp) : DSCache StmtIn U)).toFinset))
        (fun u _ h => ?_)) ?_
      · have h' : fl ∨ (ch q = none ∧
            u ∈ slotList ((ch, cp) : DSCache StmtIn U)) := h
        rcases h' with h' | h'
        · exact absurd h' hfl
        · exact List.mem_toFinset.mpr h'.2
      · refine le_trans (LazyPermBridge.probEvent_uniformSample_le_card _) ?_
        rw [card_vector_pow]
        exact div_card_pow_C_le_stepBound hslot
    · -- hash hit: never flags
      rw [QueryImpl.withCaching_run_some _ hcq]
      refine le_trans (le_of_eq (probEvent_eq_zero fun z hz hbad => ?_)) (zero_le _)
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      have h' : fl ∨ (ch q = none ∧
          u ∈ slotList ((ch, cp) : DSCache StmtIn U)) := hbad
      rcases h' with h' | h'
      · exact hfl h'
      · exact absurd (hcq.symm.trans h'.1) (by simp)
  · -- forward permutation arm
    rcases hcfind : cp.find? (fun w => w.1 = sIn) with _ | w
    · -- fresh forward draw
      by_cases hnil : LazyPermBridge.unusedValuesList cp = []
      · -- pool exhausted: the bound is ⊤
        have hcard : Fintype.card (CanonicalSpongeState U)
            ≤ dsCacheSize ((ch, cp) : DSCache StmtIn U) :=
          le_trans (card_le_of_unusedValuesList_eq_nil hnil) hcpm
        refine le_trans probEvent_le_one ?_
        unfold lemma58StepBound
        rw [tsub_eq_zero_of_le (by exact_mod_cast hcard),
          ENNReal.div_zero (lemma58_num_ne_zero _)]
        exact le_top
      · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_none cp hcfind]
        erw [probEvent_map, probEvent_map]
        refine le_trans (probEvent_mono
          (q := (· ∈ Finset.univ.filter
            (fun b : CanonicalSpongeState U => b.capacitySegment ∈
              insert sIn.capacitySegment
                (slotList ((ch, cp) : DSCache StmtIn U)).toFinset)))
          (fun b _ h => ?_)) ?_
        · have h' : fl ∨ (cp.find? (fun w => w.1 = sIn) = none ∧
              (b.capacitySegment ∈ slotList ((ch, cp) : DSCache StmtIn U) ∨
                b.capacitySegment = sIn.capacitySegment)) := h
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases h' with h' | h'
          · exact absurd h' hfl
          · rcases h'.2 with hs | hs
            · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hs)
            · exact hs ▸ Finset.mem_insert_self _ _
        · refine le_trans (LazyPermBridge.probEvent_sampleUnused_le_card hnil
            (LazyPermBridge.unusedValuesList_nodup cp) _) ?_
          refine div_le_stepBound_of_le ?_ ?_
          · rw [card_capacityFiber_preimage]
            refine Nat.mul_le_mul_right _ ?_
            exact le_trans (Finset.card_insert_le _ _) (by omega)
          · exact le_trans
              (Nat.sub_le_sub_left hcpm _) (le_length_unusedValuesList cp)
    · -- forward hit: never flags
      rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_some cp hcfind,
        map_pure]
      refine le_trans (le_of_eq (probEvent_eq_zero fun z hz hbad => ?_)) (zero_le _)
      have hz' : z ∈ support ((pure ((w.2 : CanonicalSpongeState U),
          ((ch, cp) : DSCache StmtIn U)) : ProbComp _)) := hz
      rw [support_pure] at hz'
      have hz2 : z = (w.2, ((ch, cp) : DSCache StmtIn U)) := hz'
      subst hz2
      have h' : fl ∨ (cp.find? (fun w => w.1 = sIn) = none ∧
          (CanonicalSpongeState.capacitySegment w.2 ∈
              slotList ((ch, cp) : DSCache StmtIn U) ∨
            CanonicalSpongeState.capacitySegment w.2 = sIn.capacitySegment)) := hbad
      rcases h' with h' | h'
      · exact hfl h'
      · exact absurd (hcfind.symm.trans h'.1) (by simp)
  · -- inverse permutation arm
    rcases hcfind : cp.find? (fun w => w.2 = sOut) with _ | w
    · -- fresh inverse draw
      by_cases hnil : LazyPermBridge.unusedKeysList cp = []
      · have hcard : Fintype.card (CanonicalSpongeState U)
            ≤ dsCacheSize ((ch, cp) : DSCache StmtIn U) :=
          le_trans (card_le_of_unusedKeysList_eq_nil hnil) hcpm
        refine le_trans probEvent_le_one ?_
        unfold lemma58StepBound
        rw [tsub_eq_zero_of_le (by exact_mod_cast hcard),
          ENNReal.div_zero (lemma58_num_ne_zero _)]
        exact le_top
      · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_none cp hcfind]
        erw [probEvent_map, probEvent_map]
        refine le_trans (probEvent_mono
          (q := (· ∈ Finset.univ.filter
            (fun a : CanonicalSpongeState U => a.capacitySegment ∈
              insert sOut.capacitySegment
                (slotList ((ch, cp) : DSCache StmtIn U)).toFinset)))
          (fun a _ h => ?_)) ?_
        · have h' : fl ∨ (cp.find? (fun w => w.2 = sOut) = none ∧
              (a.capacitySegment ∈ slotList ((ch, cp) : DSCache StmtIn U) ∨
                a.capacitySegment = sOut.capacitySegment)) := h
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases h' with h' | h'
          · exact absurd h' hfl
          · rcases h'.2 with hs | hs
            · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hs)
            · exact hs ▸ Finset.mem_insert_self _ _
        · refine le_trans (LazyPermBridge.probEvent_sampleUnused_le_card hnil
            (LazyPermBridge.unusedKeysList_nodup cp) _) ?_
          refine div_le_stepBound_of_le ?_ ?_
          · rw [card_capacityFiber_preimage]
            refine Nat.mul_le_mul_right _ ?_
            exact le_trans (Finset.card_insert_le _ _) (by omega)
          · exact le_trans
              (Nat.sub_le_sub_left hcpm _) (le_length_unusedKeysList cp)
    · -- inverse hit: never flags
      rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_some cp hcfind,
        map_pure]
      refine le_trans (le_of_eq (probEvent_eq_zero fun z hz hbad => ?_)) (zero_le _)
      have hz' : z ∈ support ((pure ((w.1 : CanonicalSpongeState U),
          ((ch, cp) : DSCache StmtIn U)) : ProbComp _)) := hz
      rw [support_pure] at hz'
      have hz2 : z = (w.1, ((ch, cp) : DSCache StmtIn U)) := hz'
      subst hz2
      have h' : fl ∨ (cp.find? (fun w => w.2 = sOut) = none ∧
          (CanonicalSpongeState.capacitySegment w.1 ∈
              slotList ((ch, cp) : DSCache StmtIn U) ∨
            CanonicalSpongeState.capacitySegment w.1 = sOut.capacitySegment)) := hbad
      rcases h' with h' | h'
      · exact hfl h'
      · exact absurd (hcfind.symm.trans h'.1) (by simp)

/-! ## The engine application and the Gauss-sum arithmetic -/

lemma dsCacheSize_empty :
    dsCacheSize ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U)))
      : DSCache StmtIn U) = 0 := by
  classical
  simp [dsCacheSize]

/-- **The accumulated flag bound**: a `T`-query computation, run from the empty cache with
the flag down, ends flagged with probability at most `∑_{i<T} (2i+1)·|U|^R/(|U|^N − i)`. -/
theorem probEvent_flag_final_le_sum {α : Type}
    (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound oa T) :
    Pr[ fun xs : α × (DSCache StmtIn U × Prop) => xs.2.2 |
        (simulateQ lazyDSImplFlagged oa).run
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))), False)]
      ≤ ∑ i ∈ Finset.range T, lemma58StepBound U i := by
  have h := DuplexSpongeFS.BirthdayBound.probEvent_simulateQ_stateT_le_sum_of_step
    (impl := lazyDSImplFlagged) (bad := fun s : DSCache StmtIn U × Prop => s.2)
    (size := fun s : DSCache StmtIn U × Prop => dsCacheSize s.1)
    (ε := lemma58StepBound U) lemma58StepBound_monotone
    (fun t s hs => lazyDSImplFlagged_step_bad t s hs)
    (fun t s _ => lazyDSImplFlagged_step_size t s) T hT
    ((∅, []), False) not_false
  simpa [dsCacheSize_empty] using h

lemma sum_range_two_mul_add_one (T : ℕ) :
    ∑ i ∈ Finset.range T, (2 * i + 1) = T ^ 2 := by
  induction T with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- The Gauss-sum domination: below half the state space, the accumulated step bounds sum
to at most `2T²/|U|^C`. -/
theorem sum_lemma58StepBound_le {T : ℕ}
    (h2T : 2 * T ≤ Fintype.card (CanonicalSpongeState U)) :
    ∑ i ∈ Finset.range T, lemma58StepBound U i
      ≤ ((2 * T ^ 2 : ℕ) : ℝ≥0∞) / ((Fintype.card U ^ SpongeSize.C : ℕ) : ℝ≥0∞) := by
  classical
  have hNE : Nonempty U := ⟨0⟩
  have hcu0 : (Fintype.card U : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcut : (Fintype.card U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set B : ℕ := Fintype.card (CanonicalSpongeState U) with hB
  have hterm : ∀ i ∈ Finset.range T, lemma58StepBound U i
      ≤ (((2 * (2 * i + 1)) : ℕ) : ℝ≥0∞) * (Fintype.card U : ℝ≥0∞) ^ SpongeSize.R
        / (B : ℝ≥0∞) := by
    intro i hi
    have hiT : i < T := Finset.mem_range.mp hi
    have hiB : 2 * i ≤ B := by omega
    have hhalf : B ≤ 2 * (B - i) := by omega
    unfold lemma58StepBound
    rw [show ((Fintype.card (CanonicalSpongeState U) : ℝ≥0∞) - (i : ℕ))
        = (((B - i : ℕ)) : ℝ≥0∞) from (ENNReal.natCast_sub B i).symm]
    rw [← ENNReal.mul_div_mul_left
      ((2 * (i : ℝ≥0∞) + 1) * (Fintype.card U : ℝ≥0∞) ^ SpongeSize.R)
      (((B - i : ℕ)) : ℝ≥0∞) (two_ne_zero) (ENNReal.ofNat_ne_top)]
    refine ENNReal.div_le_div (le_of_eq ?_) ?_
    · push_cast
      ring
    · calc (B : ℝ≥0∞) = (((B : ℕ)) : ℝ≥0∞) := rfl
        _ ≤ (((2 * (B - i) : ℕ)) : ℝ≥0∞) := by exact_mod_cast hhalf
        _ = 2 * (((B - i : ℕ)) : ℝ≥0∞) := by push_cast; ring
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range T, (((2 * (2 * i + 1)) : ℕ) : ℝ≥0∞)
      = ((2 * T ^ 2 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.mul_sum, sum_range_two_mul_add_one]
  rw [hsum]
  have hBval : (B : ℝ≥0∞)
      = (Fintype.card U : ℝ≥0∞) ^ SpongeSize.R
          * (Fintype.card U : ℝ≥0∞) ^ SpongeSize.C := by
    rw [hB, card_vector_pow, Nat.cast_pow, ← pow_add, SpongeSize.R_plus_C_eq_N]
  rw [hBval, Nat.cast_pow,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hcu0)) (Or.inl (ENNReal.pow_ne_top hcut)),
    show ((2 * T ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card U : ℝ≥0∞) ^ SpongeSize.R
        * (((Fintype.card U : ℝ≥0∞) ^ SpongeSize.R)⁻¹
            * (((Fintype.card U : ℝ≥0∞) ^ SpongeSize.C))⁻¹)
      = ((Fintype.card U : ℝ≥0∞) ^ SpongeSize.R
          * ((Fintype.card U : ℝ≥0∞) ^ SpongeSize.R)⁻¹)
        * (((2 * T ^ 2 : ℕ) : ℝ≥0∞)
            * (((Fintype.card U : ℝ≥0∞) ^ SpongeSize.C))⁻¹) from by ring,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hcu0) (ENNReal.pow_ne_top hcut), one_mul]

open DuplexSpongeFS.BirthdayBound in
/-- **The complete engine output for CO25 Lemma 5.8**: the final flag probability of any
`T`-query computation, in real form, is at most `(7T² − 3T)/(2|U|^C)` — unconditionally
(beyond half the state space the bound exceeds `1`). -/
theorem probEvent_flag_final_toReal_le_lemma5_8Bound {α : Type}
    (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound oa T) :
    (Pr[ fun xs : α × (DSCache StmtIn U × Prop) => xs.2.2 |
        (simulateQ lazyDSImplFlagged oa).run
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))), False)]).toReal
      ≤ lemma5_8Bound U T := by
  have hNE : Nonempty U := ⟨0⟩
  have hcardU : (1 : ℕ) ≤ Fintype.card U := Fintype.card_pos
  have hpowC : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := by positivity
  rcases Nat.eq_zero_or_pos T with rfl | hT1
  · -- `T = 0`: the sum is empty, the flag stays down
    have h0 : Pr[ fun xs : α × (DSCache StmtIn U × Prop) => xs.2.2 |
        (simulateQ lazyDSImplFlagged oa).run
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))), False)] = 0 :=
      le_antisymm (by simpa using probEvent_flag_final_le_sum oa 0 hT) (zero_le _)
    rw [h0]
    simp [lemma5_8Bound]
  rcases Nat.le_total (2 * T) (Fintype.card (CanonicalSpongeState U)) with h2T | h2T
  · -- small `T`: the Gauss sum applies
    have h := le_trans (probEvent_flag_final_le_sum oa T hT) (sum_lemma58StepBound_le h2T)
    have hfin : ((2 * T ^ 2 : ℕ) : ℝ≥0∞) / ((Fintype.card U ^ SpongeSize.C : ℕ) : ℝ≥0∞)
        ≠ ⊤ := by
      refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
      exact Nat.cast_ne_zero.mpr (by positivity)
    refine le_trans (ENNReal.toReal_mono hfin h) ?_
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    unfold lemma5_8Bound
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    have hTT : (0 : ℝ) ≤ 3 * (T : ℝ) ^ 2 - 3 * T := by nlinarith
    nlinarith [mul_nonneg hTT hpowC.le]
  · -- large `T`: the bound exceeds one
    have hple : (Pr[ fun xs : α × (DSCache StmtIn U × Prop) => xs.2.2 |
        (simulateQ lazyDSImplFlagged oa).run ((∅, []), False)]).toReal ≤ 1 :=
      le_trans (ENNReal.toReal_mono ENNReal.one_ne_top probEvent_le_one) (by simp)
    refine le_trans hple ?_
    unfold lemma5_8Bound
    rw [le_div_iff₀ (by positivity)]
    have hCN : Fintype.card U ^ SpongeSize.C ≤ Fintype.card (CanonicalSpongeState U) := by
      rw [card_vector_pow]
      exact Nat.pow_le_pow_right hcardU (by have := SpongeSize.R_plus_C_eq_N (sz := ‹_›); omega)
    have hC2T : Fintype.card U ^ SpongeSize.C ≤ 2 * T := le_trans hCN h2T
    have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    have hCR : (Fintype.card U : ℝ) ^ SpongeSize.C ≤ 2 * T := by exact_mod_cast hC2T
    nlinarith [sq_nonneg ((T : ℝ) - 1)]

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone
#print axioms DuplexSpongeFS.EagerLazyDS.card_capacityFiber_preimage
#print axioms DuplexSpongeFS.EagerLazyDS.slotList_length_le
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_bad
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_le_sum
#print axioms DuplexSpongeFS.EagerLazyDS.sum_lemma58StepBound_le
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_toReal_le_lemma5_8Bound
