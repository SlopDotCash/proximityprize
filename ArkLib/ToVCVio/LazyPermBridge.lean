/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.LazyPermMarginal
import ArkLib.Data.Hash.DuplexSponge
import VCVio

/-!
# The lazy permutation oracle — implementations and step distributions

Brick 4 (increment A) of the eager–lazy permutation bridge behind CO25 Lemma 5.8
(`Lemma5_8EagerPaperResidual`): the two implementations of a bidirectional permutation
oracle `(X ⊕ X) →ₒ X` (forward queries on `.inl`, inverse queries on `.inr`), and the
distribution facts for a single lazy step.

* `eagerPermImpl π` — answer through a fixed permutation (the once-sampled carrier);
* `lazyPermImpl` — memoize a growing cache of pairs; answer cache hits deterministically
  and fresh queries by a uniform draw from the unused side (`sampleUnused`, with a junk
  default for the unreachable empty case);
* `evalDist_sampleUnused` — over a duplicate-free nonempty list, `sampleUnused` is the
  uniform distribution on the list's finset, connecting the implementation to the
  chain-rule lemmas of `LazyPermMarginal`.

The master `simulateQ` induction (lazy from a realizable cache ≡ draw a uniform extension
once, then answer eagerly) is increment B.
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace LazyPermBridge

open LazyPermMarginal

variable {X : Type} [DecidableEq X] [Inhabited X]

/-- Answer both directions of the permutation oracle through a fixed permutation. -/
noncomputable def eagerPermImpl (π : Equiv.Perm X) :
    QueryImpl ((X ⊕ X) →ₒ X) ProbComp :=
  fun t => pure (match t with
    | .inl a => π a
    | .inr b => π.symm b)

/-- Uniformly sample an element of a list (junk default on the empty list, which is
unreachable from realizable caches). -/
noncomputable def sampleUnused (xs : List X) : ProbComp X :=
  match xs with
  | [] => pure default
  | y :: ys => ((y :: ys)[·]) <$> $[0..ys.length]

variable [Fintype X]

/-- The unused outputs of a cache, as a list (for sampling). -/
noncomputable def unusedValuesList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun b : X => b ∉ c.map Prod.snd)).toList

/-- The unused inputs of a cache, as a list (for sampling on inverse queries). -/
noncomputable def unusedKeysList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun a : X => a ∉ c.map Prod.fst)).toList

/-- The lazy bidirectional permutation oracle: cache hits answer deterministically; fresh
queries draw uniformly from the unused side and record the new pair. -/
noncomputable def lazyPermImpl :
    QueryImpl ((X ⊕ X) →ₒ X) (StateT (List (X × X)) ProbComp) :=
  fun t c =>
    match t with
    | .inl a =>
        match c.find? (fun p => p.1 = a) with
        | some p => pure (p.2, c)
        | none => (fun b => (b, c.concat (a, b))) <$> sampleUnused (unusedValuesList c)
    | .inr b =>
        match c.find? (fun p => p.2 = b) with
        | some p => pure (p.1, c)
        | none => (fun a => (a, c.concat (a, b))) <$> sampleUnused (unusedKeysList c)

section Facts

@[simp] lemma mem_unusedValuesList {c : List (X × X)} {b : X} :
    b ∈ unusedValuesList c ↔ b ∉ c.map Prod.snd := by
  classical
  simp [unusedValuesList]

@[simp] lemma mem_unusedKeysList {c : List (X × X)} {a : X} :
    a ∈ unusedKeysList c ↔ a ∉ c.map Prod.fst := by
  classical
  simp [unusedKeysList]

lemma unusedValuesList_nodup (c : List (X × X)) : (unusedValuesList c).Nodup := by
  classical
  exact Finset.nodup_toList _

lemma unusedKeysList_nodup (c : List (X × X)) : (unusedKeysList c).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- **The lazy step distribution**: over a duplicate-free nonempty list, `sampleUnused` is
the uniform distribution on the list's finset (lifted to the success branch). This connects
the implementation's fresh-query step to the chain rules of `LazyPermMarginal`. -/
theorem evalDist_sampleUnused_run (xs : List X) (hnd : xs.Nodup) (hxs : xs ≠ []) :
    (evalDist (sampleUnused xs)).run
      = (PMF.uniformOfFinset xs.toFinset (by
          simpa [Finset.nonempty_iff_ne_empty, List.toFinset_eq_empty_iff] using hxs)).map
            some := by
  classical
  rcases xs with _ | ⟨y, ys⟩
  · exact absurd rfl hxs
  · ext o
    rcases o with _ | x
    · -- failure mass is zero on both sides
      have hfail : Pr[⊥ | sampleUnused (y :: ys)] = 0 := by
        simp [sampleUnused]
      rw [show ((evalDist (sampleUnused (y :: ys))).run none)
          = Pr[⊥ | sampleUnused (y :: ys)] from rfl, hfail]
      rw [PMF.map_apply]
      refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
      simp
    · -- success mass: `count/length = 1/card` for a duplicate-free list
      have hout : ((evalDist (sampleUnused (y :: ys))).run (some x))
          = Pr[= x | sampleUnused (y :: ys)] := rfl
      rw [hout]
      have hcount : Pr[= x | sampleUnused (y :: ys)]
          = ((y :: ys).count x : ℝ≥0∞) / (y :: ys).length := by
        show Pr[= x | ((y :: ys)[·]) <$> $[0..ys.length]] = _
        rw [List.count, ← List.countP_eq_sum_fin_ite]
        simp [probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]
      rw [hcount, PMF.map_apply]
      refine Eq.trans ?_ (tsum_eq_single x
        (fun b hb => if_neg (fun h => hb (Option.some_inj.mp h).symm))).symm
      rw [if_pos rfl]
      by_cases hx : x ∈ (y :: ys)
      · rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨y, by simp⟩)
            (List.mem_toFinset.mpr hx),
          List.count_eq_one_of_mem hnd hx, List.toFinset_card_of_nodup hnd]
        simp [ENNReal.div_eq_inv_mul]
      · rw [PMF.uniformOfFinset_apply_of_notMem (hs := ⟨y, by simp⟩)
            (fun h => hx (List.mem_toFinset.mp h)),
          List.count_eq_zero_of_not_mem hx]
        simp


/-- The fresh sample lands in the list (nonempty case). -/
lemma support_sampleUnused {xs : List X} (h : xs ≠ []) :
    support (sampleUnused xs) ⊆ {x | x ∈ xs} := by
  rcases xs with _ | ⟨y, ys⟩
  · exact absurd rfl h
  · intro x hx
    simp only [sampleUnused, support_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact List.getElem_mem _

/-- Event probability of the fresh sample: `countP/length` (mirrors
`probEvent_uniformSelectList`, without the `OptionT` layer). -/
lemma probEvent_sampleUnused {xs : List X} (h : xs ≠ []) (p : X → Prop) [DecidablePred p] :
    Pr[ p | sampleUnused xs] = ((xs.countP p : ℕ) : ℝ≥0∞) / xs.length := by
  classical
  rcases xs with _ | ⟨y, ys⟩
  · exact absurd rfl h
  · show Pr[ p | ((y :: ys)[·]) <$> $[0..ys.length]] = _
    simp only [Fin.getElem_fin, probEvent_map, ProbComp.probEvent_uniformFin,
      Function.comp_apply, Fin.countP_eq_countP_map_finRange, Nat.cast_add, Nat.cast_one,
      List.length_cons]
    congr 2
    exact List.countP_finRange_getElem (y :: ys) (fun b => decide (p b))

/-- **The per-step landing bound (4D-3 atom)**: a fresh sample from a duplicate-free pool
lands in a target set with probability at most `|target| / |pool|`. -/
lemma probEvent_sampleUnused_le_card {xs : List X} (h : xs ≠ []) (hnd : xs.Nodup)
    (S : Finset X) :
    Pr[ (· ∈ S) | sampleUnused xs] ≤ (S.card : ℝ≥0∞) / xs.length := by
  classical
  rw [probEvent_sampleUnused h]
  refine ENNReal.div_le_div_right ?_ _
  have hcount : xs.countP (· ∈ S) ≤ S.card := by
    have hlen : xs.countP (· ∈ S) = (xs.filter (· ∈ S)).length :=
      List.countP_eq_length_filter
    rw [hlen, ← List.toFinset_card_of_nodup (hnd.filter _)]
    refine Finset.card_le_card fun x hx => ?_
    have hmem := List.mem_toFinset.mp hx
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  exact_mod_cast hcount

/-- **The per-step landing bound, full-uniform arm (4D-3 hash atom)**: a uniform draw from
the whole type hits a target set with probability at most `|target| / |type|`. -/
lemma probEvent_uniformSample_le_card {Y : Type} [Fintype Y] [Nonempty Y] [SampleableType Y]
    [DecidableEq Y] (S : Finset Y) :
    Pr[ (· ∈ S) | $ᵗ Y] ≤ (S.card : ℝ≥0∞) / Fintype.card Y := by
  classical
  rw [probEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)

/-! ## Step exposures (public, for cross-file consumers) -/

lemma lazyPermImpl_run_inl_none (cp : List (X × X)) {a : X}
    (hc : cp.find? (fun p => p.1 = a) = none) :
    (lazyPermImpl ((.inl a : X ⊕ X))).run cp
      = (fun b => (b, cp.concat (a, b))) <$> sampleUnused (unusedValuesList cp) := by
  show (match cp.find? (fun p => p.1 = a) with
    | some p => (pure (p.2, cp) : ProbComp (X × List (X × X)))
    | none => (fun b => (b, cp.concat (a, b))) <$> sampleUnused (unusedValuesList cp)) = _
  rw [hc]

lemma lazyPermImpl_run_inl_some (cp : List (X × X)) {a : X} {p : X × X}
    (hc : cp.find? (fun p => p.1 = a) = some p) :
    (lazyPermImpl ((.inl a : X ⊕ X))).run cp = (pure (p.2, cp) : ProbComp _) := by
  show (match cp.find? (fun p => p.1 = a) with
    | some p => (pure (p.2, cp) : ProbComp (X × List (X × X)))
    | none => (fun b => (b, cp.concat (a, b))) <$> sampleUnused (unusedValuesList cp)) = _
  rw [hc]

lemma lazyPermImpl_run_inr_none (cp : List (X × X)) {b : X}
    (hc : cp.find? (fun p => p.2 = b) = none) :
    (lazyPermImpl ((.inr b : X ⊕ X))).run cp
      = (fun a => (a, cp.concat (a, b))) <$> sampleUnused (unusedKeysList cp) := by
  show (match cp.find? (fun p => p.2 = b) with
    | some p => (pure (p.1, cp) : ProbComp (X × List (X × X)))
    | none => (fun a => (a, cp.concat (a, b))) <$> sampleUnused (unusedKeysList cp)) = _
  rw [hc]

lemma lazyPermImpl_run_inr_some (cp : List (X × X)) {b : X} {p : X × X}
    (hc : cp.find? (fun p => p.2 = b) = some p) :
    (lazyPermImpl ((.inr b : X ⊕ X))).run cp = (pure (p.1, cp) : ProbComp _) := by
  show (match cp.find? (fun p => p.2 = b) with
    | some p => (pure (p.1, cp) : ProbComp (X × List (X × X)))
    | none => (fun a => (a, cp.concat (a, b))) <$> sampleUnused (unusedKeysList cp)) = _
  rw [hc]

/-! ## The flavored variant (direction-tagged cache, for the birthday accounting)

The accounting's bad event must anchor on the *sampled* (answer) component of each cache
pair, which the bare pair list cannot recover. The flavored implementation records a tag
(`true` = created by an inverse query, i.e. the key was sampled); it forgets to the plain
implementation by projecting tags away. -/

/-- The direction-tagged lazy permutation oracle: identical sampling to `lazyPermImpl`,
with each fresh pair recorded together with its creation direction. -/
noncomputable def lazyPermImplFlavored :
    QueryImpl ((X ⊕ X) →ₒ X) (StateT (List ((X × X) × Bool)) ProbComp) :=
  fun t c =>
    match t with
    | .inl a =>
        match (c.map Prod.fst).find? (fun p => p.1 = a) with
        | some p => pure (p.2, c)
        | none => (fun b => (b, c.concat ((a, b), false))) <$>
            sampleUnused (unusedValuesList (c.map Prod.fst))
    | .inr b =>
        match (c.map Prod.fst).find? (fun p => p.2 = b) with
        | some p => pure (p.1, c)
        | none => (fun a => (a, c.concat ((a, b), true))) <$>
            sampleUnused (unusedKeysList (c.map Prod.fst))

/-- **The forgetting bridge**: projecting the tags away maps the flavored run onto the
plain run, state and all. -/
theorem lazyPermImpl_run_map_flavored {α : Type}
    (oa : OracleComp ((X ⊕ X) →ₒ X) α) (c : List ((X × X) × Bool)) :
    (simulateQ lazyPermImpl oa).run (c.map Prod.fst)
      = (fun (p : α × List ((X × X) × Bool)) => (p.1, p.2.map Prod.fst)) <$>
          (simulateQ lazyPermImplFlavored oa).run c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      rw [show (simulateQ lazyPermImpl (liftM (((X ⊕ X) →ₒ X).query t))).run (c.map Prod.fst)
          = (lazyPermImpl t).run (c.map Prod.fst) from by
        refine congrArg (fun z => StateT.run z (c.map Prod.fst)) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rw [show (simulateQ lazyPermImplFlavored (liftM (((X ⊕ X) →ₒ X).query t))).run c
          = (lazyPermImplFlavored t).run c from by
        refine congrArg (fun z => StateT.run z c) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rcases t with a | b
      · rcases hc : (c.map Prod.fst).find? (fun p => p.1 = a) with _ | p
        · rw [lazyPermImpl_run_inl_none (c.map Prod.fst) hc,
            show (lazyPermImplFlavored ((.inl a : X ⊕ X))).run c
              = (fun b => (b, c.concat ((a, b), false))) <$>
                  sampleUnused (unusedValuesList (c.map Prod.fst)) from by
            show (match (c.map Prod.fst).find? (fun p => p.1 = a) with
              | some p => (pure (p.2, c) : ProbComp _)
              | none => (fun b => (b, c.concat ((a, b), false))) <$>
                  sampleUnused (unusedValuesList (c.map Prod.fst))) = _
            rw [hc]]
          rw [bind_map_left, bind_map_left, map_bind]
          refine congrArg _ (funext fun b => ?_)
          have hmapconcat : (c.concat ((a, b), false)).map Prod.fst
              = (c.map Prod.fst).concat (a, b) := by
            simp [List.concat_eq_append]
          rw [← hmapconcat]
          exact ih b (c.concat ((a, b), false))
        · rw [lazyPermImpl_run_inl_some (c.map Prod.fst) hc,
            show (lazyPermImplFlavored ((.inl a : X ⊕ X))).run c
              = (pure (p.2, c) : ProbComp _) from by
            show (match (c.map Prod.fst).find? (fun p => p.1 = a) with
              | some p => (pure (p.2, c) : ProbComp _)
              | none => (fun b => (b, c.concat ((a, b), false))) <$>
                  sampleUnused (unusedValuesList (c.map Prod.fst))) = _
            rw [hc]]
          rw [pure_bind, pure_bind]
          exact ih p.2 c
      · rcases hc : (c.map Prod.fst).find? (fun p => p.2 = b) with _ | p
        · rw [lazyPermImpl_run_inr_none (c.map Prod.fst) hc,
            show (lazyPermImplFlavored ((.inr b : X ⊕ X))).run c
              = (fun a => (a, c.concat ((a, b), true))) <$>
                  sampleUnused (unusedKeysList (c.map Prod.fst)) from by
            show (match (c.map Prod.fst).find? (fun p => p.2 = b) with
              | some p => (pure (p.1, c) : ProbComp _)
              | none => (fun a => (a, c.concat ((a, b), true))) <$>
                  sampleUnused (unusedKeysList (c.map Prod.fst))) = _
            rw [hc]]
          rw [bind_map_left, bind_map_left, map_bind]
          refine congrArg _ (funext fun a => ?_)
          have hmapconcat : (c.concat ((a, b), true)).map Prod.fst
              = (c.map Prod.fst).concat (a, b) := by
            simp [List.concat_eq_append]
          rw [← hmapconcat]
          exact ih a (c.concat ((a, b), true))
        · rw [lazyPermImpl_run_inr_some (c.map Prod.fst) hc,
            show (lazyPermImplFlavored ((.inr b : X ⊕ X))).run c
              = (pure (p.1, c) : ProbComp _) from by
            show (match (c.map Prod.fst).find? (fun p => p.2 = b) with
              | some p => (pure (p.1, c) : ProbComp _)
              | none => (fun a => (a, c.concat ((a, b), true))) <$>
                  sampleUnused (unusedKeysList (c.map Prod.fst))) = _
            rw [hc]]
          rw [pure_bind, pure_bind]
          exact ih p.1 c

/-- Single-step form of the forgetting bridge, for consumption outside this file (the
defeq `show`-trick exposures of the flavored arms do not transport across files). -/
theorem lazyPermImpl_step_map_flavored (t : X ⊕ X) (c : List ((X × X) × Bool)) :
    (lazyPermImpl t).run (c.map Prod.fst)
      = (fun (p : X × List ((X × X) × Bool)) => (p.1, p.2.map Prod.fst)) <$>
          (lazyPermImplFlavored t).run c := by
  have h := lazyPermImpl_run_map_flavored (liftM (((X ⊕ X) →ₒ X).query t)) c
  rwa [show (simulateQ lazyPermImpl (liftM (((X ⊕ X) →ₒ X).query t))).run (c.map Prod.fst)
      = (lazyPermImpl t).run (c.map Prod.fst) from by
    refine congrArg (fun z => StateT.run z (c.map Prod.fst)) ?_
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map],
    show (simulateQ lazyPermImplFlavored (liftM (((X ⊕ X) →ₒ X).query t))).run c
      = (lazyPermImplFlavored t).run c from by
    refine congrArg (fun z => StateT.run z c) ?_
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]] at h

/-! ## The permutation overlay (`tableExtending` analogue)

`permExtending c π` corrects `π` to agree with every cached pair by **pre-composition**
swaps, processed left to right: fixing `(a, b)` disturbs only the inputs `a` and `π⁻¹ b`,
so (for a duplicate-free cache) earlier corrections are never undone. -/

/-- Overlay a cache on a permutation: pre-composition swap corrections force agreement
with every cached pair. -/
def permExtending (c : List (X × X)) (π : Equiv.Perm X) : Equiv.Perm X :=
  c.foldl (fun π' p => (Equiv.swap p.1 (π'.symm p.2)).trans π') π

@[simp] lemma permExtending_nil (π : Equiv.Perm X) : permExtending [] π = π := rfl

lemma permExtending_cons (p : X × X) (c : List (X × X)) (π : Equiv.Perm X) :
    permExtending (p :: c) π
      = permExtending c ((Equiv.swap p.1 (π.symm p.2)).trans π) := rfl

/-- The one-pair correction sends `a` to `b`. -/
lemma onestep_apply_self (a b : X) (π : Equiv.Perm X) :
    ((Equiv.swap a (π.symm b)).trans π) a = b := by
  simp [Equiv.trans_apply, Equiv.swap_apply_left]

/-- The one-pair correction fixes any input other than `a` whose value is not `b`. -/
lemma onestep_apply_of_ne (a b x : X) (π : Equiv.Perm X)
    (hxa : x ≠ a) (hxb : π x ≠ b) :
    ((Equiv.swap a (π.symm b)).trans π) x = π x := by
  rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hxa]
  intro h
  exact hxb (by rw [h, Equiv.apply_symm_apply])

/-- **Overlay preservation**: a pair already realized by `π` and disjoint from the cache
keys and values survives the overlay. -/
lemma permExtending_preserves (c : List (X × X)) (π : Equiv.Perm X) {a b : X}
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd) (hab : π a = b) :
    permExtending c π a = b := by
  induction c generalizing π with
  | nil => simpa using hab
  | cons p rest ih =>
      rw [permExtending_cons]
      have hpa : a ≠ p.1 := fun h => ha (by simp [h])
      have hpb : π a ≠ p.2 := by
        rw [hab]
        exact fun h => hb (by simp [h])
      exact ih _ (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h))
        (by rw [onestep_apply_of_ne p.1 p.2 a π hpa hpb, hab])

/-- **Overlay agreement**: the overlay realizes every cached pair (duplicate-free cache). -/
lemma extends_permExtending (c : List (X × X)) (π : Equiv.Perm X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup) :
    Extends (permExtending c π) c := by
  induction c generalizing π with
  | nil => exact extends_nil _
  | cons p rest ih =>
      intro q hq
      rw [permExtending_cons]
      rcases List.mem_cons.mp hq with rfl | hq
      · -- the head pair: established by its own correction, preserved by the rest
        refine permExtending_preserves rest _ ?_ ?_ (onestep_apply_self q.1 q.2 π)
        · exact fun h => (List.nodup_cons.mp (by simpa using hkeys)).1 h
        · exact fun h => (List.nodup_cons.mp (by simpa using hvals)).1 h
      · exact ih _ ((List.nodup_cons.mp (by simpa using hkeys)).2)
          ((List.nodup_cons.mp (by simpa using hvals)).2) q hq

/-! ## The one-step fiber lemma

The fiber of the one-pair correction over an extension `τ` of `c ⧺ [(a,b)]`, within the
extensions of `c`, is exactly `{(swap b w) ∘ τ : w unused}` — one preimage per unused
output, which is why a uniform conditioned permutation stays uniform after the correction. -/

/-- Fiber characterization of the one-pair correction. -/
lemma onestep_fiber_iff (c : List (X × X)) (a b : X)
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd)
    {τ : Equiv.Perm X} (hτ : Extends τ (c.concat (a, b))) (π : Equiv.Perm X) :
    (Extends π c ∧ (Equiv.swap a (π.symm b)).trans π = τ)
      ↔ ∃ w, w ∉ c.map Prod.snd ∧ π = τ.trans (Equiv.swap b w) := by
  obtain ⟨hτc, hτa⟩ := (extends_concat_iff τ c a b).mp hτ
  constructor
  · rintro ⟨hπc, hstep⟩
    refine ⟨π a, fun hmem => extends_apply_ne_of_used hπc ha hmem rfl, ?_⟩
    apply Equiv.ext
    intro x
    rw [Equiv.trans_apply]
    have hτx : ∀ y, τ y = π ((Equiv.swap a (π.symm b)) y) := by
      intro y
      rw [← hstep, Equiv.trans_apply]
    rcases eq_or_ne x a with rfl | hxa
    · rw [hτa, Equiv.swap_apply_left]
    · rcases eq_or_ne x (π.symm b) with rfl | hxb
      · rw [Equiv.apply_symm_apply, hτx (π.symm b), Equiv.swap_apply_right,
          Equiv.swap_apply_right]
      · rw [hτx x, Equiv.swap_apply_of_ne_of_ne hxa hxb,
          Equiv.swap_apply_of_ne_of_ne]
        · intro h
          apply hxb
          rw [← h, Equiv.symm_apply_apply]
        · exact fun h => hxa (π.injective h)
  · rintro ⟨w, hw, rfl⟩
    have hπa : (τ.trans (Equiv.swap b w)) a = w := by
      rw [Equiv.trans_apply, hτa, Equiv.swap_apply_left]
    constructor
    · intro p hp
      have hτp : τ p.1 = p.2 := hτc p hp
      rw [Equiv.trans_apply, hτp, Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => hb (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      · exact fun h => hw (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
    · -- the correction of `τ ∘ (swap b w)` recovers `τ`
      have hsymmb : (τ.trans (Equiv.swap b w)).symm b = τ.symm w := by
        rw [Equiv.symm_apply_eq, Equiv.trans_apply, Equiv.apply_symm_apply,
          Equiv.swap_apply_right]
      apply Equiv.ext
      intro x
      rw [Equiv.trans_apply, hsymmb]
      rcases eq_or_ne x a with rfl | hxa
      · rw [Equiv.swap_apply_left, Equiv.trans_apply, Equiv.apply_symm_apply,
          Equiv.swap_apply_right, hτa]
      · rcases eq_or_ne x (τ.symm w) with rfl | hxw
        · rw [Equiv.swap_apply_right, hπa, Equiv.apply_symm_apply]
        · rw [Equiv.swap_apply_of_ne_of_ne hxa hxw, Equiv.trans_apply,
            Equiv.swap_apply_of_ne_of_ne]
          · intro h
            exact hxa (τ.injective (by rw [h, hτa]))
          · intro h
            exact hxw ((Equiv.symm_apply_eq τ).mpr h.symm).symm

/-- The one-pair correction of an extension of `c` extends `c ⧺ [(a,b)]` (for `a` fresh and
`b` unused): the correction disturbs only `a` and `π⁻¹ b`, neither of which is cached. -/
lemma onestep_extends (c : List (X × X)) (a b : X)
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd)
    {π : Equiv.Perm X} (hπ : Extends π c) :
    Extends ((Equiv.swap a (π.symm b)).trans π) (c.concat (a, b)) := by
  rw [extends_concat_iff]
  refine ⟨?_, onestep_apply_self a b π⟩
  intro p hp
  have hpa : p.1 ≠ a := fun h => ha (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hpb : π p.1 ≠ b := by
    rw [hπ p hp]
    exact fun h => hb (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [onestep_apply_of_ne a b p.1 π hpa hpb]
  exact hπ p hp

set_option maxHeartbeats 800000 in
/-- **The one-step pushforward**: a uniform extension of `c`, corrected at a fresh pair
slot, is a uniform extension of the grown cache — uniformity survives because the fibers
(`onestep_fiber_iff`) all have exactly one preimage per unused output. -/
theorem map_onestep_uniform (c : List (X × X)) (a b : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd)
    (hne : (extendsFinset c).Nonempty) :
    (PMF.uniformOfFinset (extendsFinset c) hne).map
        (fun π => (Equiv.swap a (π.symm b)).trans π)
      = PMF.uniformOfFinset (extendsFinset (c.concat (a, b)))
          (extendsFinset_concat_nonempty c a b ha hb hne) := by
  classical
  letI : DecidableEq (Equiv.Perm X) := Classical.decEq _
  ext τ
  rw [PMF.map_apply, tsum_fintype]
  by_cases hτ : Extends τ (c.concat (a, b))
  · -- count the fiber: one preimage per unused output
    have hsum : ∀ π : Equiv.Perm X,
        (if τ = (Equiv.swap a (π.symm b)).trans π then
          (PMF.uniformOfFinset (extendsFinset c) hne) π else 0)
        = (if π ∈ (extendsFinset c).filter
            (fun π => (Equiv.swap a (π.symm b)).trans π = τ) then
              ((extendsFinset c).card : ℝ≥0∞)⁻¹ else 0) := by
      intro π
      by_cases hmem : Extends π c
      · by_cases hstep : (Equiv.swap a (π.symm b)).trans π = τ
        · rw [if_pos hstep.symm, if_pos (Finset.mem_filter.mpr
              ⟨mem_extendsFinset.mpr hmem, hstep⟩),
            PMF.uniformOfFinset_apply_of_mem (hs := hne) (mem_extendsFinset.mpr hmem)]
        · rw [if_neg (fun h => hstep h.symm)]
          split_ifs with h2
          · exact absurd (Finset.mem_filter.mp h2).2 hstep
          · rfl
      · have h0 : (PMF.uniformOfFinset (extendsFinset c) hne) π = 0 :=
          PMF.uniformOfFinset_apply_of_notMem (hs := hne)
            (fun h => hmem (mem_extendsFinset.mp h))
        split_ifs with h1 h2 h2
        · exact absurd (mem_extendsFinset.mp (Finset.mem_filter.mp h2).1) hmem
        · exact h0
        · exact absurd (mem_extendsFinset.mp (Finset.mem_filter.mp h2).1) hmem
        · rfl
    refine (Finset.sum_congr rfl (fun π _ => hsum π)).trans ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((extendsFinset c).filter
        (fun π => (Equiv.swap a (π.symm b)).trans π = τ)).card
        = (unusedFinset c).card := by
      refine Eq.symm (Finset.card_bij (fun w _ => τ.trans (Equiv.swap b w)) ?_ ?_ ?_)
      · intro w hw
        have hfib := (onestep_fiber_iff c a b ha hb hτ (τ.trans (Equiv.swap b w))).mpr
          ⟨w, mem_unusedFinset.mp hw, rfl⟩
        exact Finset.mem_filter.mpr ⟨mem_extendsFinset.mpr hfib.1, hfib.2⟩
      · intro w₁ hw₁ w₂ hw₂ heq
        have := congrArg (fun e : Equiv.Perm X => e (τ.symm b)) heq
        simpa [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]
          using this
      · intro π hπ
        obtain ⟨hπc, hstep⟩ := Finset.mem_filter.mp hπ
        obtain ⟨w, hw, rfl⟩ := (onestep_fiber_iff c a b ha hb hτ π).mp
          ⟨mem_extendsFinset.mp hπc, hstep⟩
        exact ⟨w, mem_unusedFinset.mpr hw, rfl⟩
    rw [hcard, PMF.uniformOfFinset_apply_of_mem
        (hs := extendsFinset_concat_nonempty c a b ha hb hne) (mem_extendsFinset.mpr hτ),
      card_extendsFinset_eq_card_unused_mul c a b ha hb,
      show (Finset.univ.filter (fun b : X => b ∉ c.map Prod.snd)) = unusedFinset c from rfl,
      Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _)),
      ← mul_assoc, ENNReal.mul_inv_cancel ?hu (ENNReal.natCast_ne_top _), one_mul]
    case hu =>
      have := unusedFinset_nonempty c a hkeys hvals ha
      exact_mod_cast Nat.cast_ne_zero.mpr (Finset.card_pos.mpr this).ne'
  · -- off the grown extensions both sides vanish
    rw [PMF.uniformOfFinset_apply_of_notMem
      (hs := extendsFinset_concat_nonempty c a b ha hb hne)
      (fun h => hτ (mem_extendsFinset.mp h))]
    refine Finset.sum_eq_zero fun π _ => ?_
    by_cases hstep : τ = (Equiv.swap a (π.symm b)).trans π
    · rw [if_pos hstep]
      refine PMF.uniformOfFinset_apply_of_notMem (hs := hne) (fun hmem => ?_)
      exact hτ (hstep ▸ onestep_extends c a b ha hb (mem_extendsFinset.mp hmem))
    · rw [if_neg hstep]

@[simp] lemma extendsFinset_nil : extendsFinset ([] : List (X × X)) = Finset.univ := by
  classical
  ext π
  simp [mem_extendsFinset, Extends]

/-- Realizability of an appended cache, by induction from the front cache. -/
lemma extendsFinset_append_nonempty (c₀ rest : List (X × X))
    (hkeys : (((c₀ ++ rest).map Prod.fst)).Nodup)
    (hvals : (((c₀ ++ rest).map Prod.snd)).Nodup)
    (hne : (extendsFinset c₀).Nonempty) :
    (extendsFinset (c₀ ++ rest)).Nonempty := by
  classical
  induction rest generalizing c₀ with
  | nil => simpa using hne
  | cons p rest ih =>
      have hkeys' : (((c₀.concat p ++ rest).map Prod.fst)).Nodup := by
        simpa [List.concat_append] using hkeys
      have hvals' : (((c₀.concat p ++ rest).map Prod.snd)).Nodup := by
        simpa [List.concat_append] using hvals
      have hk0 := (List.nodup_append.mp (by
        simpa [List.map_append] using hkeys)).2.2
      have hv0 := (List.nodup_append.mp (by
        simpa [List.map_append] using hvals)).2.2
      have hp1 : p.1 ∉ c₀.map Prod.fst := fun h => hk0 p.1 h p.1 (by simp) rfl
      have hp2 : p.2 ∉ c₀.map Prod.snd := fun h => hv0 p.2 h p.2 (by simp) rfl
      have := ih (c₀.concat p) hkeys' hvals'
        (extendsFinset_concat_nonempty c₀ p.1 p.2 hp1 hp2 hne)
      simpa [List.concat_append] using this

set_option maxHeartbeats 800000 in
/-- **The overlay pushforward**: pushing a uniform extension of the front cache through the
overlay of the remaining pairs gives a uniform extension of the whole cache. Iterates
`map_onestep_uniform` along the fold. -/
theorem map_permExtending_uniform (c₀ rest : List (X × X))
    (hkeys : (((c₀ ++ rest).map Prod.fst)).Nodup)
    (hvals : (((c₀ ++ rest).map Prod.snd)).Nodup)
    (hne : (extendsFinset c₀).Nonempty) :
    (PMF.uniformOfFinset (extendsFinset c₀) hne).map (permExtending rest)
      = PMF.uniformOfFinset (extendsFinset (c₀ ++ rest))
          (extendsFinset_append_nonempty c₀ rest hkeys hvals hne) := by
  classical
  induction rest generalizing c₀ with
  | nil =>
      rw [show (permExtending ([] : List (X × X))) = id from rfl, PMF.map_id]
      have : c₀ ++ [] = c₀ := List.append_nil c₀
      congr 1 <;> simp [this]
  | cons p rest ih =>
      have hkeys' : (((c₀.concat p ++ rest).map Prod.fst)).Nodup := by
        simpa [List.concat_append] using hkeys
      have hvals' : (((c₀.concat p ++ rest).map Prod.snd)).Nodup := by
        simpa [List.concat_append] using hvals
      have hk0 := (List.nodup_append.mp (by
        simpa [List.map_append] using hkeys)).2.2
      have hv0 := (List.nodup_append.mp (by
        simpa [List.map_append] using hvals)).2.2
      have hp1 : p.1 ∉ c₀.map Prod.fst := fun h => hk0 p.1 h p.1 (by simp) rfl
      have hp2 : p.2 ∉ c₀.map Prod.snd := fun h => hv0 p.2 h p.2 (by simp) rfl
      have hk0nodup : (c₀.map Prod.fst).Nodup :=
        (List.nodup_append.mp (by simpa [List.map_append] using hkeys)).1
      have hv0nodup : (c₀.map Prod.snd).Nodup :=
        (List.nodup_append.mp (by simpa [List.map_append] using hvals)).1
      have hsplit : (permExtending (p :: rest) : Equiv.Perm X → Equiv.Perm X)
          = (permExtending rest) ∘ (fun π => (Equiv.swap p.1 (π.symm p.2)).trans π) := rfl
      rw [hsplit, ← PMF.map_comp,
        map_onestep_uniform c₀ p.1 p.2 hk0nodup hv0nodup hp1 hp2 hne,
        ih (c₀.concat p) hkeys' hvals'
          (extendsFinset_concat_nonempty c₀ p.1 p.2 hp1 hp2 hne)]
      have hconc : c₀.concat p ++ rest = c₀ ++ p :: rest := List.concat_append
      congr 1 <;> simp [hconc]

/-! ## The master eager–lazy induction -/

/-- The unused-values list enumerates the unused finset. -/
lemma toFinset_unusedValuesList (c : List (X × X)) :
    (unusedValuesList c).toFinset = unusedFinset c := by
  classical
  ext b
  simp [unusedValuesList, unusedFinset]

/-- The unused-keys list enumerates the swapped cache's unused finset. -/
lemma toFinset_unusedKeysList (c : List (X × X)) :
    (unusedKeysList c).toFinset = unusedFinset (c.map Prod.swap) := by
  classical
  ext a
  simp [unusedKeysList, unusedFinset, List.map_map, Function.comp_def]

/-- `bind` of a PMF against an `Option.elim`-shaped function only depends on the success
branch over the success support. -/
private lemma pmf_bind_elim_congr {α β : Type} (p : PMF (Option α))
    (f g : α → PMF (Option β))
    (h : ∀ a, p (some a) ≠ 0 → f a = g a) :
    (p.bind (fun o => o.elim (PMF.pure none) f))
      = (p.bind (fun o => o.elim (PMF.pure none) g)) := by
  classical
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun o => ?_
  rcases o with _ | a
  · rfl
  · rcases eq_or_ne (p (some a)) 0 with ha | ha
    · rw [ha, zero_mul, zero_mul]
    · simp only [Option.elim_some]
      rw [h a ha]

section PMFAbsorption

variable [SampleableType (Equiv.Perm X)]

/-- The overlay pushforward, stated from the uniform permutation (`uniformOfFintype` is
definitionally `uniformOfFinset univ`, and `extendsFinset [] = univ`). -/
theorem map_permExtending_uniform_fintype (rest : List (X × X))
    (hkeys : ((rest.map Prod.fst)).Nodup) (hvals : ((rest.map Prod.snd)).Nodup) :
    (PMF.uniformOfFintype (Equiv.Perm X)).map (permExtending rest)
      = PMF.uniformOfFinset (extendsFinset rest)
          (by
            have := extendsFinset_append_nonempty [] rest (by simpa using hkeys)
              (by simpa using hvals) (by simp)
            simpa using this) := by
  classical
  have h := map_permExtending_uniform [] rest (by simpa using hkeys)
    (by simpa using hvals) (by simp)
  have huniv : PMF.uniformOfFintype (Equiv.Perm X)
      = PMF.uniformOfFinset (extendsFinset ([] : List (X × X)))
          (by simp) := by
    ext π
    rw [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply_of_mem
      (hs := by simp) (by simp [mem_extendsFinset])]
    simp
  rw [huniv]
  simpa using h

/-- **The miss-case absorption, PMF level**: drawing a fresh unused output and overlaying
the grown cache on a uniform permutation is the overlay of the original cache — the chain
rule `uniformOfFinset_extends_step` composed with the overlay pushforward. -/
theorem pmf_absorb {α : Type} (c : List (X × X)) (a : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) (hne : (extendsFinset c).Nonempty)
    (ψ : Equiv.Perm X → α) :
    (PMF.uniformOfFinset (unusedFinset c)
        (unusedFinset_nonempty c a hkeys hvals ha)).bind (fun b =>
      ((PMF.uniformOfFintype (Equiv.Perm X)).map
        (fun π => ψ (permExtending (c.concat (a, b)) π))))
      = (PMF.uniformOfFintype (Equiv.Perm X)).map
          (fun π => ψ (permExtending c π)) := by
  classical
  -- nodups of the grown cache, for unused `b` (rewritten per-fibre on the support)
  have hgrow : ∀ b, b ∉ c.map Prod.snd →
      (((c.concat (a, b)).map Prod.fst).Nodup ∧ ((c.concat (a, b)).map Prod.snd).Nodup) := by
    intro b hb
    constructor
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      exact ⟨hkeys, List.nodup_singleton _, by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun h => ha (h ▸ hx)⟩
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      exact ⟨hvals, List.nodup_singleton _, by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun h => hb (h ▸ hx)⟩
  -- rewrite the bound fibres via the fintype pushforward at the grown cache
  rw [LazyPermMarginal.bind_congr_support _ _
    (fun b =>
      if h : (extendsFinset (c.concat (a, b))).Nonempty then
        (PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h).map ψ
      else (PMF.uniformOfFinset (extendsFinset c) hne).map ψ)
    (by
      intro b hb
      rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedFinset] at hb
      obtain ⟨hk', hv'⟩ := hgrow b hb
      have hpos := extendsFinset_concat_nonempty c a b ha hb hne
      dsimp only
      rw [dif_pos hpos,
        show (fun π => ψ (permExtending (c.concat (a, b)) π))
          = ψ ∘ (permExtending (c.concat (a, b))) from rfl, ← PMF.map_comp,
        map_permExtending_uniform_fintype (c.concat (a, b)) hk' hv'])]
  -- pull the `ψ`-map out of the bind and apply the chain rule
  have hpull : (PMF.uniformOfFinset (unusedFinset c)
      (unusedFinset_nonempty c a hkeys hvals ha)).bind (fun b =>
        (if h : (extendsFinset (c.concat (a, b))).Nonempty then
          (PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h).map ψ
        else (PMF.uniformOfFinset (extendsFinset c) hne).map ψ))
      = ((PMF.uniformOfFinset (unusedFinset c)
          (unusedFinset_nonempty c a hkeys hvals ha)).bind (fun b =>
            if h : (extendsFinset (c.concat (a, b))).Nonempty then
              PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h
            else PMF.uniformOfFinset (extendsFinset c) hne)).map ψ := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun b => ?_)
    split_ifs <;> rfl
  rw [hpull, ← uniformOfFinset_extends_step c a hkeys hvals ha hne,
    show (fun π => ψ (permExtending c π)) = ψ ∘ (permExtending c) from rfl,
    ← PMF.map_comp, map_permExtending_uniform_fintype c hkeys hvals]

/-- **The miss-case absorption, inverse direction**: drawing a fresh unused *key* and
overlaying the grown cache is the overlay of the original cache — the inverse chain rule
composed with the overlay pushforward. -/
theorem pmf_absorb_inv {α : Type} (c : List (X × X)) (b : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (hb : b ∉ c.map Prod.snd) (hne : (extendsFinset c).Nonempty)
    (ψ : Equiv.Perm X → α) :
    (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
        (unusedFinset_nonempty (c.map Prod.swap) b
          (by simpa [List.map_map, Function.comp_def] using hvals)
          (by simpa [List.map_map, Function.comp_def] using hkeys)
          (by simpa [List.map_map, Function.comp_def] using hb))).bind (fun a =>
      ((PMF.uniformOfFintype (Equiv.Perm X)).map
        (fun π => ψ (permExtending (c.concat (a, b)) π))))
      = (PMF.uniformOfFintype (Equiv.Perm X)).map
          (fun π => ψ (permExtending c π)) := by
  classical
  have hgrow : ∀ a, a ∉ c.map Prod.fst →
      (((c.concat (a, b)).map Prod.fst).Nodup ∧ ((c.concat (a, b)).map Prod.snd).Nodup) := by
    intro a ha
    constructor
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      exact ⟨hkeys, List.nodup_singleton _, by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun h => ha (h ▸ hx)⟩
    · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      exact ⟨hvals, List.nodup_singleton _, by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact fun h => hb (h ▸ hx)⟩
  rw [LazyPermMarginal.bind_congr_support _ _
    (fun a =>
      if h : (extendsFinset (c.concat (a, b))).Nonempty then
        (PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h).map ψ
      else (PMF.uniformOfFinset (extendsFinset c) hne).map ψ)
    (by
      intro a ha
      rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedFinset] at ha
      have haK : a ∉ c.map Prod.fst := by
        simpa [List.map_map, Function.comp_def] using ha
      obtain ⟨hk', hv'⟩ := hgrow a haK
      have hpos : (extendsFinset (c.concat (a, b))).Nonempty := by
        have := extendsFinset_append_nonempty [] (c.concat (a, b))
          (by simpa using hk') (by simpa using hv') (by simp)
        simpa using this
      dsimp only
      rw [dif_pos hpos,
        show (fun π => ψ (permExtending (c.concat (a, b)) π))
          = ψ ∘ (permExtending (c.concat (a, b))) from rfl, ← PMF.map_comp,
        map_permExtending_uniform_fintype (c.concat (a, b)) hk' hv'])]
  have hpull : (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
      (unusedFinset_nonempty (c.map Prod.swap) b
        (by simpa [List.map_map, Function.comp_def] using hvals)
        (by simpa [List.map_map, Function.comp_def] using hkeys)
        (by simpa [List.map_map, Function.comp_def] using hb))).bind (fun a =>
        (if h : (extendsFinset (c.concat (a, b))).Nonempty then
          (PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h).map ψ
        else (PMF.uniformOfFinset (extendsFinset c) hne).map ψ))
      = ((PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
          (unusedFinset_nonempty (c.map Prod.swap) b
            (by simpa [List.map_map, Function.comp_def] using hvals)
            (by simpa [List.map_map, Function.comp_def] using hkeys)
            (by simpa [List.map_map, Function.comp_def] using hb))).bind (fun a =>
            if h : (extendsFinset (c.concat (a, b))).Nonempty then
              PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h
            else PMF.uniformOfFinset (extendsFinset c) hne)).map ψ := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun a => ?_)
    split_ifs <;> rfl
  rw [hpull, ← uniformOfFinset_extends_step_inv c b hkeys hvals hb hne,
    show (fun π => ψ (permExtending c π)) = ψ ∘ (permExtending c) from rfl,
    ← PMF.map_comp, map_permExtending_uniform_fintype c hkeys hvals]

/-- The forward miss-case absorption with a spectator sample (the combined duplex-sponge
induction's hash table rides along untouched): swap the spectator out, absorb per fibre. -/
theorem pmf_absorb_spectator {α γ : Type} (c : List (X × X)) (a : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) (hne : (extendsFinset c).Nonempty)
    (G : PMF γ) (ψ : γ → Equiv.Perm X → α) :
    (PMF.uniformOfFinset (unusedFinset c)
        (unusedFinset_nonempty c a hkeys hvals ha)).bind (fun b =>
      G.bind (fun g =>
        (PMF.uniformOfFintype (Equiv.Perm X)).map
          (fun π => ψ g (permExtending (c.concat (a, b)) π))))
      = G.bind (fun g =>
          (PMF.uniformOfFintype (Equiv.Perm X)).map
            (fun π => ψ g (permExtending c π))) := by
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun g => pmf_absorb c a hkeys hvals ha hne (ψ g))

/-- The inverse-direction spectatored absorption. -/
theorem pmf_absorb_inv_spectator {α γ : Type} (c : List (X × X)) (b : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (hb : b ∉ c.map Prod.snd) (hne : (extendsFinset c).Nonempty)
    (G : PMF γ) (ψ : γ → Equiv.Perm X → α) :
    (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
        (unusedFinset_nonempty (c.map Prod.swap) b
          (by simpa [List.map_map, Function.comp_def] using hvals)
          (by simpa [List.map_map, Function.comp_def] using hkeys)
          (by simpa [List.map_map, Function.comp_def] using hb))).bind (fun a =>
      G.bind (fun g =>
        (PMF.uniformOfFintype (Equiv.Perm X)).map
          (fun π => ψ g (permExtending (c.concat (a, b)) π))))
      = G.bind (fun g =>
          (PMF.uniformOfFintype (Equiv.Perm X)).map
            (fun π => ψ g (permExtending c π))) := by
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun g => pmf_absorb_inv c b hkeys hvals hb hne (ψ g))

end PMFAbsorption

section MasterInduction

variable [SampleableType (Equiv.Perm X)]

/-- The bidirectional answer function of a permutation. -/
def permFn (π : Equiv.Perm X) : (t : X ⊕ X) → X :=
  fun t => match t with
  | .inl x => π x
  | .inr y => π.symm y

@[simp] lemma permFn_inl (π : Equiv.Perm X) (x : X) : permFn π (.inl x) = π x := rfl
@[simp] lemma permFn_inr (π : Equiv.Perm X) (y : X) : permFn π (.inr y) = π.symm y := rfl

private lemma uniformOfFinset_congr {β : Type} [DecidableEq β] {s t : Finset β}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    PMF.uniformOfFinset s hs = PMF.uniformOfFinset t ht := by
  subst h
  rfl

/-- Reduce the overlay-evaluation program's `toPMF` to PMF maps. -/
lemma toPMF_overlay {α : Type} (c' : List (X × X)) (F : Equiv.Perm X → α) :
    (evalDist (do
      let π ← $ᵗ (Equiv.Perm X)
      pure (F (permExtending c' π)) : ProbComp α)).toPMF
      = ((PMF.uniformOfFintype (Equiv.Perm X)).map
          (fun π => F (permExtending c' π))).map some := by
  have hprog : (do
      let π ← $ᵗ (Equiv.Perm X)
      pure (F (permExtending c' π)) : ProbComp α)
      = (fun π => F (permExtending c' π)) <$> ($ᵗ (Equiv.Perm X)) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hprog, evalDist_map, SPMF.toPMF_map, evalDist_uniformSample, SPMF.liftM_eq_map,
    SPMF.toPMF_mk, PMF.monad_map_eq_map, PMF.map_comp, PMF.map_comp]
  rfl

/-- The sample's `toPMF` over a cache's unused values. -/
lemma toPMF_sampleUnused (c : List (X × X)) (a : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) :
    (evalDist (sampleUnused (unusedValuesList c))).toPMF
      = (PMF.uniformOfFinset (unusedFinset c)
          (unusedFinset_nonempty c a hkeys hvals ha)).map some := by
  rw [← SPMF.run_eq_toPMF,
    evalDist_sampleUnused_run (unusedValuesList c) (unusedValuesList_nodup c)
      (by
        intro hnil
        have := unusedFinset_nonempty c a hkeys hvals ha
        rw [← toFinset_unusedValuesList, hnil] at this
        simpa using this)]
  exact congrArg (PMF.map some)
    (uniformOfFinset_congr (toFinset_unusedValuesList c) _ _)

/-- The sample's `toPMF` over a cache's unused keys (the swapped cache's unused values). -/
lemma toPMF_sampleUnusedKeys (c : List (X × X)) (b : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (hb : b ∉ c.map Prod.snd) :
    (evalDist (sampleUnused (unusedKeysList c))).toPMF
      = (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
          (unusedFinset_nonempty (c.map Prod.swap) b
            (by simpa [List.map_map, Function.comp_def] using hvals)
            (by simpa [List.map_map, Function.comp_def] using hkeys)
            (by simpa [List.map_map, Function.comp_def] using hb))).map some := by
  rw [← SPMF.run_eq_toPMF,
    evalDist_sampleUnused_run (unusedKeysList c) (unusedKeysList_nodup c)
      (by
        intro hnil
        have := unusedFinset_nonempty (c.map Prod.swap) b
          (by simpa [List.map_map, Function.comp_def] using hvals)
          (by simpa [List.map_map, Function.comp_def] using hkeys)
          (by simpa [List.map_map, Function.comp_def] using hb)
        rw [← toFinset_unusedKeysList, hnil] at this
        simpa using this)]
  exact congrArg (PMF.map some)
    (uniformOfFinset_congr (toFinset_unusedKeysList c) _ _)

set_option maxHeartbeats 1600000 in
/-- **The eager–lazy permutation bridge**: simulating against the lazy memoizing
bidirectional permutation oracle from a duplicate-free cache has the same distribution as
sampling one uniform permutation and answering eagerly through the cache overlay. The
permutation analogue of `evalDist_simulateQ_randomOracle_run'_eq_tableExtending`. -/
theorem evalDist_simulateQ_lazyPermImpl_run'
    {α : Type} (oa : OracleComp ((X ⊕ X) →ₒ X) α) (c : List (X × X))
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup) :
    evalDist ((simulateQ lazyPermImpl oa).run' c)
      = evalDist (do
          let π ← $ᵗ (Equiv.Perm X)
          pure (evalWithAnswerFn (QueryImpl.ofFn (permFn (permExtending c π))) oa)
          : ProbComp α) := by
  classical
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    have hlhs : (simulateQ lazyPermImpl (pure a : OracleComp _ α)).run' c
        = (pure a : ProbComp α) := by
      rw [simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, c) : ProbComp (α × _)) = pure a
      rw [map_pure]
    rw [hlhs]
    simp only [evalWithAnswerFn_pure]
    symm
    refine evalDist_ext fun x => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (Equiv.Perm X)) (by simp), one_mul]
  | query_bind t k ih =>
    have hred : (simulateQ lazyPermImpl
          (liftM (((X ⊕ X) →ₒ X).query t) >>= k)).run' c
        = ((lazyPermImpl t).run c) >>= fun p =>
            (simulateQ lazyPermImpl (k p.1)).run' p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      change Prod.fst <$> (((lazyPermImpl t).run c) >>= fun p =>
        (simulateQ lazyPermImpl (k p.1)).run p.2) = _
      rw [map_bind]
      rfl
    have heval : ∀ π : Equiv.Perm X,
        evalWithAnswerFn (QueryImpl.ofFn (permFn π))
            (liftM (((X ⊕ X) →ₒ X).query t) >>= k)
          = evalWithAnswerFn (QueryImpl.ofFn (permFn π)) (k (permFn π t)) := by
      intro π
      rw [evalWithAnswerFn_bind]
      rfl
    rw [hred]
    simp_rw [heval]
    rcases t with x | y
    · rcases hc : c.find? (fun p => p.1 = x) with _ | p
      · -- forward fresh query
        have hx : x ∉ c.map Prod.fst := by
          intro hmem
          obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hc q hq
          simp [hq1] at this
        have hstep : (lazyPermImpl ((.inl x : X ⊕ X))).run c
            = (fun b => (b, c.concat (x, b))) <$> sampleUnused (unusedValuesList c) := by
          show (match c.find? (fun p => p.1 = x) with
            | some p => (pure (p.2, c) : ProbComp (X × List (X × X)))
            | none => (fun b => (b, c.concat (x, b))) <$>
                sampleUnused (unusedValuesList c)) = _
          rw [hc]
        rw [hstep, bind_map_left]
        rw [← SPMF.toPMF_inj]
        rw [evalDist_bind, SPMF.toPMF_bind]
        rw [toPMF_overlay c
          (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ)) (k (permFn σ (Sum.inl x))))]
        rw [toPMF_sampleUnused c x hkeys hvals hx]
        rw [show Option.elimM ((PMF.uniformOfFinset (unusedFinset c)
              (unusedFinset_nonempty c x hkeys hvals hx)).map some)
            (PMF.pure none)
            (fun b => (evalDist ((simulateQ lazyPermImpl (k b)).run'
              (c.concat (x, b)))).toPMF)
          = (PMF.uniformOfFinset (unusedFinset c)
              (unusedFinset_nonempty c x hkeys hvals hx)).bind
              (fun b => (evalDist ((simulateQ lazyPermImpl (k b)).run'
                (c.concat (x, b)))).toPMF) from by
          rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
          rfl]
        have hfib : ∀ b ∈ (PMF.uniformOfFinset (unusedFinset c)
            (unusedFinset_nonempty c x hkeys hvals hx)).support,
            (evalDist ((simulateQ lazyPermImpl (k b)).run' (c.concat (x, b)))).toPMF
            = ((PMF.uniformOfFintype (Equiv.Perm X)).map
                (fun π => evalWithAnswerFn
                  (QueryImpl.ofFn (permFn (permExtending (c.concat (x, b)) π)))
                  (k (permFn (permExtending (c.concat (x, b)) π) (Sum.inl x))))).map
                some := by
          intro b hb
          rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedFinset] at hb
          have hk' : (((c.concat (x, b)).map Prod.fst)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hkeys, List.nodup_singleton _, by
              intro u hu v hv
              simp only [List.mem_singleton] at hv
              subst hv
              exact fun h => hx (h ▸ hu)⟩
          have hv' : (((c.concat (x, b)).map Prod.snd)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hvals, List.nodup_singleton _, by
              intro u hu v hv
              simp only [List.mem_singleton] at hv
              subst hv
              exact fun h => hb (h ▸ hu)⟩
          rw [ih b (c.concat (x, b)) hk' hv',
            toPMF_overlay (c.concat (x, b))
              (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ)) (k b))]
          -- replace the continuation argument `b` by the overlay's value at `x`
          congr 1
          refine congrArg _ (funext fun π => ?_)
          have hagree : permExtending (c.concat (x, b)) π x = b := by
            have := extends_permExtending (c.concat (x, b)) π hk' hv'
            exact this (x, b) (by simp [List.concat_eq_append])
          dsimp only [Function.comp_apply]
          rw [show permFn (permExtending (c.concat (x, b)) π) (Sum.inl x)
              = permExtending (c.concat (x, b)) π x from rfl, hagree]
        rw [LazyPermMarginal.bind_congr_support _ _ _ hfib, ← PMF.map_bind]
        have hne : (extendsFinset c).Nonempty := by
          have := extendsFinset_append_nonempty [] c (by simpa using hkeys)
            (by simpa using hvals) (by simp)
          simpa using this
        exact congrArg (fun p => PMF.map some p)
          (pmf_absorb c x hkeys hvals hx hne
            (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ))
              (k (permFn σ (Sum.inl x)))))
      · -- forward cache hit
        have hp1 : p.1 = x := by
          have := List.find?_some hc
          simpa using this
        have hpc : p ∈ c := List.mem_of_find?_eq_some hc
        have hstep : (lazyPermImpl ((.inl x : X ⊕ X))).run c
            = (pure (p.2, c) : ProbComp (X × List (X × X))) := by
          show (match c.find? (fun p => p.1 = x) with
            | some p => (pure (p.2, c) : ProbComp (X × List (X × X)))
            | none => (fun b => (b, c.concat (x, b))) <$>
                sampleUnused (unusedValuesList c)) = _
          rw [hc]
        rw [hstep, pure_bind]
        rw [ih p.2 c hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ (Equiv.Perm X)) >>= F) (funext fun π => ?_))
        have hval : permExtending c π x = p.2 := by
          have := extends_permExtending c π hkeys hvals p hpc
          rwa [hp1] at this
        rw [show permFn (permExtending c π) (Sum.inl x)
            = permExtending c π x from rfl, hval]
    · rcases hc : c.find? (fun p => p.2 = y) with _ | p
      · -- inverse fresh query
        have hy : y ∉ c.map Prod.snd := by
          intro hmem
          obtain ⟨q, hq, hq2⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hc q hq
          simp [hq2] at this
        have hstep : (lazyPermImpl ((.inr y : X ⊕ X))).run c
            = (fun a => (a, c.concat (a, y))) <$> sampleUnused (unusedKeysList c) := by
          show (match c.find? (fun p => p.2 = y) with
            | some p => (pure (p.1, c) : ProbComp (X × List (X × X)))
            | none => (fun a => (a, c.concat (a, y))) <$>
                sampleUnused (unusedKeysList c)) = _
          rw [hc]
        rw [hstep, bind_map_left]
        rw [← SPMF.toPMF_inj]
        rw [evalDist_bind, SPMF.toPMF_bind]
        rw [toPMF_overlay c
          (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ)) (k (permFn σ (Sum.inr y))))]
        rw [toPMF_sampleUnusedKeys c y hkeys hvals hy]
        rw [show Option.elimM ((PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
              (unusedFinset_nonempty (c.map Prod.swap) y
                (by simpa [List.map_map, Function.comp_def] using hvals)
                (by simpa [List.map_map, Function.comp_def] using hkeys)
                (by simpa [List.map_map, Function.comp_def] using hy))).map some)
            (PMF.pure none)
            (fun a => (evalDist ((simulateQ lazyPermImpl (k a)).run'
              (c.concat (a, y)))).toPMF)
          = (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
              (unusedFinset_nonempty (c.map Prod.swap) y
                (by simpa [List.map_map, Function.comp_def] using hvals)
                (by simpa [List.map_map, Function.comp_def] using hkeys)
                (by simpa [List.map_map, Function.comp_def] using hy))).bind
              (fun a => (evalDist ((simulateQ lazyPermImpl (k a)).run'
                (c.concat (a, y)))).toPMF) from by
          rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
          rfl]
        have hfib : ∀ a ∈ (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
            (unusedFinset_nonempty (c.map Prod.swap) y
              (by simpa [List.map_map, Function.comp_def] using hvals)
              (by simpa [List.map_map, Function.comp_def] using hkeys)
              (by simpa [List.map_map, Function.comp_def] using hy))).support,
            (evalDist ((simulateQ lazyPermImpl (k a)).run' (c.concat (a, y)))).toPMF
            = ((PMF.uniformOfFintype (Equiv.Perm X)).map
                (fun π => evalWithAnswerFn
                  (QueryImpl.ofFn (permFn (permExtending (c.concat (a, y)) π)))
                  (k (permFn (permExtending (c.concat (a, y)) π) (Sum.inr y))))).map
                some := by
          intro a ha
          rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedFinset] at ha
          have haK : a ∉ c.map Prod.fst := by
            simpa [List.map_map, Function.comp_def] using ha
          have hk' : (((c.concat (a, y)).map Prod.fst)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hkeys, List.nodup_singleton _, by
              intro u hu v hv
              simp only [List.mem_singleton] at hv
              subst hv
              exact fun h => haK (h ▸ hu)⟩
          have hv' : (((c.concat (a, y)).map Prod.snd)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hvals, List.nodup_singleton _, by
              intro u hu v hv
              simp only [List.mem_singleton] at hv
              subst hv
              exact fun h => hy (h ▸ hu)⟩
          rw [ih a (c.concat (a, y)) hk' hv',
            toPMF_overlay (c.concat (a, y))
              (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ)) (k a))]
          congr 1
          refine congrArg _ (funext fun π => ?_)
          have hagree : permExtending (c.concat (a, y)) π a = y := by
            have := extends_permExtending (c.concat (a, y)) π hk' hv'
            exact this (a, y) (by simp [List.concat_eq_append])
          have hsymm : (permExtending (c.concat (a, y)) π).symm y = a :=
            (Equiv.symm_apply_eq _).mpr hagree.symm
          dsimp only [Function.comp_apply]
          rw [show permFn (permExtending (c.concat (a, y)) π) (Sum.inr y)
              = (permExtending (c.concat (a, y)) π).symm y from rfl, hsymm]
        rw [LazyPermMarginal.bind_congr_support _ _ _ hfib, ← PMF.map_bind]
        have hne : (extendsFinset c).Nonempty := by
          have := extendsFinset_append_nonempty [] c (by simpa using hkeys)
            (by simpa using hvals) (by simp)
          simpa using this
        exact congrArg (fun p => PMF.map some p)
          (pmf_absorb_inv c y hkeys hvals hy hne
            (fun σ => evalWithAnswerFn (QueryImpl.ofFn (permFn σ))
              (k (permFn σ (Sum.inr y)))))
      · -- inverse cache hit
        have hp2 : p.2 = y := by
          have := List.find?_some hc
          simpa using this
        have hpc : p ∈ c := List.mem_of_find?_eq_some hc
        have hstep : (lazyPermImpl ((.inr y : X ⊕ X))).run c
            = (pure (p.1, c) : ProbComp (X × List (X × X))) := by
          show (match c.find? (fun p => p.2 = y) with
            | some p => (pure (p.1, c) : ProbComp (X × List (X × X)))
            | none => (fun a => (a, c.concat (a, y))) <$>
                sampleUnused (unusedKeysList c)) = _
          rw [hc]
        rw [hstep, pure_bind]
        rw [ih p.1 c hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ (Equiv.Perm X)) >>= F) (funext fun π => ?_))
        have hval : permExtending c π p.1 = y := by
          have := extends_permExtending c π hkeys hvals p hpc
          rwa [hp2] at this
        have hsymm : (permExtending c π).symm y = p.1 :=
          (Equiv.symm_apply_eq _).mpr hval.symm
        rw [show permFn (permExtending c π) (Sum.inr y)
            = (permExtending c π).symm y from rfl, hsymm]

/-- The duplex-sponge permutation oracle (a sum of the forward and backward single-query
specs) **is** the bridge's bidirectional spec: `OracleSpec ι` is just the range function,
and both assign `X` at every index. Lets the bridge consume `permutationOracle` programs
directly. -/
lemma permutationOracle_eq_sumSpec :
    OracleSpec.permutationOracle X = ((X ⊕ X) →ₒ X) := by
  funext t
  rcases t with a | b <;> rfl

end MasterInduction

end Facts

end LazyPermBridge

/-! ## Axiom audit — kernel-clean. -/
#print axioms LazyPermBridge.evalDist_sampleUnused_run
#print axioms LazyPermBridge.onestep_fiber_iff
#print axioms LazyPermBridge.extends_permExtending
#print axioms LazyPermBridge.map_onestep_uniform
#print axioms LazyPermBridge.map_permExtending_uniform
#print axioms LazyPermBridge.pmf_absorb
#print axioms LazyPermBridge.pmf_absorb_inv
#print axioms LazyPermBridge.evalDist_simulateQ_lazyPermImpl_run'
#print axioms LazyPermBridge.lazyPermImpl_run_map_flavored
#print axioms LazyPermBridge.map_permExtending_uniform_fintype
