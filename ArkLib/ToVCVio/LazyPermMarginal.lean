/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Marginals of a uniform permutation conditioned on a partial injection — counting core

Toward the **eager–lazy equivalence for random permutations** (the missing VCVio brick behind
CO25 Lemma 5.8, `Lemma5_8EagerPaperResidual`): VCVio's `RandomOracle/EagerTable.lean` provides
the bridge for random *functions*; the permutation analogue needs the conditional-marginal
fact that, for a uniform `π : Equiv.Perm X` conditioned on extending a partial injection `c`,
the value `π a` at a fresh point `a` is **uniform over the unused outputs** `X \ c.values`.

This file proves the counting core, with no probability semantics:

* `Extends π c` — `π` agrees with the association list `c`;
* `extendsFinset_card_eq_of_fresh` — the **swap-trick uniformity**: for fresh `a` and two
  unused outputs `b`, `b'`, the sets of permutations extending `c ⧺ [(a, b)]` and
  `c ⧺ [(a, b')]` are equinumerous (post-compose with `Equiv.swap b b'`);
* `extends_apply_ne_of_used` — an extension of `c` never sends a fresh input to a used
  output (injectivity), so the marginal is supported on the unused outputs;
* `extendsFinset_eq_biUnion` — the partition of the extensions of `c` by the value at `a`.

The probabilistic layer (uniform-permutation marginalization, the `simulateQ` induction
mirroring `EagerTable.lean`, and the per-step birthday bounds for CO25 Lemma 5.8) builds on
these in follow-up increments.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

namespace LazyPermMarginal

variable {X : Type} [DecidableEq X]

/-- `π` extends the association list `c`: it agrees with every recorded pair. -/
def Extends (π : Equiv.Perm X) (c : List (X × X)) : Prop :=
  ∀ p ∈ c, π p.1 = p.2

@[simp] lemma extends_nil (π : Equiv.Perm X) : Extends π ([] : List (X × X)) :=
  fun _ h => absurd h (List.not_mem_nil)

lemma extends_concat_iff (π : Equiv.Perm X) (c : List (X × X)) (a b : X) :
    Extends π (c.concat (a, b)) ↔ Extends π c ∧ π a = b := by
  simp only [Extends, List.concat_eq_append, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), h (a, b) (Or.inr rfl)⟩
  · rintro ⟨hc, hab⟩ p hp
    rcases hp with hp | rfl
    · exact hc p hp
    · exact hab

/-- An extension of `c` sends a fresh input only to unused outputs: if `a` is not a key of
`c` but `b` is a value of `c`, then `π a ≠ b`. -/
lemma extends_apply_ne_of_used {π : Equiv.Perm X} {c : List (X × X)}
    (hπ : Extends π c) {a b : X}
    (ha : a ∉ c.map Prod.fst) (hb : b ∈ c.map Prod.snd) : π a ≠ b := by
  intro hab
  obtain ⟨p, hp, hpb⟩ := List.mem_map.mp hb
  have hkey : π p.1 = p.2 := hπ p hp
  have : a = p.1 := π.injective (by rw [hab, hkey, hpb])
  exact ha (List.mem_map.mpr ⟨p, hp, this.symm⟩)

section Fintype

variable [Fintype X]

/-- The finset of permutations extending `c`. -/
noncomputable def extendsFinset (c : List (X × X)) : Finset (Equiv.Perm X) := by
  classical
  exact Finset.univ.filter (fun π => Extends π c)

@[simp] lemma mem_extendsFinset {c : List (X × X)} {π : Equiv.Perm X} :
    π ∈ extendsFinset c ↔ Extends π c := by
  classical
  simp [extendsFinset]

/-- **The swap trick**: post-composing with `Equiv.swap b b'` exchanges the extensions of
`c ⧺ [(a, b)]` and `c ⧺ [(a, b')]` whenever neither `b` nor `b'` is a used output. Hence the
two extension sets are equinumerous — the heart of the conditional-marginal uniformity. -/
theorem extendsFinset_card_eq_of_fresh (c : List (X × X)) (a b b' : X)
    (hb : b ∉ c.map Prod.snd) (hb' : b' ∉ c.map Prod.snd) :
    (extendsFinset (c.concat (a, b))).card = (extendsFinset (c.concat (a, b'))).card := by
  classical
  refine Finset.card_bij (fun π _ => (Equiv.swap b b').trans π.symm |>.symm) ?_ ?_ ?_
  · -- maps into the target extension set
    intro π hπ
    rw [mem_extendsFinset, extends_concat_iff] at hπ ⊢
    obtain ⟨hc, hab⟩ := hπ
    constructor
    · intro p hp
      have hval : π p.1 = p.2 := hc p hp
      have hpb : p.2 ≠ b := fun h => hb (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hpb' : p.2 ≠ b' := fun h => hb' (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      show Equiv.swap b b' (π p.1) = p.2
      rw [hval, Equiv.swap_apply_of_ne_of_ne hpb hpb']
    · show Equiv.swap b b' (π a) = b'
      rw [hab, Equiv.swap_apply_left]
  · -- injective
    intro π₁ h₁ π₂ h₂ heq
    have h1 : (Equiv.swap b b').trans π₁.symm = (Equiv.swap b b').trans π₂.symm := by
      have := congrArg Equiv.symm heq
      simpa using this
    have h2 : π₁.symm = π₂.symm := by
      have := congrArg (fun e => (Equiv.swap b b').symm.trans e) h1
      simpa [← Equiv.trans_assoc] using this
    have := congrArg Equiv.symm h2
    simpa using this
  · -- surjective
    intro τ hτ
    refine ⟨((Equiv.swap b b').trans τ.symm).symm, ?_, ?_⟩
    · rw [mem_extendsFinset, extends_concat_iff] at hτ ⊢
      obtain ⟨hc, hab'⟩ := hτ
      constructor
      · intro p hp
        have hval : τ p.1 = p.2 := hc p hp
        have hpb : p.2 ≠ b := fun h => hb (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        have hpb' : p.2 ≠ b' := fun h => hb' (h ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        show Equiv.swap b b' (τ p.1) = p.2
        rw [hval, Equiv.swap_apply_of_ne_of_ne hpb hpb']
      · show Equiv.swap b b' (τ a) = b
        rw [hab', Equiv.swap_apply_right]
    · apply Equiv.ext
      intro x
      simp [Equiv.swap_apply_self]

/-- The extensions of `c` partition by the value at a fresh input `a`, over unused outputs. -/
theorem extendsFinset_eq_biUnion (c : List (X × X)) (a : X)
    (ha : a ∉ c.map Prod.fst) :
    extendsFinset c =
      ((Finset.univ.filter (fun b => b ∉ c.map Prod.snd)).biUnion
        (fun b => extendsFinset (c.concat (a, b)))) := by
  classical
  ext π
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_extendsFinset]
  constructor
  · intro hπ
    refine ⟨π a, ?_, ?_⟩
    · intro hused
      exact extends_apply_ne_of_used hπ ha hused rfl
    · exact (extends_concat_iff π c a (π a)).mpr ⟨hπ, rfl⟩
  · rintro ⟨b, _, hext⟩
    exact ((extends_concat_iff π c a b).mp hext).1

/-- The pieces of the partition are pairwise disjoint (a permutation has one value at `a`). -/
theorem extendsFinset_concat_disjoint (c : List (X × X)) (a : X) {b b' : X} (hbb' : b ≠ b') :
    Disjoint (extendsFinset (c.concat (a, b))) (extendsFinset (c.concat (a, b'))) := by
  classical
  refine Finset.disjoint_left.mpr fun π hπ hπ' => ?_
  rw [mem_extendsFinset, extends_concat_iff] at hπ hπ'
  exact hbb' (hπ.2.symm.trans hπ'.2)

/-- **Cardinality form of the marginal**: the extensions of `c` split as
`(#unused outputs) · (#extensions of c ⧺ [(a, b₀)])` for any unused reference output `b₀`. -/
theorem card_extendsFinset_eq_card_unused_mul (c : List (X × X)) (a b₀ : X)
    (ha : a ∉ c.map Prod.fst) (hb₀ : b₀ ∉ c.map Prod.snd) :
    (extendsFinset c).card =
      (Finset.univ.filter (fun b : X => b ∉ c.map Prod.snd)).card *
        (extendsFinset (c.concat (a, b₀))).card := by
  classical
  rw [extendsFinset_eq_biUnion c a ha,
    Finset.card_biUnion (fun b _ b' _ hbb' => extendsFinset_concat_disjoint c a hbb')]
  rw [Finset.sum_congr rfl (fun b hb => extendsFinset_card_eq_of_fresh c a b b₀
      (Finset.mem_filter.mp hb).2 hb₀)]
  rw [Finset.sum_const, smul_eq_mul]

/-! ## Inversion symmetry — the bidirectional cache

The duplex-sponge carrier answers `p` and `p⁻¹` through one permutation, so the lazy cache
records pairs queried in *either* direction. Inversion is an involution exchanging the roles
of keys and values, letting every forward-direction lemma transport to inverse queries. -/

@[simp] lemma extends_symm_swap_iff (π : Equiv.Perm X) (c : List (X × X)) :
    Extends π.symm (c.map Prod.swap) ↔ Extends π c := by
  constructor
  · intro h p hp
    have := h p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa using congrArg π this.symm
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have := h p hp
    simpa using congrArg π.symm this.symm

/-! ## Nonemptiness propagation and the probabilistic chain rule -/

/-- The unused outputs of a cache. -/
noncomputable def unusedFinset (c : List (X × X)) : Finset X := by
  classical
  exact Finset.univ.filter (fun b => b ∉ c.map Prod.snd)

@[simp] lemma mem_unusedFinset {c : List (X × X)} {b : X} :
    b ∈ unusedFinset c ↔ b ∉ c.map Prod.snd := by
  classical
  simp [unusedFinset]

/-- A fresh input plus duplicate-free keys and values leave at least one unused output. -/
lemma unusedFinset_nonempty (c : List (X × X)) (a : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) : (unusedFinset c).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hall : ∀ b : X, b ∈ c.map Prod.snd := by
    intro b
    by_contra hb
    exact (Finset.eq_empty_iff_forall_notMem.mp hempty b) (mem_unusedFinset.mpr hb)
  -- the value list covers `X`, so the key list (same length, nodup) covers `X` too,
  -- contradicting the freshness of `a`
  have hcardv : (c.map Prod.snd).toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hvals, List.length_map]
  have hcardk : (c.map Prod.fst).toFinset.card = c.length := by
    rw [List.toFinset_card_of_nodup hkeys, List.length_map]
  have huniv : (c.map Prod.snd).toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun b => List.mem_toFinset.mpr (hall b))
  have hkuniv : (c.map Prod.fst).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardk, ← hcardv, huniv, Finset.card_univ]
  exact ha (List.mem_toFinset.mp (hkuniv ▸ Finset.mem_univ a))

/-- **Nonemptiness propagates along fresh extensions**: if the cache is realizable, every
unused output is a realizable value at a fresh input (swap-trick equidistribution: all
fibres of the partition have equal cardinality, and their union is nonempty). -/
theorem extendsFinset_concat_nonempty (c : List (X × X)) (a b : X)
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd)
    (hne : (extendsFinset c).Nonempty) :
    (extendsFinset (c.concat (a, b))).Nonempty := by
  classical
  rw [← Finset.card_pos]
  by_contra hzero
  push_neg at hzero
  have hzero' : (extendsFinset (c.concat (a, b))).card = 0 := Nat.le_zero.mp hzero
  have hcard := card_extendsFinset_eq_card_unused_mul c a b ha hb
  rw [hzero', mul_zero] at hcard
  exact (Finset.card_pos.mpr hne).ne' hcard

/-- **The probabilistic chain rule for a uniform permutation conditioned on a cache**:
drawing uniformly among the extensions of `c` is the same as first drawing the value at a
fresh input `a` uniformly among the unused outputs, then drawing uniformly among the
extensions of the grown cache. This is the per-query step of the lazy permutation oracle. -/
theorem uniformOfFinset_extends_step (c : List (X × X)) (a : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (ha : a ∉ c.map Prod.fst) (hne : (extendsFinset c).Nonempty) :
    PMF.uniformOfFinset (extendsFinset c) hne
      = (PMF.uniformOfFinset (unusedFinset c)
          (unusedFinset_nonempty c a hkeys hvals ha)).bind (fun b =>
            if h : (extendsFinset (c.concat (a, b))).Nonempty then
              PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h
            else PMF.uniformOfFinset (extendsFinset c) hne) := by
  classical
  ext π
  rw [PMF.bind_apply]
  by_cases hπ : Extends π c
  · -- only the summand `b = π a` contributes
    have hπa_unused : π a ∈ unusedFinset c := by
      rw [mem_unusedFinset]
      intro hused
      exact extends_apply_ne_of_used hπ ha hused rfl
    have hπext : Extends π (c.concat (a, π a)) :=
      (extends_concat_iff π c a (π a)).mpr ⟨hπ, rfl⟩
    have hconc : (extendsFinset (c.concat (a, π a))).Nonempty :=
      ⟨π, mem_extendsFinset.mpr hπext⟩
    have hside : ∀ b, b ≠ π a →
        (PMF.uniformOfFinset (unusedFinset c)
            (unusedFinset_nonempty c a hkeys hvals ha)) b *
          (if h : (extendsFinset (c.concat (a, b))).Nonempty then
              PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h
            else PMF.uniformOfFinset (extendsFinset c) hne) π = 0 := by
      intro b hb
      by_cases hbu : b ∈ unusedFinset c
      · rw [dif_pos (extendsFinset_concat_nonempty c a b ha (mem_unusedFinset.mp hbu) hne)]
        have hnotin : π ∉ extendsFinset (c.concat (a, b)) := by
          rw [mem_extendsFinset, extends_concat_iff]
          rintro ⟨-, hab⟩
          exact hb hab.symm
        rw [PMF.uniformOfFinset_apply_of_notMem (hs := extendsFinset_concat_nonempty c a b ha (mem_unusedFinset.mp hbu) hne) hnotin, mul_zero]
      · rw [PMF.uniformOfFinset_apply_of_notMem (hs := unusedFinset_nonempty c a hkeys hvals ha) hbu, zero_mul]
    rw [tsum_eq_single (π a) hside, PMF.uniformOfFinset_apply_of_mem (hs := unusedFinset_nonempty c a hkeys hvals ha) hπa_unused,
      dif_pos hconc, PMF.uniformOfFinset_apply_of_mem (hs := hconc) (mem_extendsFinset.mpr hπext),
      PMF.uniformOfFinset_apply_of_mem (hs := hne) (mem_extendsFinset.mpr hπ)]
    have hN := card_extendsFinset_eq_card_unused_mul c a (π a) ha
      (mem_unusedFinset.mp hπa_unused)
    rw [hN, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inl (ENNReal.natCast_ne_top _))]
    rfl
  · -- both sides vanish off the extensions of `c`
    rw [PMF.uniformOfFinset_apply_of_notMem (hs := hne) (fun h => hπ (mem_extendsFinset.mp h))]
    refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
    by_cases hbu : b ∈ unusedFinset c
    · rw [dif_pos (extendsFinset_concat_nonempty c a b ha (mem_unusedFinset.mp hbu) hne)]
      have hnotin : π ∉ extendsFinset (c.concat (a, b)) := by
        rw [mem_extendsFinset]
        intro hext
        exact hπ ((extends_concat_iff π c a b).mp hext).1
      rw [PMF.uniformOfFinset_apply_of_notMem (hs := extendsFinset_concat_nonempty c a b ha (mem_unusedFinset.mp hbu) hne) hnotin, mul_zero]
    · rw [PMF.uniformOfFinset_apply_of_notMem (hs := unusedFinset_nonempty c a hkeys hvals ha) hbu, zero_mul]

/-- Inversion as a bijection between extension sets: the extensions of the swapped cache
are exactly the inverses of the extensions of `c`. -/
lemma extendsFinset_swap_card (c : List (X × X)) :
    (extendsFinset (c.map Prod.swap)).card = (extendsFinset c).card := by
  classical
  refine Finset.card_bij (fun π _ => π.symm) ?_ ?_ ?_
  · intro π hπ
    rw [mem_extendsFinset] at hπ ⊢
    exact (extends_symm_swap_iff π.symm c).mp (by simpa using hπ)
  · intro π₁ _ π₂ _ h
    simpa using congrArg Equiv.symm h
  · intro τ hτ
    exact ⟨τ.symm, by
      rw [mem_extendsFinset] at hτ ⊢
      exact (extends_symm_swap_iff τ c).mpr hτ, by simp⟩

/-- Mapping inversion over the uniform distribution on the swapped cache's extensions gives
the uniform distribution on the original cache's extensions. -/
lemma map_symm_uniform_extends_swap (d : List (X × X))
    (hne : (extendsFinset d).Nonempty)
    (hneswap : (extendsFinset (d.map Prod.swap)).Nonempty) :
    (PMF.uniformOfFinset (extendsFinset (d.map Prod.swap)) hneswap).map
      (fun π : Equiv.Perm X => π.symm)
      = PMF.uniformOfFinset (extendsFinset d) hne := by
  classical
  ext τ
  rw [PMF.map_apply]
  rw [tsum_eq_single τ.symm (fun π hπ => by
    rw [if_neg]
    intro h
    have e : τ.symm = π := by simpa using congrArg Equiv.symm h
    exact hπ e.symm)]
  rw [if_pos (by simp)]
  by_cases hτ : Extends τ d
  · rw [PMF.uniformOfFinset_apply_of_mem (hs := hneswap)
      (mem_extendsFinset.mpr ((extends_symm_swap_iff τ d).mpr hτ)),
      PMF.uniformOfFinset_apply_of_mem (hs := hne) (mem_extendsFinset.mpr hτ),
      extendsFinset_swap_card]
  · rw [PMF.uniformOfFinset_apply_of_notMem (hs := hneswap)
      (fun h => hτ ((extends_symm_swap_iff τ d).mp (mem_extendsFinset.mp h))),
      PMF.uniformOfFinset_apply_of_notMem (hs := hne)
        (fun h => hτ (mem_extendsFinset.mp h))]

/-- `bind` only depends on the function over the support. -/
lemma bind_congr_support {α β : Type} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have ha0 : p a = 0 := by
      rw [PMF.mem_support_iff] at ha
      push_neg at ha
      exact ha
    rw [ha0, zero_mul, zero_mul]

/-- **The inverse-direction chain rule**: drawing uniformly among the extensions of `c` is
the same as first drawing the *preimage* at a fresh output `b` uniformly among the unused
keys, then drawing uniformly among the extensions of the cache grown by `(a, b)`. Transport
of `uniformOfFinset_extends_step` along the inversion involution. -/
theorem uniformOfFinset_extends_step_inv (c : List (X × X)) (b : X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (hb : b ∉ c.map Prod.snd) (hne : (extendsFinset c).Nonempty) :
    PMF.uniformOfFinset (extendsFinset c) hne
      = (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
          (unusedFinset_nonempty (c.map Prod.swap) b
            (by simpa [List.map_map, Function.comp_def] using hvals)
            (by simpa [List.map_map, Function.comp_def] using hkeys)
            (by simpa [List.map_map, Function.comp_def] using hb))).bind (fun a =>
            if h : (extendsFinset (c.concat (a, b))).Nonempty then
              PMF.uniformOfFinset (extendsFinset (c.concat (a, b))) h
            else PMF.uniformOfFinset (extendsFinset c) hne) := by
  classical
  have hswapk : ((c.map Prod.swap).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using hvals
  have hswapv : ((c.map Prod.swap).map Prod.snd).Nodup := by
    simpa [List.map_map, Function.comp_def] using hkeys
  have hbswap : b ∉ (c.map Prod.swap).map Prod.fst := by
    simpa [List.map_map, Function.comp_def] using hb
  have hneswap : (extendsFinset (c.map Prod.swap)).Nonempty := by
    obtain ⟨π, hπ⟩ := hne
    exact ⟨π.symm, mem_extendsFinset.mpr
      ((extends_symm_swap_iff π c).mpr (mem_extendsFinset.mp hπ))⟩
  have hstep := uniformOfFinset_extends_step (c.map Prod.swap) b
    hswapk hswapv hbswap hneswap
  have hconcat_swap : ∀ a : X, (c.map Prod.swap).concat (b, a)
      = (c.concat (a, b)).map Prod.swap := by
    intro a
    simp [List.concat_eq_append]
  calc PMF.uniformOfFinset (extendsFinset c) hne
      = (PMF.uniformOfFinset (extendsFinset (c.map Prod.swap)) hneswap).map
          (fun π : Equiv.Perm X => π.symm) :=
        (map_symm_uniform_extends_swap c hne hneswap).symm
    _ = ((PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
          (unusedFinset_nonempty (c.map Prod.swap) b hswapk hswapv hbswap)).bind
            (fun a =>
              if h : (extendsFinset ((c.map Prod.swap).concat (b, a))).Nonempty then
                PMF.uniformOfFinset (extendsFinset ((c.map Prod.swap).concat (b, a))) h
              else PMF.uniformOfFinset (extendsFinset (c.map Prod.swap)) hneswap)).map
          (fun π : Equiv.Perm X => π.symm) := by rw [← hstep]
    _ = (PMF.uniformOfFinset (unusedFinset (c.map Prod.swap))
          (unusedFinset_nonempty (c.map Prod.swap) b hswapk hswapv hbswap)).bind
            (fun a =>
              (if h : (extendsFinset ((c.map Prod.swap).concat (b, a))).Nonempty then
                PMF.uniformOfFinset (extendsFinset ((c.map Prod.swap).concat (b, a))) h
              else PMF.uniformOfFinset (extendsFinset (c.map Prod.swap)) hneswap).map
                (fun π : Equiv.Perm X => π.symm)) := PMF.map_bind _ _ _
    _ = _ := by
        refine bind_congr_support _ _ _ fun a ha => ?_
        rw [PMF.mem_support_uniformOfFinset_iff, mem_unusedFinset] at ha
        have haK : a ∉ c.map Prod.fst := by
          simpa [List.map_map, Function.comp_def] using ha
        have hposSwap : (extendsFinset ((c.map Prod.swap).concat (b, a))).Nonempty :=
          extendsFinset_concat_nonempty (c.map Prod.swap) b a hbswap
            (by simpa [List.map_map, Function.comp_def] using haK) hneswap
        have hpos : (extendsFinset (c.concat (a, b))).Nonempty := by
          obtain ⟨π, hπ⟩ := hposSwap
          refine ⟨π.symm, mem_extendsFinset.mpr ?_⟩
          have := (extends_symm_swap_iff π.symm (c.concat (a, b))).mp ?_
          · exact this
          · rw [← hconcat_swap a]
            simpa using mem_extendsFinset.mp hπ
        rw [dif_pos hposSwap, dif_pos hpos]
        have hcc : (c.map Prod.swap).concat (b, a) = (c.concat (a, b)).map Prod.swap :=
          hconcat_swap a
        simp only [hcc]
        exact map_symm_uniform_extends_swap (c.concat (a, b)) hpos (hcc ▸ hposSwap)

end Fintype

end LazyPermMarginal

/-! ## Axiom audit — kernel-clean. -/
#print axioms LazyPermMarginal.extendsFinset_card_eq_of_fresh
#print axioms LazyPermMarginal.card_extendsFinset_eq_card_unused_mul
#print axioms LazyPermMarginal.uniformOfFinset_extends_step
#print axioms LazyPermMarginal.extendsFinset_concat_nonempty
#print axioms LazyPermMarginal.uniformOfFinset_extends_step_inv
