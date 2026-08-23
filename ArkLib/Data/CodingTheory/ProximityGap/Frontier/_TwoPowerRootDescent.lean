/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TowerRootDescent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete root-count descent on the prize 2-power subgroup `μ_{2^μ}` (#407 / #444)

`_TowerRootDescent` proved the **abstract** root-count descent
`rootCount_descent_of_uniform_fiber`: when the `m`-th-power map is uniformly `k`-to-1 from an
evaluation set `G` onto a target `H`, the root count of the tower polynomial `Q.comp (X^m)` in `G`
is exactly `k ·` the base root count of `Q` in `H`. That theorem carries an abstract uniform-fiber
hypothesis (`hmap`/`hfib`). This file **discharges that hypothesis for the concrete prize
subgroup**: the `2^μ`-th roots of unity over a field `F` containing a primitive `2^μ`-th root.

Concretely, with `G = nthRootsFinset (2^μ) (1:F)` (the `2^μ`-th roots of unity) and
`H = nthRootsFinset (2^(μ-s)) (1:F)` (the `2^{μ-s}`-th roots of unity), for `s ≤ μ`:

* `pow_map_image` : `α ∈ μ_{2^μ} → α^(2^s) ∈ μ_{2^{μ-s}}` (the `hmap` instance). Immediate from
  `(α^{2^s})^{2^{μ-s}} = α^{2^μ} = 1`.
* `pow_map_fiber_card` : for `β ∈ μ_{2^{μ-s}}`, `#{α ∈ μ_{2^μ} : α^{2^s} = β} = 2^s` (the `hfib`
  instance). The fiber within `μ_{2^μ}` coincides with the **full** set of `2^s`-th roots of `β`
  (every such `α` automatically lies in `μ_{2^μ}` since `α^{2^μ} = β^{2^{μ-s}} = 1`); that set has
  exactly `2^s` elements — `card_nthRoots` gives `2^s` because a primitive `2^μ`-th root furnishes a
  primitive `2^s`-th root (so the `2^s`-power map is surjective onto `μ_{2^{μ-s}}`), and
  `nthRoots_nodup` makes them distinct.
* `rootCount_descent_two_pow` : the concrete corollary — the count of roots of the tower polynomial
  `Q.comp (X^{2^s})` in `μ_{2^μ}` is exactly `2^s ·` the count of base roots of `Q` in
  `μ_{2^{μ-s}}`, by applying `rootCount_descent_of_uniform_fiber` with `k = 2^s`.

**Honest scope.** This pins the **uniform-fiber** geometry of the off-BGK list recursion to the real
2-power group at any octave `s ≤ μ` — the list descends by exactly the fiber factor `2^s`,
prime-independently. It is NOT a closure: the base-count *bound* (the list upper bound, #444 c.97)
remains the open core, untouched here. Axiom-clean. Issues #407, #444.
-/

open Polynomial

namespace ProximityGap.Frontier.TwoPowerRootDescent

variable {F : Type*} [Field F]

/-- `α ↦ α^(2^s)` sends the `2^μ`-th roots of unity into the `2^{μ-s}`-th roots of unity (the
`hmap` instance for `rootCount_descent_of_uniform_fiber`). Pure exponent arithmetic:
`(α^{2^s})^{2^{μ-s}} = α^{2^μ} = 1`. -/
theorem pow_map_image {μ s : ℕ} (hs : s ≤ μ) {α : F}
    (hα : α ∈ nthRootsFinset (2 ^ μ) (1 : F)) :
    α ^ (2 ^ s) ∈ nthRootsFinset (2 ^ (μ - s)) (1 : F) := by
  rw [mem_nthRootsFinset (Nat.pow_pos (by norm_num : 0 < 2)) 1] at hα ⊢
  rw [← pow_mul, ← pow_add]
  rwa [Nat.add_sub_cancel' hs] at *

open Classical in
/-- The fiber `{α ∈ μ_{2^μ} : α^{2^s} = β}` coincides with the **full** set of `2^s`-th roots of `β`
in `F`, for any `β ∈ μ_{2^{μ-s}}`: every `α` with `α^{2^s} = β` automatically satisfies
`α^{2^μ} = β^{2^{μ-s}} = 1`, hence lies in `μ_{2^μ}`. -/
theorem fiber_eq_nthRootsFinset {μ s : ℕ} (hs : s ≤ μ) {β : F}
    (hβ : β ∈ nthRootsFinset (2 ^ (μ - s)) (1 : F)) :
    (nthRootsFinset (2 ^ μ) (1 : F)).filter (fun α => α ^ (2 ^ s) = β)
      = nthRootsFinset (2 ^ s) β := by
  rw [mem_nthRootsFinset (Nat.pow_pos (by norm_num : 0 < 2)) 1] at hβ
  ext α
  simp only [Finset.mem_filter, mem_nthRootsFinset (Nat.pow_pos (by norm_num : 0 < 2))]
  constructor
  · rintro ⟨_, hαβ⟩; exact hαβ
  · intro hαβ
    refine ⟨?_, hαβ⟩
    -- `α^{2^μ} = (α^{2^s})^{2^{μ-s}} = β^{2^{μ-s}} = 1`
    rw [show (2 : ℕ) ^ μ = 2 ^ s * 2 ^ (μ - s) by rw [← pow_add, Nat.add_sub_cancel' hs],
      pow_mul, hαβ, hβ]

open Classical in
/-- **Uniform fiber count (the `hfib` instance).** For `β ∈ μ_{2^{μ-s}}`, the fiber
`{α ∈ μ_{2^μ} : α^{2^s} = β}` has exactly `2^s` elements, GIVEN a primitive `2^μ`-th root of unity
in `F`. The fiber is the full set of `2^s`-th roots of `β`; that set has `2^s` distinct elements
because a primitive `2^μ`-th root furnishes both a primitive `2^s`-th root (`nthRoots_nodup`) and a
`2^s`-th-power preimage of `β` (surjectivity of the `2^s`-power map on the cyclic 2-group, via the
primitive `2^{μ-s}`-th root `ζ^{2^s}`). -/
theorem pow_map_fiber_card {μ s : ℕ} (hs : s ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ))
    {β : F} (hβ : β ∈ nthRootsFinset (2 ^ (μ - s)) (1 : F)) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter (fun α => α ^ (2 ^ s) = β)).card = 2 ^ s := by
  classical
  rw [fiber_eq_nthRootsFinset hs hβ]
  -- A primitive `2^s`-th root: `ζ^{2^{μ-s}}` (from `2^μ = 2^{μ-s} * 2^s`).
  have hζs : IsPrimitiveRoot (ζ ^ (2 ^ (μ - s))) (2 ^ s) :=
    hζ.pow (Nat.pow_pos (by norm_num : 0 < 2)) (by rw [← pow_add, Nat.sub_add_cancel hs])
  -- A primitive `2^{μ-s}`-th root: `ζ^{2^s}` (from `2^μ = 2^s * 2^{μ-s}`).
  have hζms : IsPrimitiveRoot (ζ ^ (2 ^ s)) (2 ^ (μ - s)) :=
    hζ.pow (Nat.pow_pos (by norm_num : 0 < 2)) (by rw [← pow_add, Nat.add_sub_cancel' hs])
  -- `β` has a `2^s`-th-power preimage: `β = (ζ^{2^s})^i = (ζ^i)^{2^s}` for some `i`.
  have hβpow : β ^ (2 ^ (μ - s)) = 1 := by
    rwa [mem_nthRootsFinset (Nat.pow_pos (by norm_num : 0 < 2)) 1] at hβ
  haveI : NeZero (2 ^ (μ - s)) := ⟨Nat.pow_pos (by norm_num : 0 < 2) |>.ne'⟩
  obtain ⟨i, _, hi⟩ := hζms.eq_pow_of_pow_eq_one hβpow
  have hexists : ∃ α : F, α ^ (2 ^ s) = β := by
    refine ⟨ζ ^ i, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hi]
  -- `nthRootsFinset (2^s) β` has `2^s` distinct roots.
  rw [nthRootsFinset_def, Multiset.toFinset_card_of_nodup (hζs.nthRoots_nodup ?_)]
  · rw [hζs.card_nthRoots, if_pos hexists]
  · -- `β ≠ 0`: it is a root of unity.
    rintro rfl
    rw [zero_pow (Nat.pow_pos (by norm_num : 0 < 2)).ne'] at hβpow
    exact one_ne_zero hβpow.symm

open Classical in
/-- **Concrete root-count descent on the prize 2-power subgroup.** Over a field `F` with a
primitive `2^μ`-th root of unity, for any octave `s ≤ μ` and any base polynomial `Q`, the count of
roots of the tower polynomial `Q.comp (X^{2^s})` in `μ_{2^μ}` is exactly `2^s ·` the count of base
roots of `Q` in `μ_{2^{μ-s}}`.

This is the concrete instance of `TowerRootDescent.rootCount_descent_of_uniform_fiber` with
`G = μ_{2^μ}`, `H = μ_{2^{μ-s}}`, `m = k = 2^s`, both hypotheses discharged by `pow_map_image`
(`hmap`) and `pow_map_fiber_card` (`hfib`). The list descends by exactly the fiber factor `2^s`,
prime-independently. -/
theorem rootCount_descent_two_pow {μ s : ℕ} (hs : s ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (Q : F[X]) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ (2 ^ s))).IsRoot α)).card
      = 2 ^ s * ((nthRootsFinset (2 ^ (μ - s)) (1 : F)).filter (fun β => Q.IsRoot β)).card :=
  TowerRootDescent.rootCount_descent_of_uniform_fiber Q (2 ^ s)
    (nthRootsFinset (2 ^ μ) (1 : F)) (nthRootsFinset (2 ^ (μ - s)) (1 : F)) (2 ^ s)
    (fun _ hα => pow_map_image hs hα)
    (fun _ hβ => pow_map_fiber_card hs hζ hβ)

open Classical in
/-- The one-octave (`s = 1`) corollary: the `2`-power map is `2`-to-1 from `μ_{2^μ}` onto
`μ_{2^{μ-1}}`, so the tower root count of `Q.comp (X^2)` in `μ_{2^μ}` is `2 ·` the base root count.
This is the single dyadic step of c.97's list recursion. -/
theorem rootCount_descent_two {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (Q : F[X]) :
    ((nthRootsFinset (2 ^ μ) (1 : F)).filter
        (fun α => (Q.comp (X ^ 2)).IsRoot α)).card
      = 2 * ((nthRootsFinset (2 ^ (μ - 1)) (1 : F)).filter (fun β => Q.IsRoot β)).card := by
  have := rootCount_descent_two_pow hμ hζ Q
  simpa using this

end ProximityGap.Frontier.TwoPowerRootDescent

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.TwoPowerRootDescent.pow_map_image
#print axioms ProximityGap.Frontier.TwoPowerRootDescent.fiber_eq_nthRootsFinset
#print axioms ProximityGap.Frontier.TwoPowerRootDescent.pow_map_fiber_card
#print axioms ProximityGap.Frontier.TwoPowerRootDescent.rootCount_descent_two_pow
#print axioms ProximityGap.Frontier.TwoPowerRootDescent.rootCount_descent_two
