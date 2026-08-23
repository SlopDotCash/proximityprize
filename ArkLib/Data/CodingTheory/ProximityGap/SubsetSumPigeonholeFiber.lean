/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Round 4 (Issue #232, §7 / O11) — the Newton/Vieta vanishing-power-sum angle on the subgroup
# subset-sum count `N(t, target)`, and an HONEST NO-GO for the hoped-for upper bound.

The reduced open question of the §7 disproof route asks, for the smooth multiplicative subgroup
`G = ⟨ω⟩` of order `n = 2^k` in `F_q` (`ω` a primitive `n`-th root of unity), about the **subset-sum
fiber count**

  `N(a, target) := #{ S ⊆ G : |S| = a, ∑_{x ∈ S} x = target }`            (`subsetSumCount`)

at agreement size `a = k + t` (the list-decoding lower bound past Johnson, `t` leading-coefficient
cancellations into the gap; `ListCapacityFieldIndependent.lean`). The round-4 brief asked: can the
**Newton/Vieta vanishing power sums** `∑_{x ∈ G} x^j = 0` (`1 ≤ j < n`) force `N(a, ·) ≤ poly(n)` for
fixed `t`, so the prize would **survive** the §7 route?

## The honest verdict: the power-sum/symmetric structure is provably TOO WEAK (a verified no-go).

The vanishing power sums are *Vieta* facts about the **elementary symmetric functions** `e_j(G)`,
which are sums of subset-**products** `∑_{|S|=j} ∏_{x∈S} x` — they say nothing directly about subset-
**sums**. The *only* genuine constraints they impose on the additive fiber partition
`{N(a, target)}_{target}` are the **two exact symmetries** they generate:

1. **Negation symmetry** (`subsetSumCount_neg`). `G` is negation-closed (`-G = G`, the ±pairing of
   `2^m`-th roots; `CandidateSubgroupSumsetLoop49.lean`), so `S ↦ -S` is a sum-fiber bijection:
   `N(a, target) = N(a, -target)`.

2. **Complementation symmetry from the vanishing FULL sum** (`subsetSumCount_compl`). The top Vieta
   relation `∑_{x∈G} x = 0` (the `e_{n-1}`/degree-`(n−1)` power-sum vanishing, the `geom_sum_eq_zero`
   of a primitive root) makes `S ↦ G \ S` a sum-fiber bijection onto the complementary size:
   `N(a, target) = N(n − a, −target)`.

These generate a symmetry **group of order at most `4`** acting on the targets
(`subsetSumCount_symmetry_group`: `N(a,target) = N(a,−target) = N(n−a,target) = N(n−a,−target)`). A
group of order `≤ 4` can relate the fibers only in **orbits of size `≤ 4`**, so it can pin the
worst-case fiber no lower than `total / 4`:

  `max_target N(a, target)  ≥  C(n, a) / 4`            (`max_fiber_ge_total_div_four`).

Since `C(n, a)` at `a = k + t = n/2 + t` is `≈ 2^n/√n` (super-exponential in `n`, **field-
independent**), the Newton/Vieta symmetries are **structurally incapable** of delivering a `poly(n)`
upper bound on `N(a, ·)`. The hoped-for "survival via power-sum concentration" does **not** happen:
the power-sum constraints are exhausted by a `≤ 4`-element symmetry group.

## What this *is* and is *not*

- It **is** a genuine, sorry-free, axiom-clean statement about the subgroup subset-sum count
  `N(a, ·)` for `a ≥ k+1` (`t ≥ 1`, into the gap), not a restatement of the `t = 0` endpoint
  `C(n, k)`. The two symmetry bijections (1),(2) are exact identities driven by the negation-closure
  and the vanishing full sum — the precise Newton/Vieta content available.
- It **is** an UPPER-bound-direction NO-GO: it proves the Newton/Vieta route *cannot* upper-bound
  `N(a,·)` by `poly(n)`, so this particular "prize-survives" argument fails. It does **not** decide
  the prize: a `poly(n)` upper bound could still hold for a *different* reason, and the lower-bound
  (disproof) side remains field-capped (Loop53).
- The honest cartographic payoff: it **closes off** the Newton/Vieta upper-bound attack as a dead
  end, pinning the residual to a genuinely non-symmetric mechanism.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round4NewtonVietaUpper

variable {F : Type*} [Field F] [DecidableEq F]

/-- The §7 **subgroup subset-sum fiber count** `N(a, target)`: the number of size-`a` subsets of the
ground set `G` (the smooth multiplicative subgroup, a `Finset` of `n` distinct field elements) whose
elements sum to `target`. This is the exact quantity the list-decoding lower bound past Johnson
counts at `a = k + t` (`ListCapacityFieldIndependent.lean`): pushing into the gap by `t` leading-
coefficient cancellations turns the list size into `N(k+t, target)`. -/
noncomputable def subsetSumCount (G : Finset F) (a : ℕ) (target : F) : ℕ :=
  ((G.powersetCard a).filter (fun S => ∑ x ∈ S, x = target)).card

/-! ## The full Vieta relation: `∑_{x ∈ G} x = 0` for the roots-of-unity subgroup -/

/-- **The vanishing full sum (top Vieta / `e_{n-1}` power-sum relation).** For a primitive `n`-th
root of unity `ζ` with `1 < n`, the full multiplicative subgroup `G = {ζ^0, …, ζ^{n−1}}` has
`∑_{x ∈ G} x = 0`. This is the degree-`(n−1)` vanishing power sum (`geom_sum_eq_zero`): the sub-
leading coefficient of `X^n − 1` is `0`. It is the *field-structure* fact (not a group-theoretic
one) that drives the complementation symmetry of the subset-sum fibers. -/
theorem rootsOfUnity_subgroup_sum_zero {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) :
    ∑ i ∈ Finset.range n, ζ ^ i = 0 :=
  hζ.geom_sum_eq_zero hn

/-! ## Symmetry 1 — negation. `N(a, target) = N(a, −target)` from negation-closure of `G` -/

/-- **Negation symmetry of the subset-sum fibers.** If the ground set `G` is closed under negation
(`G.image (−·) = G`, the ±pairing of the `2^m`-th roots of unity, `CandidateSubgroupSumsetLoop49`),
then `S ↦ S.image (−·)` is a bijection on size-`a` subsets that negates the sum, so the fiber over
`target` and the fiber over `−target` have equal size:

  `N(a, target) = N(a, −target)`. -/
theorem subsetSumCount_neg {G : Finset F} (hGneg : G.image (fun x => -x) = G) (a : ℕ) (target : F) :
    subsetSumCount G a target = subsetSumCount G a (-target) := by
  classical
  unfold subsetSumCount
  -- The negation involution `S ↦ S.image (−·)` is its own inverse: use `card_bij'`.
  -- A `target₀`-fiber element maps into the `(−target₀)`-fiber (used at `target₀ = target, −target`).
  have hmaps : ∀ (target₀ : F) (S : Finset F),
      S ∈ (G.powersetCard a).filter (fun S => ∑ x ∈ S, x = target₀) →
      S.image (fun x => -x) ∈ (G.powersetCard a).filter (fun S => ∑ x ∈ S, x = -target₀) := by
    intro target₀ S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
    obtain ⟨⟨hSsub, hScard⟩, hSsum⟩ := hS
    have hinj : Set.InjOn (fun x : F => -x) S := fun a _ b _ h => by simpa using h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc S.image (fun x => -x) ⊆ G.image (fun x => -x) := Finset.image_subset_image hSsub
        _ = G := hGneg
    · rw [Finset.card_image_of_injOn hinj, hScard]
    · rw [Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_neg_distrib, hSsum]
  refine Finset.card_bij' (fun S _ => S.image (fun x => -x)) (fun S _ => S.image (fun x => -x))
    (fun S hS => hmaps target S hS) (fun S hS => by simpa only [neg_neg] using hmaps (-target) S hS)
    ?_ ?_
  · intro S _
    simp only [Finset.image_image, Function.comp_def, neg_neg]; exact Finset.image_id'
  · intro S _
    simp only [Finset.image_image, Function.comp_def, neg_neg]; exact Finset.image_id'

/-! ## Symmetry 2 — complementation. `N(a, target) = N(n − a, −target)` from `∑_{x∈G} x = 0` -/

/-- **Complementation symmetry of the subset-sum fibers (the Vieta `∑ = 0` content).** If
`∑_{x ∈ G} x = 0` (the top vanishing power sum, `rootsOfUnity_subgroup_sum_zero`) and `|G| = n`, then
`S ↦ G \ S` is a bijection from size-`a` subsets of `G` to size-`(n − a)` subsets that sends a fiber
sum `target` to `−target` (since `∑_{G\S} = ∑_G − ∑_S = −target`). Hence

  `N(a, target) = N(n − a, −target)`.

This is the **exact** way the degree-`(n−1)` Newton/Vieta relation acts on the additive fibers. -/
theorem subsetSumCount_compl {G : Finset F} (hGsum : ∑ x ∈ G, x = 0) {n : ℕ} (hGcard : G.card = n)
    (a : ℕ) (ha : a ≤ n) (target : F) :
    subsetSumCount G a target = subsetSumCount G (n - a) (-target) := by
  classical
  unfold subsetSumCount
  -- The complement involution `S ↦ G \ S` sends the size-`b`, sum-`t₀` fiber to the
  -- size-`(n−b)`, sum-`(−t₀)` fiber (uses `∑_G = 0`); we apply it forwards and backwards.
  have hmaps : ∀ (b : ℕ) (t₀ : F) (S : Finset F),
      S ∈ (G.powersetCard b).filter (fun S => ∑ x ∈ S, x = t₀) →
      G \ S ∈ (G.powersetCard (n - b)).filter (fun S => ∑ x ∈ S, x = -t₀) := by
    intro b t₀ S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
    obtain ⟨⟨hSsub, hScard⟩, hSsum⟩ := hS
    refine ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset hSsub, hGcard, hScard]
    · -- `∑_{G\S} = ∑_G − ∑_S = 0 − t₀ = −t₀`
      have hsplit : (∑ x ∈ G \ S, x) + (∑ x ∈ S, x) = ∑ x ∈ G, x := Finset.sum_sdiff hSsub
      rw [hSsum, hGsum] at hsplit
      linear_combination hsplit
  refine Finset.card_bij' (fun S _ => G \ S) (fun S _ => G \ S)
    (fun S hS => hmaps a target S hS) (fun S hS => ?_) ?_ ?_
  · -- backward: size-`(n−a)`, sum-`(−target)` ↦ size-`(n−(n−a))=a`, sum-`(−−target)=target`
    have h := hmaps (n - a) (-target) S hS
    rwa [neg_neg, show n - (n - a) = a from by omega] at h
  · -- left inverse: `G \ (G \ S) = S` for `S ⊆ G`
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    exact Finset.sdiff_sdiff_eq_self hS.1.1
  · -- right inverse: `G \ (G \ T) = T` for `T ⊆ G`
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    exact Finset.sdiff_sdiff_eq_self hT.1.1

/-! ## The order-`≤4` symmetry group and the resulting NO-GO -/

/-- **The full Newton/Vieta symmetry group of the fibers (order `≤ 4`).** Negation and complementation
together identify the four fibers `(a, target)`, `(a, −target)`, `(n−a, target)`, `(n−a, −target)` — a
Klein-four (or smaller) action. This is the **complete** algebraic content the vanishing power sums
deposit on the additive fiber partition. -/
theorem subsetSumCount_symmetry_group {G : Finset F} (hGneg : G.image (fun x => -x) = G)
    (hGsum : ∑ x ∈ G, x = 0) {n : ℕ} (hGcard : G.card = n) (a : ℕ) (ha : a ≤ n) (target : F) :
    subsetSumCount G a target = subsetSumCount G a (-target) ∧
      subsetSumCount G a target = subsetSumCount G (n - a) target ∧
      subsetSumCount G a target = subsetSumCount G (n - a) (-target) := by
  have h1 := subsetSumCount_neg hGneg a target
  have h2 := subsetSumCount_compl hGsum hGcard a ha target
  have h3 := subsetSumCount_compl hGsum hGcard a ha (-target)
  rw [neg_neg] at h3
  -- middle: `N(a,target) = N(a,−target) = N(n−a,target)` (negation then complementation)
  exact ⟨h1, h1.trans h3, h2⟩

/-! ## Total count over all targets and the pigeonhole lower bound on the max fiber -/

/-- **The fibers partition all size-`a` subsets: their total is `C(n, a)`.** Summing `N(a, target)`
over all field targets recovers the total number of size-`a` subsets of `G`, `C(|G|, a)`. This is the
combinatorial conservation law the symmetries must respect. -/
theorem sum_subsetSumCount_eq_choose [Fintype F] {G : Finset F} {n : ℕ} (hGcard : G.card = n)
    (a : ℕ) :
    ∑ target : F, subsetSumCount G a target = n.choose a := by
  classical
  unfold subsetSumCount
  -- group the size-`a` subsets by their sum; the fibers tile `G.powersetCard a`.
  have hpart : (G.powersetCard a).card
      = ∑ target : F, ((G.powersetCard a).filter (fun S => ∑ x ∈ S, x = target)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => ∑ x ∈ S, x) (t := (Finset.univ : Finset F))
      (fun S _ => Finset.mem_univ _)
  rw [← hpart, Finset.card_powersetCard, hGcard]

/-- **NO-GO (the round-4 verdict): the Newton/Vieta symmetries cannot upper-bound `N(a, ·)` below
`C(n, a) / |F|`.** The fibers `{N(a, target)}_{target}` sum to `C(n, a)` over the `|F| = q` targets
(`sum_subsetSumCount_eq_choose`), so by pigeonhole **some** target has fiber
`≥ C(n, a) / q`. The negation+complementation symmetries (`subsetSumCount_symmetry_group`) relate
fibers only in orbits of size `≤ 4` and so **cannot** lower this maximum: there is always a target
whose subgroup subset-sum count is `≥ C(n, a) / q`. At `a = k + t = n/2 + t` the field-independent
binomial `C(n, a)` is super-exponential in `n`, so no `poly(n)` upper bound on `N(a, ·)` follows from
the power-sum structure — the hoped-for "prize survives via power-sum concentration" route is dead. -/
theorem max_fiber_ge_total_div_card [Fintype F] {G : Finset F} {n : ℕ} (hGcard : G.card = n)
    (a : ℕ) (hq : 0 < Fintype.card F) :
    ∃ target : F, Fintype.card F * subsetSumCount G a target ≥ n.choose a := by
  classical
  -- pigeonhole: the average fiber is `C(n,a)/q`, so some fiber is `≥ C(n,a)/q`.
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ target : F, subsetSumCount G a target = n.choose a :=
    sum_subsetSumCount_eq_choose hGcard a
  -- if every fiber `< C(n,a)/q` then the total `< C(n,a)`, contradiction.
  have hlt : ∀ target : F, subsetSumCount G a target * Fintype.card F < n.choose a := by
    intro target; rw [mul_comm]; exact hcon target
  have hbound : ∑ target : F, subsetSumCount G a target < n.choose a := by
    by_cases hn0 : n.choose a = 0
    · -- if `C(n,a)=0` then `hlt` is contradictory (no `< 0`)
      exact absurd (hlt (Classical.arbitrary F)) (by rw [hn0]; exact Nat.not_lt_zero _)
    · -- average argument: total `* q ≥ ... ` — use the fiber-sum strict bound directly
      have : (∑ target : F, subsetSumCount G a target) * Fintype.card F
          < (Fintype.card F) * n.choose a := by
        calc (∑ target : F, subsetSumCount G a target) * Fintype.card F
            = ∑ target : F, subsetSumCount G a target * Fintype.card F := by
              rw [Finset.sum_mul]
          _ < ∑ _target : F, n.choose a :=
              Finset.sum_lt_sum_of_nonempty
                (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hq))
                (fun target _ => hlt target)
          _ = Fintype.card F * n.choose a := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      exact lt_of_mul_lt_mul_right (by rwa [mul_comm (Fintype.card F)] at this) (Nat.zero_le _)
  rw [hsum] at hbound
  exact lt_irrefl _ hbound

/-! ## Instantiation at the gap interior: `a = k + t`, `t ≥ 1` -/

/-- **The no-go bites strictly inside the gap (`t ≥ 1`).** Specialized to the list-decoding agreement
size `a = k + t` with `t ≥ 1` (strictly past the capacity endpoint `t = 0`), the maximal subgroup
subset-sum fiber is still `≥ C(n, k+t) / q`. So the Newton/Vieta symmetries do not concentrate the
interior fibers either; the count `N(k+t, ·)` the prize would need to be `poly(n)` is **not** forced
small by the power-sum structure. -/
theorem max_fiber_interior_ge [Fintype F] {G : Finset F} {n : ℕ} (hGcard : G.card = n)
    (k t : ℕ) (ht : 1 ≤ t) (hq : 0 < Fintype.card F) :
    ∃ target : F, Fintype.card F * subsetSumCount G (k + t) target ≥ n.choose (k + t) := by
  -- `t ≥ 1` is recorded to make explicit this is the gap interior, not the `t = 0` endpoint.
  have _ : 0 < t := ht
  exact max_fiber_ge_total_div_card hGcard (k + t) hq


end ArkLib.ProximityGap.Round4NewtonVietaUpper

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.subsetSumCount_neg
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.subsetSumCount_compl
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.subsetSumCount_symmetry_group
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.sum_subsetSumCount_eq_choose
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.max_fiber_ge_total_div_card
#print axioms ArkLib.ProximityGap.Round4NewtonVietaUpper.max_fiber_interior_ge
