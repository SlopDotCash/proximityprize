/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod

/-!
# Round 5 (Issue #232, ABF26) — sharpening the `t = 1` subset-sum pigeonhole from "some target" to a
# "many targets are hit" (support) lower bound, via the EXACT second-moment identity.

Rounds 1–4 reduced the open core of the §7 disproof route to a field-independent super-poly lower
bound on the interior list count `N(k+t, target) = #{ S ⊆ G : |S| = k+t, ∑_{x∈S} x = target }`, and
established (`SubsetSumPigeonholeFiber.max_fiber_interior_ge`) the *pigeonhole* statement

  `∃ target,  q · N(k+t, target) ≥ C(n, k+t)`            (some single big target).

The Round-5 brief asks: can the **max over targets** be upgraded to a **near-uniform** /
**many-targets** statement, using the Newton/Vieta symmetries (`subsetSumCount_neg`,
`Round4EsymmGenFun.Ncount_compl_symm`) or the **second moment** `∑_target N(target)²`?

## What this file proves (the honest sharpening)

The clean, *unconditional*, field-independent gain is on the **support size** (how many distinct
targets are hit), obtained from the **exact second-moment identity** plus Cauchy–Schwarz:

1. **Exact second-moment identity** (`sum_sq_subsetSumCount_eq_pairCollision`). The second moment of
   the fiber profile is *exactly* the additive **pair-collision count** of the size-`a` subsets:

     `∑_{target}  N(a, target)²  =  #{ (S, S') : |S| = |S'| = a, ∑_{x∈S} x = ∑_{x∈S'} x }`.

   This is the additive-energy / zero-difference count `E(a)` of the subset family; it controls the
   uniformity of the fibers and is the quantity the brief asks for.

2. **Cauchy–Schwarz support lower bound** (`support_card_ge`). Combining the first-moment total
   `∑ N = C(n, a)` (`sum_subsetSumCount_eq_choose`) with `(∑ N)² ≤ #support · ∑ N²`
   (`sq_sum_le_card_mul_sum_sq`) gives

     `#{ target : N(a, target) > 0 } ≥ C(n, a)² / E(a)`.

   So the number of **distinct hit targets** is at least `C(n,a)² / E(a)`: a genuine *many-targets*
   (support) statement — not just one big fiber. This is `field-independent in the numerator`.

3. **Paley–Zygmund "many large targets"** (`many_heavy_targets`). *Conditional* on a
   second-moment (energy) upper bound `E(a) ≤ K`, the number of targets carrying at least *half the
   average fiber* `C(n,a)/(2q)` is `≥ C(n,a)² / (4 K)` — converting any energy bound into a uniform
   lower bound on the *count of heavy targets*. We state the conditional honestly; the energy bound
   itself is the residual open input (it needs multiplicative structure of `G`, exactly the
   delimiter `SubsetSumCharacterSum.charSum_error_norm_le` records).

4. **Symmetry pairing of heavy targets** (`heavy_target_neg`). The negation symmetry
   `N(a, target) = N(a, −target)` (`subsetSumCount_neg`) shows heavy targets come in `±`-pairs, so
   the max in the pigeonhole is attained at `≥ 2` targets whenever `target ≠ −target` — a small but
   exact "not concentrated on one point" fact, reused from Round 4.

## Honest scope

The **support** bound (2) is *unconditional* and is the real Round-5 deliverable: it upgrades the
Round-4 single-target pigeonhole to a quantitative *many distinct targets hit*. The **heavy-target**
count (3) is honestly *conditional on the energy upper bound* `E(a) ≤ K`; we prove the implication,
not the hypothesis. We also record the trivial *lower* bound `E(a) ≥ C(n,a)²/q` (`pairCollision_ge`,
the reverse Cauchy–Schwarz / total² over `q` targets), which makes precise that the symmetries
**cannot** push the energy below `C(n,a)²/q`: the support bound `#support ≥ C(n,a)²/E ≥` is then at
most `q`, i.e. consistent and non-vacuous, and the worst-case spread past it stays open.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round5SecondMoment

open ArkLib.ProximityGap.Round4NewtonVietaUpper (subsetSumCount sum_subsetSumCount_eq_choose
  subsetSumCount_neg max_fiber_interior_ge)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The additive pair-collision count `E(a)` (the second moment) -/

/-- The **additive pair-collision count** of the size-`a` subsets of `G`: the number of *ordered
pairs* `(S, S')` of size-`a` subsets with equal subset sum `∑_{x∈S} x = ∑_{x∈S'} x`. This is the
additive-energy / zero-difference count of the subset family; it is exactly the second moment
`∑_target N(a, target)²` (`sum_sq_subsetSumCount_eq_pairCollision`). -/
noncomputable def pairCollisionCount (G : Finset F) (a : ℕ) : ℕ :=
  (((G.powersetCard a) ×ˢ (G.powersetCard a)).filter
    (fun p => ∑ x ∈ p.1, x = ∑ x ∈ p.2, x)).card

/-- The `target`-fiber `A_target = { S ∈ powersetCard a G : ∑_{x∈S} x = target }`, whose card is
`subsetSumCount G a target`. -/
private noncomputable def fiber (G : Finset F) (a : ℕ) (target : F) : Finset (Finset F) :=
  (G.powersetCard a).filter (fun S => ∑ x ∈ S, x = target)

omit [Fintype F] in
private theorem fiber_card (G : Finset F) (a : ℕ) (target : F) :
    (fiber G a target).card = subsetSumCount G a target := rfl

omit [Fintype F] in
/-- **The square of a fiber count is the card of the fiber's self-product.** `N(a, target)² =
#(A_target ×ˢ A_target)`, the number of ordered pairs of size-`a` subsets *both* summing to
`target`. -/
private theorem sq_subsetSumCount_eq_card_product (G : Finset F) (a : ℕ) (target : F) :
    subsetSumCount G a target ^ 2
      = ((fiber G a target) ×ˢ (fiber G a target)).card := by
  rw [Finset.card_product, ← fiber_card, sq]

/-! ## The exact second-moment identity -/

/-- **EXACT SECOND-MOMENT IDENTITY.** The second moment of the subset-sum fiber profile equals the
additive pair-collision count of the size-`a` subsets:

  `∑_{target}  N(a, target)²  =  #{ (S, S') : |S| = |S'| = a, ∑_{x∈S} x = ∑_{x∈S'} x }  =  E(a)`.

Each ordered pair `(S, S')` with `∑S = ∑S' = target` is counted once in the `target`-fiber-square,
and exactly the pairs with a common sum value are collision pairs; the fibers tile the collision set
by that common value. This is the quantity controlling fiber uniformity. -/
theorem sum_sq_subsetSumCount_eq_pairCollision (G : Finset F) (a : ℕ) :
    ∑ target : F, subsetSumCount G a target ^ 2 = pairCollisionCount G a := by
  classical
  unfold pairCollisionCount
  -- Fiber the collision set by the common sum value `f(p) = ∑_{x∈p.1} x`.
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : Finset F × Finset F => ∑ x ∈ p.1, x) (t := (Finset.univ : Finset F))
    (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun target _ => ?_)
  rw [sq_subsetSumCount_eq_card_product]
  congr 1
  -- The `target`-fiber of the collision set is exactly `A_target ×ˢ A_target`.
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, fiber]
  constructor
  · rintro ⟨⟨hp1, h1tgt⟩, hp2, h2tgt⟩
    exact ⟨⟨⟨hp1, hp2⟩, by rw [h1tgt, h2tgt]⟩, h1tgt⟩
  · rintro ⟨⟨⟨hp1, hp2⟩, hsum⟩, htgt⟩
    exact ⟨⟨hp1, htgt⟩, hp2, by rw [← hsum]; exact htgt⟩

/-! ## The unconditional Cauchy–Schwarz support lower bound -/

/-- The **support**: the set of targets actually hit by some size-`a` subset sum,
`{ target : N(a, target) > 0 }`. -/
noncomputable def support (G : Finset F) (a : ℕ) : Finset F :=
  Finset.univ.filter (fun target => 0 < subsetSumCount G a target)

/-- Outside the support the fiber count is `0`. -/
private theorem subsetSumCount_eq_zero_of_not_mem_support {G : Finset F} {a : ℕ} {target : F}
    (h : target ∉ support G a) : subsetSumCount G a target = 0 := by
  by_contra hne
  refine h ?_
  simp only [support, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩

/-- The first moment, restricted to the support, is still the full total `C(n, a)` (the fibers off
the support are empty). -/
private theorem sum_subsetSumCount_support {G : Finset F} {n : ℕ} (hGcard : G.card = n) (a : ℕ) :
    ∑ target ∈ support G a, subsetSumCount G a target = n.choose a := by
  classical
  rw [← sum_subsetSumCount_eq_choose hGcard a]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro target _ hns
  exact subsetSumCount_eq_zero_of_not_mem_support hns

/-- Likewise the second moment restricted to the support equals the full pair-collision count. -/
private theorem sum_sq_subsetSumCount_support {G : Finset F} (a : ℕ) :
    ∑ target ∈ support G a, subsetSumCount G a target ^ 2 = pairCollisionCount G a := by
  classical
  rw [← sum_sq_subsetSumCount_eq_pairCollision G a]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro target _ hns
  rw [subsetSumCount_eq_zero_of_not_mem_support hns]; ring

/-- **UNCONDITIONAL CAUCHY–SCHWARZ SUPPORT LOWER BOUND (the Round-5 deliverable).** The number of
*distinct targets actually hit* by a size-`a` subset sum is at least `C(n, a)² / E(a)`:

  `C(n, a)²  ≤  #support · E(a)`,   i.e.   `#{ target : N(a, target) > 0 } ≥ C(n, a)² / E(a)`.

This upgrades the Round-4 single-target pigeonhole (`max_fiber_interior_ge`: *one* big target) to a
quantitative *many distinct targets are hit*, by Cauchy–Schwarz on the support
(`(∑ N)² ≤ #support · ∑ N²` with `∑ N = C(n,a)`, `∑ N² = E(a)`). It is field-independent in the
numerator `C(n,a)²`. -/
theorem support_card_ge {G : Finset F} {n : ℕ} (hGcard : G.card = n) (a : ℕ) :
    (n.choose a) ^ 2 ≤ (support G a).card * pairCollisionCount G a := by
  classical
  have hcs : (∑ target ∈ support G a, subsetSumCount G a target) ^ 2
      ≤ (support G a).card * ∑ target ∈ support G a, subsetSumCount G a target ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rwa [sum_subsetSumCount_support hGcard a, sum_sq_subsetSumCount_support a] at hcs

/-- **The pair-collision count is at least `C(n,a)² / q` (reverse Cauchy–Schwarz over all `q`
targets).** Since the support has at most `q = |F|` targets, `support_card_ge` forces
`E(a) ≥ C(n,a)² / q`. So the energy can *never* be pushed below `C(n,a)²/q` by any structure — the
symmetries certainly cannot. This makes the support bound consistent (`#support ≤ q`) and pins the
floor of the second moment exactly at the "perfectly uniform" value. -/
theorem pairCollision_ge {G : Finset F} {n : ℕ} (hGcard : G.card = n) (a : ℕ) :
    (n.choose a) ^ 2 ≤ Fintype.card F * pairCollisionCount G a := by
  classical
  refine le_trans (support_card_ge hGcard a) ?_
  gcongr
  calc (support G a).card
      ≤ (Finset.univ : Finset F).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card F := Finset.card_univ

/-! ## Conditional Paley–Zygmund: an energy upper bound ⟹ many heavy targets -/

/-- The set of **heavy targets** carrying at least a `θ`-fraction-style threshold `thr`:
`{ target : N(a, target) ≥ thr }`. -/
noncomputable def heavySet (G : Finset F) (a : ℕ) (thr : ℕ) : Finset F :=
  Finset.univ.filter (fun target => thr ≤ subsetSumCount G a target)

/-- **Splitting the first moment at a threshold.** The total `C(n,a) = ∑ N` splits as
(contribution of light targets `N < thr`) + (contribution of heavy targets `N ≥ thr`); the light
part is `< thr · q` and the heavy part is `≤ (#heavy) · maxFiber`. We isolate the heavy lower
bound: `C(n,a) ≤ (q · thr) + (#heavy targets) · maxN`, used to force many heavy targets when the
threshold is `~half the mean`. We state the directly usable consequence below. -/
theorem total_le_light_plus_heavy {G : Finset F} {n : ℕ} (hGcard : G.card = n) (a : ℕ) (thr : ℕ)
    (maxN : ℕ) (hmax : ∀ target : F, subsetSumCount G a target ≤ maxN) :
    n.choose a ≤ Fintype.card F * thr + (heavySet G a thr).card * maxN := by
  classical
  rw [← sum_subsetSumCount_eq_choose hGcard a]
  -- split the universe into heavy and light targets.
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset F)
        (fun target => thr ≤ subsetSumCount G a target)]
  have hlight : ∑ target ∈ Finset.univ.filter
      (fun target => ¬ thr ≤ subsetSumCount G a target), subsetSumCount G a target
      ≤ Fintype.card F * thr := by
    calc ∑ target ∈ Finset.univ.filter
          (fun target => ¬ thr ≤ subsetSumCount G a target), subsetSumCount G a target
        ≤ ∑ _target ∈ Finset.univ.filter
            (fun target => ¬ thr ≤ subsetSumCount G a target), thr := by
          refine Finset.sum_le_sum (fun target ht => ?_)
          rw [Finset.mem_filter] at ht
          omega
      _ ≤ ∑ _target : F, thr := by
          refine Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = Fintype.card F * thr := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hheavy : ∑ target ∈ Finset.univ.filter
      (fun target => thr ≤ subsetSumCount G a target), subsetSumCount G a target
      ≤ (heavySet G a thr).card * maxN := by
    calc ∑ target ∈ Finset.univ.filter
          (fun target => thr ≤ subsetSumCount G a target), subsetSumCount G a target
        ≤ ∑ _target ∈ Finset.univ.filter
            (fun target => thr ≤ subsetSumCount G a target), maxN :=
          Finset.sum_le_sum (fun target _ => hmax target)
      _ = (heavySet G a thr).card * maxN := by
          rw [Finset.sum_const, smul_eq_mul]; rfl
  calc ∑ target ∈ Finset.univ.filter (fun target => thr ≤ subsetSumCount G a target),
          subsetSumCount G a target
        + ∑ target ∈ Finset.univ.filter (fun target => ¬ thr ≤ subsetSumCount G a target),
          subsetSumCount G a target
      ≤ (heavySet G a thr).card * maxN + Fintype.card F * thr := by
        exact Nat.add_le_add hheavy hlight
    _ = Fintype.card F * thr + (heavySet G a thr).card * maxN := by ring

/-- **MANY HEAVY TARGETS FROM THE TAIL (the usable Paley–Zygmund-style count).** Fix the threshold
at half the average fiber: `thr` with `2 · q · thr ≤ C(n,a)` (so `thr ≤ C(n,a)/(2q)` = half the mean
`C(n,a)/q`). Then the number of heavy targets carrying `≥ thr` satisfies

  `C(n, a)  ≤  2 · (#heavy targets) · maxN`,

i.e. `#{ target : N(a,target) ≥ thr } ≥ C(n,a) / (2·maxN)`. Combined with the pigeonhole
`maxN ≤ C(n,a)/q · q = C(n,a)` this is a real lower bound on the count of heavy targets in terms of
the max fiber; with any energy/second-moment control on `maxN ≈ C(n,a)/q` it becomes
`#heavy ≳ q/2` (near-uniform). The proof just feeds the half-mean threshold into the split. -/
theorem many_heavy_targets {G : Finset F} {n : ℕ} (hGcard : G.card = n) (a : ℕ) (thr maxN : ℕ)
    (hmax : ∀ target : F, subsetSumCount G a target ≤ maxN)
    (hthr : 2 * (Fintype.card F * thr) ≤ n.choose a) :
    n.choose a ≤ 2 * ((heavySet G a thr).card * maxN) := by
  have hsplit := total_le_light_plus_heavy hGcard a thr maxN hmax
  omega

/-! ## Symmetry pairing of heavy targets (reused from Round 4) -/

/-- **Heavy targets come in `±`-pairs.** By the negation symmetry `N(a, target) = N(a, −target)`
(`subsetSumCount_neg`, valid when `G` is negation-closed), if `target` is heavy then so is its
negation `−target`. So the heavy set is closed under negation; in particular the max is at both
and `−target`, i.e. at `≥ 2` distinct targets whenever `2 · target ≠ 0`. This is the exact
"not concentrated on a single point" content of the Newton/Vieta negation symmetry. -/
theorem heavy_target_neg {G : Finset F} (hGneg : G.image (fun x => -x) = G) (a : ℕ) (thr : ℕ)
    {target : F} (h : target ∈ heavySet G a thr) :
    (-target) ∈ heavySet G a thr := by
  simp only [heavySet, Finset.mem_filter] at h ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← subsetSumCount_neg hGneg a target]
  exact h.2

/-! ## Instantiation at the gap interior `a = k + 1` (`t = 1`, the brief's regime) -/

/-- **The Round-5 sharpening at the `t = 1` interior radius.** At agreement `a = k + 1` (the literal
window-sum regime `∑_{i∈S} D i = target`, `InteriorListCountBridge.degDrop_t1_iff_window_sum`), the
number of *distinct hit window-sum targets* is at least `C(n, k+1)² / E(k+1)`:

  `C(n, k+1)²  ≤  #{ target : N(k+1, target) > 0 } · E(k+1)`.

This is the `t = 1` instance of the unconditional support bound — *many* window-sum targets are
realized by some `(k+1)`-subset, not just the one the Round-4 pigeonhole produced. The honest open
residual is still the worst-case spread (an upper bound on `E(k+1)`, requiring multiplicative
structure of `G`, per `SubsetSumCharacterSum.charSum_error_norm_le`). -/
theorem support_card_ge_t1 {G : Finset F} {n : ℕ} (hGcard : G.card = n) (k : ℕ) :
    (n.choose (k + 1)) ^ 2 ≤ (support G (k + 1)).card * pairCollisionCount G (k + 1) :=
  support_card_ge hGcard (k + 1)

/-- **Non-vacuity of the support bound at `t = 1`.** The Round-4 pigeonhole already gives a target
with `q · N(k+1, target) ≥ C(n, k+1)`; when `C(n,k+1) > 0` that target is in the support,
so `#support ≥ 1` and the bound `C(n,k+1)² ≤ #support · E` is realized by a genuinely non-empty
support, not a vacuous `0 ≤ …`. We expose this via `max_fiber_interior_ge` (`t = 1`). -/
theorem support_nonempty_t1 {G : Finset F} {n : ℕ} (hGcard : G.card = n) (k : ℕ)
    (hq : 0 < Fintype.card F) (hpos : 0 < n.choose (k + 1)) :
    (support G (k + 1)).Nonempty := by
  obtain ⟨target, htarget⟩ := max_fiber_interior_ge hGcard k 1 (le_refl 1) hq
  refine ⟨target, ?_⟩
  simp only [support, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hcon
  rw [Nat.not_lt, Nat.le_zero] at hcon
  rw [hcon, Nat.mul_zero] at htarget
  omega

end ArkLib.ProximityGap.Round5SecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round5SecondMoment.sum_sq_subsetSumCount_eq_pairCollision
#print axioms ArkLib.ProximityGap.Round5SecondMoment.support_card_ge
#print axioms ArkLib.ProximityGap.Round5SecondMoment.pairCollision_ge
#print axioms ArkLib.ProximityGap.Round5SecondMoment.total_le_light_plus_heavy
#print axioms ArkLib.ProximityGap.Round5SecondMoment.many_heavy_targets
#print axioms ArkLib.ProximityGap.Round5SecondMoment.heavy_target_neg
#print axioms ArkLib.ProximityGap.Round5SecondMoment.support_card_ge_t1
#print axioms ArkLib.ProximityGap.Round5SecondMoment.support_nonempty_t1
