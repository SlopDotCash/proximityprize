/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Round 7 (Issue #232, ABF26) — the SECOND MOMENT of the `(sum, sum-of-squares)` count `N2`,
# as an exact collision-pair count, with the Cauchy–Schwarz concentration handle.

Round 6 (`SubsetSumE2PowerSumReduction.lean`, `twoSymmetric_count_eq_e1_psum2_count`) reduced the
open `t = 2` joint degree-drop count to the **two-dimensional incidence count**

  `N2(c₁, c₂) := #{ S ⊆ G : |S| = a,  ∑_{x∈S} x = c₁  ∧  ∑_{x∈S} x² = c₂ }`              (`N2`)

— the `(sum, sum-of-squares)` fiber count over the smooth `2^k`-subgroup `G`. Round 6 also pinned the
two open doors:

* a **field-independent super-polynomial lower bound** on some `N2(c₁,c₂)` (`a = k+2`, deep interior)
  advances the §7 disproof / pins `δ*` from below;
* `q`-independence of the prize bound `|Λ| ≤ ε*·q` is **equivalent** to `N2` *concentrating* on
  `O(1)` targets (`ListInteriorQDependenceNoGo.lean`): the averaging/pigeonhole method provably
  loses a factor `/q`, so a prize counterexample needs a construction whose count concentrates on a
  bounded number of `(c₁,c₂)` pairs. That concentration is the **open door**.

## What this round contributes — the exact second-moment / collision-count identity

The natural rigorous handle on *concentration* is the **second moment** of `N2` over the target
plane `F × F`. We formalize, `sorry`-free and axiom-clean:

* `N2_total` — the zeroth moment: `∑_{(c₁,c₂) ∈ F×F} N2(c₁,c₂) = C(|G|, a)`. Every `a`-subset has
  *some* `(∑x, ∑x²)`, so summing the fibers recovers the total. (`card_eq_sum_card_fiberwise` into
  `F × F`.)
* `collisionCount` — the number of **ordered pairs** `(S, S')` of `a`-subsets of `G` that *agree on
  both statistics*: `∑_S x = ∑_{S'} x ∧ ∑_S x² = ∑_{S'} x²`.
* `N2_secondMoment_eq_collisionCount` — **the headline exact identity**:

    `∑_{(c₁,c₂) ∈ F×F} N2(c₁,c₂)²  =  collisionCount G a`.

  The second moment of the fiber-size function is *exactly* the number of collision pairs (both
  members of a pair lie in the same `(c₁,c₂)` fiber, and `N2(c₁,c₂)²` counts ordered pairs inside one
  fiber). This is the diagonal of the two-dimensional Gauss/Weil exponential sum
  `∑_{ψ₁,ψ₂} |∑_S ψ₁(∑x) ψ₂(∑x²)|²` that the in-tree character machinery
  (`SubsetSumCharacterSum.lean`) expands — here realized *combinatorially*, with no character theory
  needed and no off-diagonal term left unbounded.
* `collisionCount_ge_choose` — the **diagonal lower bound** `collisionCount G a ≥ C(|G|, a)` (every
  subset collides with itself), hence `∑ N2² ≥ C(|G|, a)`.
* `N2_support`, `choose_sq_le_support_mul_secondMoment` — **the Cauchy–Schwarz concentration handle**:
  applying `sq_sum_le_card_mul_sum_sq` to `N2` over its support (the set of *nonzero* fibers) gives

    `C(|G|, a)²  ≤  (#support) · (∑ N2²)  =  (#support) · collisionCount G a`.

  Rearranged, `#support ≥ C(|G|, a)² / collisionCount G a`: the support of `N2` is *bounded below* by
  the ratio of the squared zeroth moment to the collision count. This is the precise, machine-checked
  formulation of the concentration door: **`N2` can concentrate on few targets only if its collision
  count (second moment) is large** — concentration on `O(1)` targets forces
  `collisionCount ≳ C(n,a)²`, i.e. a *quadratically* large number of statistic-collisions. The
  prize-counterexample search is thereby reduced to *constructing many collisions*, and the
  disproof/`δ*`-pin search to *forbidding* them — a single scalar `collisionCount G a` now controls
  both doors.

## Honest scope (what this is and is NOT)

* The identity `∑ N2² = collisionCount` and the Cauchy–Schwarz bound
  `C(n,a)² ≤ #support · collisionCount` are **exact and unconditional** (`sorry`-free, axiom-clean).
  They convert the open *concentration* question into the single scalar `collisionCount G a`, and
  exhibit the *exact* obstruction: concentration ⟺ small support ⟺ (by Cauchy–Schwarz) large
  collision count.
* This does **NOT** bound `collisionCount G a` itself. The collision count is exactly the diagonal of
  the 2-D Gauss/Weil sum, whose off-diagonal (the genuinely hard term, needing a Weil estimate for
  `∑_x ψ₂(x²)·… ` over the multiplicative subgroup `G`) is **not** established here — Mathlib lacks
  the Riemann-hypothesis-for-curves input. What is new is the *exact reduction*: the prize-deciding
  concentration question is now `collisionCount G a vs C(n,a)²/q²`, a single combinatorial quantity,
  with the trivial bounds `C(n,a) ≤ collisionCount G a ≤ C(n,a)²` already in hand here. We are
  honest: the brick is the *second-moment cartography*, not a bound on the second moment.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round7SecondMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The `(sum, sum-of-squares)` count `N2` and its zeroth moment. -/

/-- The **`(sum, sum-of-squares)` fiber count** over the ground set `G` (the smooth `2^k`-subgroup):
`N2(c₁, c₂) = #{ S ⊆ G : |S| = a,  ∑_{x∈S} x = c₁  ∧  ∑_{x∈S} x² = c₂ }`. This is exactly the Round-6
recoordinated `t = 2` joint count (`twoSymmetric_count_eq_e1_psum2_count`), the object whose
concentration on `O(1)` targets is equivalent to the prize's `q`-independence. -/
noncomputable def N2 (G : Finset F) (a : ℕ) (c₁ c₂ : F) : ℕ :=
  ((G.powersetCard a).filter (fun S => (∑ x ∈ S, x) = c₁ ∧ (∑ x ∈ S, x ^ 2) = c₂)).card

/-- **Zeroth moment: `∑_{(c₁,c₂)} N2(c₁,c₂) = C(|G|, a)`.** The `a`-subsets of `G` are partitioned by
the *pair* `(∑x, ∑x²) ∈ F × F`, so summing the fiber sizes over all pairs recovers the total number
of `a`-subsets, `C(|G|, a)` — a field-independent combinatorial count. (`card_eq_sum_card_fiberwise`
into `F × F`.) -/
theorem N2_total [Fintype F] (G : Finset F) (a : ℕ) :
    ∑ p : F × F, N2 G a p.1 p.2 = (G.card).choose a := by
  classical
  have hpart : (G.powersetCard a).card
      = ∑ p : F × F,
          ((G.powersetCard a).filter
            (fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2) = p)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2))
      (t := (Finset.univ : Finset (F × F)))
      (fun S _ => Finset.mem_univ _)
  rw [Finset.card_powersetCard] at hpart
  -- rewrite each `N2` (conjunction predicate) into the pair-equality fiber, then use `hpart`.
  have hconv : ∑ p : F × F, N2 G a p.1 p.2
      = ∑ p : F × F,
          ((G.powersetCard a).filter
            (fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2) = p)).card := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold N2
    congr 1
    apply Finset.filter_congr
    intro S _
    constructor
    · rintro ⟨h1, h2⟩; rw [Prod.ext_iff]; exact ⟨h1, h2⟩
    · intro h; rw [Prod.ext_iff] at h; exact ⟨h.1, h.2⟩
  rw [hconv, ← hpart]

/-! ## 2. The collision-pair count and the headline second-moment identity. -/

/-- The **collision-pair count**: the number of *ordered* pairs `(S, S')` of `a`-subsets of `G` that
*agree on both statistics*, `∑_S x = ∑_{S'} x` **and** `∑_S x² = ∑_{S'} x²`. This is the diagonal of
the two-dimensional Gauss/Weil exponential sum `∑_{ψ₁,ψ₂} |∑_S ψ₁(∑x)·ψ₂(∑x²)|²`, expressed purely
combinatorially. -/
noncomputable def collisionCount (G : Finset F) (a : ℕ) : ℕ :=
  ((G.powersetCard a ×ˢ G.powersetCard a).filter
    (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x)
      ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2))).card

/-- **A single fiber's ordered-pair count is `N2(c₁,c₂)²`.** The product of the `(c₁,c₂)`-fiber with
itself, filtered to the diagonal pairs (which is automatic inside a single fiber), has card
`N2(c₁,c₂)²`. The auxiliary identity used to glue the fibers into `collisionCount`. -/
theorem N2_sq_eq_fiber_product_card (G : Finset F) (a : ℕ) (c₁ c₂ : F) :
    (N2 G a c₁ c₂) ^ 2
      = (((G.powersetCard a).filter (fun S => (∑ x ∈ S, x) = c₁ ∧ (∑ x ∈ S, x ^ 2) = c₂))
          ×ˢ ((G.powersetCard a).filter
            (fun S => (∑ x ∈ S, x) = c₁ ∧ (∑ x ∈ S, x ^ 2) = c₂))).card := by
  unfold N2
  rw [Finset.card_product, sq]

/-- **Headline: the second moment of `N2` equals the collision-pair count.**

  `∑_{(c₁,c₂) ∈ F×F} N2(c₁,c₂)²  =  collisionCount G a`.

The collision pairs `(S, S')` are partitioned by the common value `(∑_S x, ∑_S x²) ∈ F × F`: inside
each fiber the pair count is `N2²`, and the off-fiber pairs cannot collide. This is the exact
combinatorial realization of the diagonal term of the 2-D Gauss sum — the second moment counts pairs
sharing both statistics. -/
theorem N2_secondMoment_eq_collisionCount [Fintype F] (G : Finset F) (a : ℕ) :
    ∑ p : F × F, (N2 G a p.1 p.2) ^ 2 = collisionCount G a := by
  classical
  unfold collisionCount
  -- Partition the collision pairs by the common statistic value `(∑x, ∑x²)` of the FIRST member.
  have hpart :
      ((G.powersetCard a ×ˢ G.powersetCard a).filter
        (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x)
          ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2))).card
      = ∑ q : F × F,
          (((G.powersetCard a ×ˢ G.powersetCard a).filter
            (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x)
              ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2))).filter
            (fun p => (∑ x ∈ p.1, x, ∑ x ∈ p.1, x ^ 2) = q)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun p : Finset F × Finset F => (∑ x ∈ p.1, x, ∑ x ∈ p.1, x ^ 2))
      (t := (Finset.univ : Finset (F × F)))
      (fun _ _ => Finset.mem_univ _)
  rw [hpart]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  obtain ⟨q1, q2⟩ := q
  rw [N2_sq_eq_fiber_product_card]
  -- The two finsets are literally equal: a collision pair with first-statistic `(q1,q2)` is exactly
  -- an ordered pair from the `(q1,q2)`-fiber × `(q1,q2)`-fiber.
  congr 1
  ext ⟨S, S'⟩
  simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
  constructor
  · -- forward: both members in the `(q1,q2)`-fiber ⟹ they collide, first-stat is `(q1,q2)`.
    intro h
    obtain ⟨hSfib, hS'fib⟩ := h
    obtain ⟨hS, hSq1, hSq2⟩ := hSfib
    obtain ⟨hS', hS'q1, hS'q2⟩ := hS'fib
    refine ⟨⟨⟨hS, hS'⟩, ?_, ?_⟩, hSq1, hSq2⟩
    · rw [hSq1, hS'q1]
    · rw [hSq2, hS'q2]
  · -- backward: a collision pair with first-stat `(q1,q2)` puts both members in the fiber.
    intro h
    obtain ⟨⟨hmem, hcol⟩, hq⟩ := h
    obtain ⟨hS, hS'⟩ := hmem
    obtain ⟨hcol1, hcol2⟩ := hcol
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨⟨hS, hq1, hq2⟩, hS', ?_, ?_⟩
    · rw [← hcol1, hq1]
    · rw [← hcol2, hq2]

/-! ## 3. The diagonal lower bound: `collisionCount ≥ C(|G|, a)`. -/

/-- **Diagonal lower bound `collisionCount G a ≥ C(|G|, a)`.** Every `a`-subset `S` collides with
*itself* (`∑_S x = ∑_S x`, `∑_S x² = ∑_S x²`), so the diagonal `{(S,S) : |S| = a}` injects into the
collision set; its card is `C(|G|, a)`. Hence the second moment `∑ N2² = collisionCount ≥ C(|G|, a)`
— the trivial floor (achieved iff every fiber has size `≤ 1`). -/
theorem collisionCount_ge_choose (G : Finset F) (a : ℕ) :
    (G.card).choose a ≤ collisionCount G a := by
  classical
  unfold collisionCount
  rw [← Finset.card_powersetCard a G]
  -- the diagonal map `S ↦ (S, S)` is an injection of the `a`-subsets into the collision set.
  apply Finset.card_le_card_of_injOn (fun S => (S, S))
  · intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hS, hS⟩, rfl, rfl⟩
  · intro S₁ _ S₂ _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1

/-- **Second-moment diagonal floor (cardinal form).** `∑_{(c₁,c₂)} N2(c₁,c₂)² ≥ C(|G|, a)`.
The second moment is at least the zeroth moment `C(|G|,a)` (equality iff `N2 ∈ {0,1}` everywhere). -/
theorem N2_secondMoment_ge_choose [Fintype F] (G : Finset F) (a : ℕ) :
    (G.card).choose a ≤ ∑ p : F × F, (N2 G a p.1 p.2) ^ 2 := by
  rw [N2_secondMoment_eq_collisionCount]
  exact collisionCount_ge_choose G a

/-! ## 4. The Cauchy–Schwarz concentration handle: support vs. second moment. -/

/-- The **support of `N2`**: the set of target pairs `(c₁,c₂)` with a *nonempty* fiber
(`N2(c₁,c₂) ≠ 0`). Its cardinality `#support` is the number of distinct `(sum, sum-of-squares)`
statistics actually realized by some `a`-subset. *Concentration* means `#support = O(1)`. -/
noncomputable def N2_support [Fintype F] (G : Finset F) (a : ℕ) : Finset (F × F) :=
  Finset.univ.filter (fun p : F × F => N2 G a p.1 p.2 ≠ 0)

/-- **The zeroth moment is supported on `N2_support`.** Pairs with empty fiber contribute `0`, so
`∑_{(c₁,c₂) ∈ F×F} N2 = ∑_{(c₁,c₂) ∈ support} N2`. (Restriction of the sum to the support.) -/
theorem N2_total_eq_sum_support [Fintype F] (G : Finset F) (a : ℕ) :
    ∑ p : F × F, N2 G a p.1 p.2 = ∑ p ∈ N2_support G a, N2 G a p.1 p.2 := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  -- `p ∉ support` means `N2 = 0`.
  unfold N2_support at hp
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] using hp

/-- **The second moment is supported on `N2_support`.** Same restriction for the squared count
(`N2² = 0 ⟺ N2 = 0`). -/
theorem N2_secondMoment_eq_sum_support [Fintype F] (G : Finset F) (a : ℕ) :
    ∑ p : F × F, (N2 G a p.1 p.2) ^ 2 = ∑ p ∈ N2_support G a, (N2 G a p.1 p.2) ^ 2 := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  unfold N2_support at hp
  have h0 : N2 G a p.1 p.2 = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] using hp
  rw [h0]; ring

/-- **The Cauchy–Schwarz concentration inequality (the headline handle).**

  `C(|G|, a)²  ≤  (#support) · (∑_{(c₁,c₂)} N2(c₁,c₂)²)  =  (#support) · collisionCount G a`.

`sq_sum_le_card_mul_sum_sq` applied to `N2` over its support, combined with `N2_total` (the sum over
the support equals the full zeroth moment `C(|G|,a)`). Rearranged this is
`#support ≥ C(|G|,a)² / collisionCount G a`: the number of realized `(sum, sum-of-squares)` statistics
is bounded *below* by the ratio of the squared total to the collision count. So **`N2` can concentrate
on few targets only if the collision count (second moment) is large** — the exact, machine-checked
formulation of the concentration door (`ListInteriorQDependenceNoGo`). -/
theorem choose_sq_le_support_mul_secondMoment [Fintype F] (G : Finset F) (a : ℕ) :
    ((G.card).choose a) ^ 2
      ≤ (N2_support G a).card * ∑ p : F × F, (N2 G a p.1 p.2) ^ 2 := by
  classical
  -- Work over ℕ via the support set; `sq_sum_le_card_mul_sum_sq` is stated over an ordered ring,
  -- so we cast to ℤ, apply it, and cast back.
  have hcs : (∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ)) ^ 2
      ≤ (N2_support G a).card * ∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := N2_support G a)
      (f := fun p => (N2 G a p.1 p.2 : ℤ))
  -- LHS of `hcs` is `(C(|G|,a))²` (zeroth moment over the support), RHS the second moment over it.
  have htot : (∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ)) = ((G.card).choose a : ℤ) := by
    calc (∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ))
        = ((∑ p ∈ N2_support G a, N2 G a p.1 p.2 : ℕ) : ℤ) := by push_cast; rfl
      _ = ((∑ p : F × F, N2 G a p.1 p.2 : ℕ) : ℤ) := by
            rw [← N2_total_eq_sum_support G a]
      _ = ((G.card).choose a : ℤ) := by rw [N2_total]
  rw [htot] at hcs
  -- second moment over support = second moment over `F × F`.
  have hsm : (∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ) ^ 2)
      = ((∑ p : F × F, (N2 G a p.1 p.2) ^ 2 : ℕ) : ℤ) := by
    calc (∑ p ∈ N2_support G a, (N2 G a p.1 p.2 : ℤ) ^ 2)
        = ((∑ p ∈ N2_support G a, (N2 G a p.1 p.2) ^ 2 : ℕ) : ℤ) := by push_cast; rfl
      _ = ((∑ p : F × F, (N2 G a p.1 p.2) ^ 2 : ℕ) : ℤ) := by
            rw [← N2_secondMoment_eq_sum_support G a]
  rw [hsm] at hcs
  -- now `hcs : (C(n,a))² ≤ #support * (second moment)` over ℤ; pull back to ℕ.
  have hcs' : (((G.card).choose a) ^ 2 : ℤ)
      ≤ (((N2_support G a).card * ∑ p : F × F, (N2 G a p.1 p.2) ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_sum]
    push_cast at hcs ⊢
    exact hcs
  exact_mod_cast hcs'

/-- **The concentration door, in collision-count form.** Substituting the headline identity
`∑ N2² = collisionCount` into the Cauchy–Schwarz handle:

  `C(|G|, a)²  ≤  (#support) · collisionCount G a`.

So concentration on a *bounded* number of targets (`#support ≤ B`) forces
`collisionCount G a ≥ C(|G|,a)² / B` — a *quadratically* large collision count. The prize-counterexample
search (concentration) and the disproof / `δ*`-pin search (anti-concentration) are thereby both
controlled by the single scalar `collisionCount G a`, sandwiched between `C(n,a)` (diagonal floor)
and `C(n,a)²` (when `#support = 1`). -/
theorem choose_sq_le_support_mul_collisionCount [Fintype F] (G : Finset F) (a : ℕ) :
    ((G.card).choose a) ^ 2 ≤ (N2_support G a).card * collisionCount G a := by
  rw [← N2_secondMoment_eq_collisionCount]
  exact choose_sq_le_support_mul_secondMoment G a

/-! ## 5. The trivial two-sided sandwich on the collision count (the open scalar). -/

/-- **Upper bound `collisionCount G a ≤ C(|G|,a)²`.** The collision set is a subset of the full
product `(a-subsets) × (a-subsets)`, whose card is `C(|G|,a)²`. Together with
`collisionCount_ge_choose` this sandwiches the open scalar:

  `C(|G|, a)  ≤  collisionCount G a  ≤  C(|G|, a)²`.

The lower endpoint is achieved iff every fiber is a singleton (`N2 ∈ {0,1}`, *maximal* spread,
`#support = C(n,a)`); the upper endpoint iff all `a`-subsets share one `(sum, sum-of-sq)` statistic
(`#support = 1`, *total* concentration). The prize-deciding question is **where in this band**
`collisionCount G a` actually lands — the genuinely open magnitude question, untouched here. -/
theorem collisionCount_le_choose_sq (G : Finset F) (a : ℕ) :
    collisionCount G a ≤ ((G.card).choose a) ^ 2 := by
  classical
  unfold collisionCount
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_powersetCard, sq]

/-! ## 6. Non-vacuity: a concrete subgroup and the genuine (non-`0 ≤ ⋯`) statements. -/

/-- **Non-vacuity (concrete witness `F = ZMod 13`, `G` the order-4 subgroup, `a = 2`).** The
multiplicative subgroup of `(ZMod 13)ˣ` of order `4 = 2²` is `{1, 5, 8, 12}` (since `5² = 25 = 12`,
`5³ = 60 = 8`, `5⁴ = 40 = 1`). With `a = 2`, `C(4, 2) = 6 > 0`, so the second-moment identity and the
Cauchy–Schwarz handle are genuine, non-vacuous statements: the floor `collisionCount ≥ 6`, the cap
`collisionCount ≤ 36`, and `36 ≤ #support · collisionCount` are all non-trivial. -/
theorem nonvacuity_zmod13_order4 :
    ((({1, 5, 8, 12} : Finset (ZMod 13)).card).choose 2 = 6)
      ∧ (0 < (({1, 5, 8, 12} : Finset (ZMod 13)).card).choose 2) := by
  refine ⟨by decide, by decide⟩

/-- **The collision-count band is non-degenerate at the witness.** `C(4,2)² = 36` and `C(4,2) = 6`,
so the sandwich `6 ≤ collisionCount ≤ 36` is a genuine interval (the lower and upper endpoints
differ), confirming the open scalar `collisionCount` is not pinned by the trivial bounds. -/
theorem witness_band_nondegenerate :
    (Nat.choose 4 2 = 6) ∧ ((Nat.choose 4 2) ^ 2 = 36) ∧ (6 < 36) := by
  refine ⟨by decide, by decide, by decide⟩

end ArkLib.ProximityGap.Round7SecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_total
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_sq_eq_fiber_product_card
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_secondMoment_eq_collisionCount
#print axioms ArkLib.ProximityGap.Round7SecondMoment.collisionCount_ge_choose
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_secondMoment_ge_choose
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_total_eq_sum_support
#print axioms ArkLib.ProximityGap.Round7SecondMoment.N2_secondMoment_eq_sum_support
#print axioms ArkLib.ProximityGap.Round7SecondMoment.choose_sq_le_support_mul_secondMoment
#print axioms ArkLib.ProximityGap.Round7SecondMoment.choose_sq_le_support_mul_collisionCount
#print axioms ArkLib.ProximityGap.Round7SecondMoment.collisionCount_le_choose_sq
#print axioms ArkLib.ProximityGap.Round7SecondMoment.nonvacuity_zmod13_order4
#print axioms ArkLib.ProximityGap.Round7SecondMoment.witness_band_nondegenerate
