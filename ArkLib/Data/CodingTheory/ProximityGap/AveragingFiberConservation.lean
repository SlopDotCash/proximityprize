/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
ANGLE F — Averaging-crossover hypothesis for the Ethereum Proximity Prize (ABF26, ArkLib #232).

We attack the question of where the list-size threshold δ* lies for smooth-domain
Reed–Solomon codes by formalizing the *averaging lower bound* exactly, as a conservation
law plus a second-moment identity, and stating the sharp hypothesis these support.

Conceptual setup (the "averaging" picture).
  Fix a base index set `ι` of size `n` and a parameter `a` (think `a = k + t`, the support
  size of the codewords we count). Consider all `a`-subsets `S ⊆ ι`. Each such `S` is mapped
  to a `t`-tuple of field elements `Φ S ∈ (Fin t → F)` (think: the `t` "extra evaluation
  constraints" that pin a codeword of an enlarged degree). The *fiber* over a target tuple
  `y` is `{S : Φ S = y}`; its size is the number of `a`-subsets consistent with the
  constraints `y`. The list size at the averaging radius is exactly a max fiber size, and the
  averaging lower bound is `maxList ≥ average = (#a-subsets) / q^t`.

What we prove (all axiom-clean, self-contained over `Mathlib`):

  (1) CONSERVATION LAW (the heart of the averaging bound):
        ∑_{y : Fin t → F} (#fiber over y)  =  (# of a-subsets of ι)  =  C(n, a).
      This is the clean "every a-subset lands in exactly one fiber" identity. Combined with
      the fact that there are exactly `q^t = |F|^t` targets, the *average* fiber size is
      EXACTLY `C(n,a) / q^t`, hence `maxList ≥ C(n,a) / q^t` (a pigeonhole, also proved).

  (2) SECOND-MOMENT / COLLISION IDENTITY:
        ∑_{y} (#fiber over y)²  =  # of *colliding ordered pairs* (S, S') with Φ S = Φ S'.
      This relates the second moment of the fiber distribution to the collision count and is
      what controls how far `maxList` can exceed the `average` (anti-concentration ⇒ max ≈ avg).

  (3) The MAX vs AVERAGE inequalities both directions that these identities yield:
        average ≤ max,   and   q^t · max ≥ ∑ fiber = C(n,a).

THE SHARP HYPOTHESIS (stated as a `Prop`, NOT asserted — we don't claim to prove it):
  δ* = δ_avg := the averaging crossover, iff the fiber distribution is anti-concentrated,
  i.e. maxFiber ≤ Cst · avgFiber. We give the precise `AntiConcentrated` predicate and show
  it is *equivalent* to the averaging bound being tight (max ≈ average up to the constant).

Honest scope: we prove the COMBINATORIAL CONSERVATION + SECOND-MOMENT IDENTITIES exactly, and
the pigeonhole average≤max. We do NOT prove the geometric input that `Φ`-fibers correspond to
RS codewords within radius δ, nor that the field-size corrections vanish, nor that the
anti-concentration hypothesis holds. Those are the open content of the prize. This file
delivers the *exact algebraic backbone* of the averaging lower bound and the precise
hypothesis whose truth would pin δ* = δ_avg.
-/

open Finset BigOperators

namespace AveragingCrossover

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {F : Type*} [Fintype F] [DecidableEq F]

/-- The collection of `a`-element subsets of the full index set `ι`. -/
def aSubsets (a : ℕ) : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powersetCard a

/-- The number of `a`-subsets of `ι` is the binomial coefficient `C(n, a)` where `n = |ι|`. -/
theorem card_aSubsets (a : ℕ) :
    (aSubsets (ι := ι) a).card = (Fintype.card ι).choose a := by
  unfold aSubsets
  rw [Finset.card_powersetCard, Finset.card_univ]

variable (t : ℕ) (Φ : Finset ι → (Fin t → F))

/-- The fiber of `Φ` over a target tuple `y`, restricted to `a`-subsets. -/
def fiber (a : ℕ) (y : Fin t → F) : Finset (Finset ι) :=
  (aSubsets (ι := ι) a).filter (fun S => Φ S = y)

/-- The fiber count over a target. -/
def fiberCount (a : ℕ) (y : Fin t → F) : ℕ := (fiber t Φ a y).card

/-! ### (1) Conservation law -/

/-- **CONSERVATION LAW.** The fibers of `Φ` over all `t`-tuples partition the `a`-subsets, so
the sum of fiber counts equals the total number of `a`-subsets, `C(n, a)`. This is the exact
identity underlying the averaging lower bound: total "mass" is conserved across all targets. -/
theorem sum_fiberCount_eq_choose (a : ℕ) :
    ∑ y : Fin t → F, fiberCount t Φ a y = (Fintype.card ι).choose a := by
  rw [← card_aSubsets (ι := ι) a]
  -- count the a-subsets by fibering over their Φ-image, in the target Finset `univ`
  rw [Finset.card_eq_sum_card_fiberwise
      (f := Φ) (t := (Finset.univ : Finset (Fin t → F)))
      (by intro S _; exact Finset.mem_univ _)]
  rfl

/-- The number of targets is exactly `q^t = |F|^t`. -/
theorem card_targets : (Finset.univ : Finset (Fin t → F)).card = (Fintype.card F) ^ t := by
  rw [Finset.card_univ, Fintype.card_pi_const]

/-! ### (2) Second-moment / collision identity -/

/-- The set of *colliding ordered pairs*: pairs `(S, S')` of `a`-subsets with `Φ S = Φ S'`. -/
def collidingPairs (a : ℕ) : Finset (Finset ι × Finset ι) :=
  (aSubsets (ι := ι) a ×ˢ aSubsets (ι := ι) a).filter (fun p => Φ p.1 = Φ p.2)

/-- **SECOND-MOMENT IDENTITY.** The sum of squared fiber counts equals the number of colliding
ordered pairs `(S, S')` with `Φ S = Φ S'`. This is the collision/second-moment identity that
controls anti-concentration: `∑ fiber² = #collisions`. -/
theorem sum_fiberCount_sq_eq_collisions (a : ℕ) :
    ∑ y : Fin t → F, (fiberCount t Φ a y) ^ 2 = (collidingPairs t Φ a).card := by
  -- A colliding pair lands in exactly one fiber-of-y² block (the block y = Φ S = Φ S').
  -- Count collidingPairs by fibering on the common value Φ p.1.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : Finset ι × Finset ι => Φ p.1)
      (t := (Finset.univ : Finset (Fin t → F)))
      (by intro p _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  -- the block of colliding pairs with common value y is (fiber y) ×ˢ (fiber y)
  rw [pow_two]
  show fiberCount t Φ a y * fiberCount t Φ a y = _
  unfold fiberCount
  rw [← Finset.card_product]
  -- goal: #(fiber ×ˢ fiber) = #(collidingPairs.filter (Φ ·.1 = y))
  apply Finset.card_bij' (fun p _ => p) (fun p _ => p)
  · -- i : fiber ×ˢ fiber → collidingPairs.filter (membership)
    intro p hp
    simp only [fiber, Finset.mem_product, Finset.mem_filter] at hp
    obtain ⟨⟨h1, hy1⟩, ⟨h2, hy2⟩⟩ := hp
    simp only [collidingPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨h1, h2⟩, by rw [hy1, hy2]⟩, hy1⟩
  · -- j : collidingPairs.filter → fiber ×ˢ fiber (membership)
    intro p hp
    simp only [collidingPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨h1, h2⟩, hcol⟩, hy⟩ := hp
    simp only [fiber, Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨h1, hy⟩, ⟨h2, by rw [← hcol]; exact hy⟩⟩
  · intro p _; rfl
  · intro p _; rfl

/-! ### (3) Average ≤ Max (pigeonhole), via the conservation law -/

/-- The maximum fiber size over all targets. -/
noncomputable def maxFiber (a : ℕ) : ℕ :=
  Finset.sup (Finset.univ : Finset (Fin t → F)) (fun y => fiberCount t Φ a y)

/-- **AVERAGING LOWER BOUND (max form).** Since the fibers sum to `C(n,a)` over `q^t` targets,
the maximum fiber is at least the average: `C(n,a) ≤ q^t · maxFiber`. Equivalently
`maxFiber ≥ C(n,a) / q^t`. This is the averaging lower bound on the list size. -/
theorem qt_mul_maxFiber_ge_choose (a : ℕ) [Nonempty (Fin t → F)] :
    (Fintype.card ι).choose a ≤ (Fintype.card F) ^ t * maxFiber t Φ a := by
  rw [← sum_fiberCount_eq_choose t Φ a, ← card_targets t (F := F)]
  -- ∑_y fiberCount y ≤ (#targets) * sup fiberCount
  calc ∑ y : Fin t → F, fiberCount t Φ a y
      ≤ ∑ _y : Fin t → F, maxFiber t Φ a := by
        apply Finset.sum_le_sum
        intro y _
        exact Finset.le_sup (f := fun y => fiberCount t Φ a y) (Finset.mem_univ y)
    _ = (Finset.univ : Finset (Fin t → F)).card * maxFiber t Φ a := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-! ### The sharp hypothesis (stated, not asserted) -/

/-- The fiber distribution is `C`-**anti-concentrated** if the maximum fiber is at most `C`
times the average fiber `C(n,a)/q^t`, i.e. `q^t · maxFiber ≤ C · C(n,a)`. When the multiplier
`C` is field-independent (a constant), the averaging lower bound is *tight* and `maxFiber` is
pinned to the average up to that constant. -/
def AntiConcentrated (a : ℕ) (C : ℕ) : Prop :=
  (Fintype.card F) ^ t * maxFiber t Φ a ≤ C * (Fintype.card ι).choose a

/-- **THE SHARP HYPOTHESIS, made precise.** Anti-concentration (with constant `C`) is
*equivalent* to the two-sided pinning `C(n,a) ≤ q^t · maxFiber ≤ C · C(n,a)`. Hence under
anti-concentration, `maxFiber` equals the average `C(n,a)/q^t` up to the field-independent
factor `C`. The prize hypothesis "δ* = δ_avg" is exactly: for the RS-geometric `Φ`, the fiber
is anti-concentrated with a `C` that is `poly`/`2^o(λ)` (not `q^Ω(1)`). -/
theorem antiConcentrated_iff_pinned (a : ℕ) (C : ℕ) [Nonempty (Fin t → F)] :
    AntiConcentrated t Φ a C ↔
      ((Fintype.card ι).choose a ≤ (Fintype.card F) ^ t * maxFiber t Φ a ∧
       (Fintype.card F) ^ t * maxFiber t Φ a ≤ C * (Fintype.card ι).choose a) := by
  constructor
  · intro h
    exact ⟨qt_mul_maxFiber_ge_choose t Φ a, h⟩
  · intro h
    exact h.2

/-! ### Sanity: the identities are non-vacuous (a worked instance). -/

section Sanity
/-- With `t = 0` there is a single target (the empty tuple), so the unique fiber is the whole
set of `a`-subsets, fiber count `= C(n,a)`, and the conservation law reads `C(n,a) = C(n,a)`. -/
example (a : ℕ) (Φ₀ : Finset ι → (Fin 0 → F)) :
    ∑ y : Fin 0 → F, fiberCount 0 Φ₀ a y = (Fintype.card ι).choose a :=
  sum_fiberCount_eq_choose 0 Φ₀ a

/-- The collision count is at least `C(n,a)` (every subset collides with itself), confirming the
second-moment identity is not secretly counting zero. -/
example (a : ℕ) :
    ∑ y : Fin t → F, (fiberCount t Φ a y) ^ 2 ≥ (Fintype.card ι).choose a := by
  rw [sum_fiberCount_sq_eq_collisions]
  -- diagonal pairs (S,S) inject into collidingPairs, and there are C(n,a) of them
  rw [← card_aSubsets (ι := ι) a]
  apply Finset.card_le_card_of_injOn (fun S => (S, S))
  · intro S hS
    simp only [Finset.mem_coe] at hS ⊢
    simp only [collidingPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hS, hS⟩, trivial⟩
  · intro S _ S' _ h
    exact (Prod.ext_iff.mp h).1
end Sanity

end AveragingCrossover

#print axioms AveragingCrossover.sum_fiberCount_eq_choose
#print axioms AveragingCrossover.sum_fiberCount_sq_eq_collisions
#print axioms AveragingCrossover.qt_mul_maxFiber_ge_choose
#print axioms AveragingCrossover.antiConcentrated_iff_pinned
