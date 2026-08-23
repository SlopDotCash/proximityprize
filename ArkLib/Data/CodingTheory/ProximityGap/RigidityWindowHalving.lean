/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 26 (Issue #232) — THE WINDOW-HALVING STEP: the full-window rigidity recursion engine

The single recursion step that, iterated `⌈log₂(t+1)⌉` times, proves the full linear-window
rigidity for disjoint families (Step 2 of O46, disjoint case) from Round-25's general `t=1`
theorem. Stated in **power-sum windows** (equivalent to the `e`-window over `CharZero` by Newton),
where the recursion bookkeeping is trivial:

Let `A, B` be disjoint sets of `2N`-th roots (as field elements, with the signed-point encoding
available) with equal power sums `p_1, …, p_t` (`t ≥ 1`). Then:

* **(a)** `p_1(A) = p_1(B)` + Round-25 ⟹ both sets are **antipodally closed** (`x ∈ A ⟹ −x ∈ A`);
* **(b) `odd_psum_vanish`:** for antipodally-closed sets, EVERY odd power sum vanishes
  identically (`x^r + (−x)^r = 0`, the Round-8 ω-engine at `ω = −1`) — the odd window conditions
  are automatic;
* **(c) `even_psum_halves`:** `p_{2l}(A) = 2·p_l(A²)` where `A² = {x² : x ∈ A}` (the pairs
  `{x, −x}` collapse two-to-one onto distinct squares: `squares_card`) — so the equal even-window
  conditions descend EXACTLY to equal `p_1, …, p_{⌊t/2⌋}` of the square sets `A², B²`;
* **(d) `squares_disjoint`:** the square sets are again disjoint (a shared square forces a shared
  point or a shared antipode — both in the sets by closure).

The square sets live in `μ_N` whose half basis `{ζ^{2j}}` inherits independence, so the step
re-applies: after `k = ⌈log₂(t+1)⌉` halvings the window is empty and the iterated structure is
exactly the `2^k`-lift family of Round 22 — **floor = ceiling on the full window, disjoint case**.
This file proves the step's four components; the iteration is statement-juggling over levels.
-/

open Finset

namespace Round26Recursion

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## (b) Odd power sums vanish on antipodally-closed sets -/

/-- An antipodally-closed finset: `x ∈ A ⟹ −x ∈ A`, with `0 ∉ A`. -/
def AntipodallyClosed (A : Finset F) : Prop :=
  (0 : F) ∉ A ∧ ∀ x ∈ A, -x ∈ A

omit [DecidableEq F] in
/-- **Odd power sums vanish identically on antipodally-closed sets** (the Round-8 engine at
`ω = −1`): pairing `x ↔ −x` flips the sign of `x^r` for odd `r`, and is fixed-point-free off `0`
in characteristic ≠ 2. -/
theorem odd_psum_vanish [CharZero F] {A : Finset F} (hA : AntipodallyClosed A)
    {r : ℕ} (hr : Odd r) :
    (∑ x ∈ A, x ^ r) = 0 := by
  obtain ⟨h0, hclosed⟩ := hA
  refine Finset.sum_involution (fun x _ => -x) (fun x _ => ?_) (fun x hx _ => ?_)
    (fun x hx => hclosed x hx) (fun x _ => neg_neg x)
  · -- x^r + (−x)^r = 0 for odd r
    rw [hr.neg_pow]
    ring
  · -- fixed-point-free: −x ≠ x for x ≠ 0
    intro hcontra
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have : (2 : F) * x = 0 := by linear_combination -hcontra
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h two_ne_zero
    · exact hx0 h

/-! ## (c) Even power sums halve to the square set -/

/-- The square set `A² = {x² : x ∈ A}`. -/
def squares (A : Finset F) : Finset F := A.image (fun x => x ^ 2)

/-- On an antipodally-closed set, the squaring map is exactly two-to-one: each fiber is the
antipodal pair `{y, −y}`. -/
theorem squares_fiber {A : Finset F} (hA : AntipodallyClosed A) [CharZero F]
    {x : F} (hx : x ∈ A) :
    A.filter (fun y => y ^ 2 = x ^ 2) = {x, -x} := by
  classical
  obtain ⟨h0, hclosed⟩ := hA
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hyA, hy⟩
    have : (y - x) * (y + x) = 0 := by linear_combination hy
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rintro (rfl | rfl)
    · exact ⟨hx, rfl⟩
    · exact ⟨hclosed x hx, by ring⟩

/-- **The even power sums halve:** for antipodally-closed `A`,
`p_{2l}(A) = 2 · p_l(A²)` — summing `x^{2l}` over `A` counts each square's `l`-th power exactly
twice (the squaring fibers are the antipodal pairs). -/
theorem even_psum_halves [CharZero F] {A : Finset F} (hA : AntipodallyClosed A) (l : ℕ) :
    (∑ x ∈ A, x ^ (2 * l)) = 2 * ∑ y ∈ squares A, y ^ l := by
  classical
  have hrw : (∑ x ∈ A, x ^ (2 * l)) = ∑ x ∈ A, (fun y => y ^ l) ((fun x => x ^ 2) x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp only
    rw [← pow_mul, Nat.mul_comm]
  rw [hrw, Finset.sum_comp (fun y => y ^ l) (fun x => x ^ 2)]
  unfold squares
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hy
  -- the fiber over x² is {x, −x}, of size 2
  have hfib : A.filter (fun z => z ^ 2 = x ^ 2) = {x, -x} := squares_fiber hA hxA
  have hxne : x ≠ -x := by
    intro h
    have hx0 : x ≠ 0 := fun h0 => hA.1 (h0 ▸ hxA)
    have : (2 : F) * x = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero h2
    · exact hx0 h2
  have hcard : (A.filter (fun z => z ^ 2 = x ^ 2)).card = 2 := by
    rw [hfib, Finset.card_insert_of_notMem (by simpa using hxne), Finset.card_singleton]
  rw [hcard]
  rw [nsmul_eq_mul]
  push_cast
  ring

/-! ## (d) The square sets stay disjoint -/

/-- **Disjointness descends to the squares:** if `A, B` are antipodally closed and disjoint, then
`A²` and `B²` are disjoint — a shared square `x² = z²` forces `x = ±z`, and both `z` and `−z` lie
in `B` by closure, so `x ∈ A ∩ B`. -/
theorem squares_disjoint [CharZero F] {A B : Finset F}
    (_hA : AntipodallyClosed A) (hB : AntipodallyClosed B) (hdisj : Disjoint A B) :
    Disjoint (squares A) (squares B) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyA hyB
  obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hyA
  obtain ⟨z, hzB, hz⟩ := Finset.mem_image.mp hyB
  -- z² = x² ⟹ z = ±x ⟹ x ∈ B (using closure for the − case)
  have : (z - x) * (z + x) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp this with h | h
  · have hzx : z = x := by linear_combination h
    rw [hzx] at hzB
    exact Finset.disjoint_left.mp hdisj hxA hzB
  · have hzx : z = -x := by linear_combination h
    rw [hzx] at hzB
    have : x ∈ B := by
      have := hB.2 (-x) hzB
      rwa [neg_neg] at this
    exact Finset.disjoint_left.mp hdisj hxA this

/-! ## The assembled halving step -/

/-- **THE WINDOW-HALVING STEP (the full-window recursion engine).** Let `A, B` be antipodally
closed (supplied by Round-25's general `t=1` theorem from the `p₁` condition), disjoint, with
equal power sums `p_r` for all `r ≤ t`. Then the square sets `A², B²` are disjoint with equal
power sums `p_l` for all `l ≤ t/2` — the window halves and the scale descends from `μ_{2N}` to
`μ_N` (whose half basis inherits independence). Iterating `⌈log₂(t+1)⌉` times exhausts any linear
window, forcing the iterated-antipodal (= `2^k`-lift, Round-22) structure: **floor = ceiling on
the full window for disjoint families.** -/
theorem window_halving_step [CharZero F] {A B : Finset F}
    (hA : AntipodallyClosed A) (hB : AntipodallyClosed B) (hdisj : Disjoint A B)
    {t : ℕ} (hwin : ∀ r, 1 ≤ r → r ≤ t → (∑ x ∈ A, x ^ r) = ∑ x ∈ B, x ^ r) :
    Disjoint (squares A) (squares B) ∧
      (∀ l, 1 ≤ l → 2 * l ≤ t → (∑ y ∈ squares A, y ^ l) = ∑ y ∈ squares B, y ^ l) := by
  refine ⟨squares_disjoint hA hB hdisj, ?_⟩
  intro l hl1 hlt
  have h2l := hwin (2 * l) (by omega) hlt
  rw [even_psum_halves hA l, even_psum_halves hB l] at h2l
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp at h2l
  exact h2l

end Round26Recursion

#print axioms Round26Recursion.odd_psum_vanish
#print axioms Round26Recursion.even_psum_halves
#print axioms Round26Recursion.squares_disjoint
#print axioms Round26Recursion.window_halving_step

