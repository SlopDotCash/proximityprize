/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Square-root-pair power sums — the descent step of the tower-fiber theorem (issue #232)

For the squaring map `s : x ↦ x²` on a field of characteristic `≠ 2`, the full preimage
`s⁻¹(T)` of a finite set `T` (with chosen roots `y z`, so `s⁻¹(T) = ⋃_{z∈T} {y z, −y z}`)
satisfies:

* `sum_pow_even_sqrtPairs` — `∑_{x ∈ s⁻¹(T)} x^(2j) = 2·∑_{z ∈ T} z^j`: even power sums
  descend with a factor `2`;
* `sum_pow_odd_sqrtPairs` — `∑_{x ∈ s⁻¹(T)} x^(2j+1) = 0`: odd power sums vanish;
* `card_sqrtPairs` — `|s⁻¹(T)| = 2·|T|`.

These are the induction-step identities of the tower-fiber exhaustiveness theorem
(DISPROOF_LOG O54): for `S ⊆ μ_{2^m}` with `e₁(S) = ⋯ = e_t(S) = 0`, Newton's identities
convert to power sums, the `t = 1` antipodal theorem gives `S = s⁻¹(T)`, and the
identities here hand `T ⊆ μ_{2^(m−1)}` the vanishing conditions at depth `⌊t/2⌋` — so the
`t`-fiber descends the squaring tower and equals the coset-union family
`(s^L)⁻¹(U)`, `L = ⌊log₂ t⌋ + 1`, with exact count `C(n/2^L, w/2^L)`.
-/

namespace ArkLib.SqrtPairs

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The full square-root preimage of `T`: each `z ∈ T` contributes its chosen
root `y z` and the antipode `-(y z)`. -/
def sqrtPairs (T : Finset F) (y : F → F) : Finset F :=
  T.biUnion fun z => {y z, -(y z)}

section
variable {T : Finset F} {y : F → F}

theorem pairwiseDisjoint_sqrtPairs (hy : ∀ z ∈ T, y z ^ 2 = z) :
    (↑T : Set F).PairwiseDisjoint (fun z => ({y z, -(y z)} : Finset F)) := by
  intro z hz z' hz' hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  have hsq : ∀ w ∈ T, ∀ u ∈ ({y w, -(y w)} : Finset F), u ^ 2 = w := by
    intro w hw u hu
    rcases mem_insert.mp hu with h | h
    · rw [h]; exact hy w hw
    · rw [mem_singleton.mp h, neg_sq]; exact hy w hw
  exact hne ((hsq z hz x hx).symm.trans (hsq z' hz' x hx'))

omit [DecidableEq F] in
theorem pair_ne (hchar : (2 : F) ≠ 0) {z : F} (hz0 : y z ≠ 0) : y z ≠ -(y z) := by
  intro hcontra
  apply hz0
  have h2 : (2 : F) * y z = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hchar
  · exact h

/-- Cardinality: the square-root preimage doubles the size. -/
theorem card_sqrtPairs (hchar : (2 : F) ≠ 0) (hy : ∀ z ∈ T, y z ^ 2 = z)
    (hy0 : ∀ z ∈ T, y z ≠ 0) : (sqrtPairs T y).card = 2 * T.card := by
  rw [sqrtPairs, card_biUnion (pairwiseDisjoint_sqrtPairs hy)]
  rw [sum_congr rfl fun z hz => card_pair (pair_ne hchar (hy0 z hz))]
  rw [sum_const, smul_eq_mul, mul_comm]

/-- **Even power sums descend with a factor 2 down the squaring map**:
`∑_{x ∈ s⁻¹(T)} x^(2j) = 2 · ∑_{z ∈ T} z^j` — the descent step of the
tower-fiber induction (DISPROOF_LOG O54). -/
theorem sum_pow_even_sqrtPairs (hchar : (2 : F) ≠ 0) (hy : ∀ z ∈ T, y z ^ 2 = z)
    (hy0 : ∀ z ∈ T, y z ≠ 0) (j : ℕ) :
    ∑ x ∈ sqrtPairs T y, x ^ (2 * j) = 2 * ∑ z ∈ T, z ^ j := by
  rw [sqrtPairs, sum_biUnion (pairwiseDisjoint_sqrtPairs hy), mul_sum]
  refine sum_congr rfl fun z hz => ?_
  rw [sum_pair (pair_ne hchar (hy0 z hz)), Even.neg_pow (even_two_mul j),
    pow_mul, hy z hz]
  ring

/-- **Odd power sums of a full square-root preimage vanish**:
`∑_{x ∈ s⁻¹(T)} x^(2j+1) = 0`. -/
theorem sum_pow_odd_sqrtPairs (hchar : (2 : F) ≠ 0) (hy : ∀ z ∈ T, y z ^ 2 = z)
    (hy0 : ∀ z ∈ T, y z ≠ 0) (j : ℕ) :
    ∑ x ∈ sqrtPairs T y, x ^ (2 * j + 1) = 0 := by
  rw [sqrtPairs, sum_biUnion (pairwiseDisjoint_sqrtPairs hy)]
  rw [sum_congr rfl fun z hz => sum_pair (pair_ne hchar (hy0 z hz))]
  refine sum_eq_zero fun z hz => ?_
  rw [Odd.neg_pow ⟨j, by ring⟩]
  ring

end

end ArkLib.SqrtPairs

