/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Large images of finite-field linear functionals

Ported from `proximity-prize/proximity-prize` at
`ed2b68c4a330d76dc4ab6693eec81b685b493270`,
`ProximityPrize/SubmissionUpper/HalfRadiusCollision.lean`.
The Apache-2.0 source license is preserved.

Averaging off-diagonal collisions and applying Cauchy–Schwarz gives a linear
functional whose image has density at least `|A| / (|F| + |A| - 1)`.
Sets larger than `(|F| - 1)^2` have a surjective linear projection.
These are unconditional finite-field statements, independent of any IRS
benchmark profile or game-soundness interpretation.
-/

namespace FiniteField.LinearProjection

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The linear functional specified by its coefficient vector. -/
def dot {k : ℕ} (x v : Fin k → F) : F := ∑ i, x i * v i

omit [Fintype F] [DecidableEq F] in
/-- A nonzero coefficient vector defines a surjective functional. -/
lemma dot_surjective {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    Function.Surjective (dot d) := by
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    simpa only [ne_eq, Pi.zero_apply, Function.ne_iff] using hd
  intro y
  let v : Fin k → F := fun i => if i = j then (d j)⁻¹ * y else 0
  refine ⟨v, ?_⟩
  simp only [dot, v]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro b _ hbj
    simp [hbj]
  · simp

/-- Every nonzero functional has exactly one field-sized quotient of its domain. -/
lemma dot_zero_fiber_card_mul {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    ((Finset.univ.filter fun v : Fin k → F => dot d v = 0).card) * Fintype.card F =
      Fintype.card (Fin k → F) := by
  classical
  let φ : (Fin k → F) →+ F :=
    { toFun := dot d
      map_zero' := by simp [dot]
      map_add' := by
        intro x y
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hsurj : Function.Surjective φ := dot_surjective hd
  let K := (Finset.univ.filter fun v : Fin k → F => φ v = 0).card
  have hfiber (y : F) :
      (Finset.univ.filter fun v : Fin k → F => φ v = y).card = K := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj y) (hsurj 0)
  have hsum : Fintype.card (Fin k → F) =
      ∑ y : F, (Finset.univ.filter fun v : Fin k → F => φ v = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin k → F)))
      (t := (Finset.univ : Finset F)) (f := φ)
      (fun _ _ => Finset.mem_univ _))
  rw [hsum]
  simp_rw [hfiber]
  simp [K, φ, Nat.mul_comm]
  rfl

/-- Averaging selects a functional with at most the mean off-diagonal collision count. -/
lemma exists_dot_offdiag_le {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      Fintype.card F *
          ((A.product A).filter fun xy =>
            xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card ≤
        A.card * (A.card - 1) := by
  classical
  let P := A.offDiag
  let off : (Fin k → F) → ℕ := fun v =>
    ∑ xy ∈ P, if dot xy.1 v = dot xy.2 v then 1 else 0
  have hPcard : P.card = A.card * (A.card - 1) := by
    simp only [P, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  have hinner (xy : (Fin k → F) × (Fin k → F)) (hxy : xy ∈ P) :
      Fintype.card F *
          (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) =
        Fintype.card (Fin k → F) := by
    have hne : xy.1 ≠ xy.2 := by
      exact (Finset.mem_offDiag.mp (by simpa only [P] using hxy)).2.2
    have hd : xy.1 - xy.2 ≠ 0 := sub_ne_zero.mpr hne
    have hfilter :
        (Finset.univ.filter fun v : Fin k → F => dot xy.1 v = dot xy.2 v).card =
          (Finset.univ.filter fun v : Fin k → F => dot (xy.1 - xy.2) v = 0).card := by
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    rw [← Finset.card_filter, hfilter, Nat.mul_comm]
    exact dot_zero_fiber_card_mul hd
  have htotal :
      (∑ v : Fin k → F, Fintype.card F * off v) =
        ∑ _v : Fin k → F, P.card := by
    calc
      (∑ v : Fin k → F, Fintype.card F * off v) =
          ∑ v : Fin k → F, ∑ xy ∈ P,
            Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
              simp only [off, Finset.mul_sum]
      _ = ∑ xy ∈ P, ∑ v : Fin k → F,
          Fintype.card F * if dot xy.1 v = dot xy.2 v then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ xy ∈ P, Fintype.card F *
            (∑ v : Fin k → F, if dot xy.1 v = dot xy.2 v then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro xy _
              rw [Finset.mul_sum]
      _ = ∑ _xy ∈ P, Fintype.card (Fin k → F) := by
            apply Finset.sum_congr rfl
            intro xy hxy
            exact hinner xy hxy
      _ = ∑ _v : Fin k → F, P.card := by simp [Nat.mul_comm]
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin k → F))) Finset.univ_nonempty
    (show (∑ v : Fin k → F, Fintype.card F * off v) ≤
      ∑ _v : Fin k → F, P.card by rw [htotal])
  refine ⟨v, ?_⟩
  rw [← hPcard]
  have hoff :
      ((A.product A).filter fun xy =>
        xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card = off v := by
    rw [Finset.card_filter]
    simp only [off, P]
    rw [show A.offDiag = (A ×ˢ A).filter (fun xy => xy.1 ≠ xy.2) by
      ext xy
      rcases xy with ⟨x, y⟩
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨hx, hy, hne⟩
        exact ⟨⟨hx, hy⟩, hne⟩
      · rintro ⟨⟨hx, hy⟩, hne⟩
        exact ⟨hx, hy, hne⟩]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hne : xy.1 ≠ xy.2 <;>
      by_cases heq : dot xy.1 v = dot xy.2 v <;> simp [hne, heq]
  simpa only [hoff] using hv

/-- Some linear functional has an image whose density is at least
`|A| / (|F| + |A| - 1)`.  This is the quantitative form of the collision
argument: unlike `exists_dot_surjective_of_card_sq_lt`, it does not require the
image to be all of `F`. -/
theorem exists_dot_image_card_bound {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      A.card * Fintype.card F ≤
        (A.image (fun x => dot x v)).card * (Fintype.card F + A.card - 1) := by
  classical
  by_cases hA : A.card = 0
  · refine ⟨0, ?_⟩
    simp [hA]
  obtain ⟨v, hoff⟩ := exists_dot_offdiag_le A
  let q := Fintype.card F
  let N := A.card
  let O := ((A.product A).filter fun xy =>
    xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card
  let E := ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v).card
  let c : F → ℕ := fun y => (A.filter fun x => dot x v = y).card
  let support : Finset F := Finset.univ.filter fun y => c y ≠ 0
  have hYeq : support = A.image (fun x => dot x v) := by
    ext y
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, c]
    exact Finset.fiber_card_ne_zero_iff_mem_image A (fun x => dot x v) y
  have hsumc : ∑ y ∈ support, c y = N := by
    have hall : ∑ y : F, c y = A.card := by
      symm
      simpa only [c] using (Finset.card_eq_sum_card_fiberwise
        (s := A) (t := (Finset.univ : Finset F)) (f := fun x => dot x v)
        (fun _ _ => Finset.mem_univ _))
    change ∑ y ∈ support, c y = A.card
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    exact hyY
  have hsumsq : ∑ y ∈ support, c y ^ 2 = E := by
    have hall : ∑ y : F, c y ^ 2 = E := by
      simp only [c, E, Finset.card_filter]
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp
      rw [Finset.card_filter, Finset.sum_product_right]
      simp_rw [Finset.card_filter]
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    simp [hyY]
  have hE : E = N + O := by
    simp only [E, N, O]
    rw [show ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v) =
        A.diag ∪ ((A.product A).filter fun xy =>
          xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v) by
      ext xy
      rcases xy with ⟨x, y⟩
      by_cases hxy : x = y <;> simp [hxy]]
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hdiag hoffdiag
      simp only [Finset.mem_diag] at hdiag
      simp only [Finset.mem_filter] at hoffdiag
      exact hoffdiag.2.1 hdiag.2
  have hlower : N ^ 2 ≤ support.card * E := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := support) (f := c)
    rw [hsumc, hsumsq] at hcauchy
    exact hcauchy
  have hupper : q * O ≤ N * (N - 1) := by
    simpa only [q, N, O] using hoff
  have hNpos : 0 < N := by simpa only [N] using Nat.pos_of_ne_zero hA
  have hcombined : q * N ^ 2 ≤
      support.card * (q * N + N * (N - 1)) := by
    calc
      q * N ^ 2 ≤ q * (support.card * E) := Nat.mul_le_mul_left q hlower
      _ = support.card * (q * N + q * O) := by rw [hE]; ring
      _ ≤ support.card * (q * N + N * (N - 1)) := by
        exact Nat.mul_le_mul_left support.card (Nat.add_le_add_left hupper (q * N))
  have hleft : q * N ^ 2 = N * (N * q) := by ring
  have hright : support.card * (q * N + N * (N - 1)) =
      N * (support.card * (q + N - 1)) := by
    have hN : 1 ≤ N := hNpos
    rw [show q + N - 1 = q + (N - 1) by omega]
    ring
  rw [hleft, hright] at hcombined
  refine ⟨v, ?_⟩
  rw [← hYeq]
  simpa only [q, N] using Nat.le_of_mul_le_mul_left hcombined hNpos

/-- A set larger than `(q - 1)^2` has a linear projection onto the whole field.
This follows directly from the quantitative image bound; no second collision
count is needed. -/
theorem exists_dot_surjective_of_card_sq_lt {k : ℕ} (A : Finset (Fin k → F))
    (hlarge : (Fintype.card F - 1) ^ 2 < A.card) :
    ∃ v : Fin k → F, A.image (fun x => dot x v) = Finset.univ := by
  classical
  obtain ⟨v, hv⟩ := exists_dot_image_card_bound A
  refine ⟨v, ?_⟩
  by_contra hne
  have hlt : (A.image (fun x => dot x v)).card < Fintype.card F := by
    simpa using Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  have hle : (A.image (fun x => dot x v)).card ≤ Fintype.card F - 1 := by omega
  have hbound := hv.trans (Nat.mul_le_mul_right _ hle)
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hsub : Fintype.card F - 1 + 1 = Fintype.card F := by omega
  rw [show Fintype.card F + A.card - 1 = Fintype.card F - 1 + A.card by omega]
    at hbound
  nlinarith

end FiniteField.LinearProjection

#print axioms FiniteField.LinearProjection.exists_dot_image_card_bound
#print axioms FiniteField.LinearProjection.exists_dot_surjective_of_card_sq_lt
