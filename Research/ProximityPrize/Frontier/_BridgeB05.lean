/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even

/-!
# Bridge B05 — odd-graded antipodal vanishing (#444, target E6)

The E6 recursion has two halves. The even half is a folding bijection; the **odd half**
(`#bad_{2n}(k, odd) = 0`) is governed by the antipodal involution `-1 ∈ μ_{2n}`.

This file isolates the clean mathematical core of that odd vanishing: a graded coefficient
obtained by summing an **odd-weight** value over a set that is **closed under negation** is `0`,
because the negation involution pairs each element `x` with `-x` and the odd weight flips sign
across the pair (`w(-x) = -w(x)`), so the two contributions cancel. The total sum is therefore
its own negation, hence zero.

Concretely, with `μ_{2n}` carrying the antipodal symmetry `x ↦ -x` (the unique order-2 element
`-1 ∈ μ_{2n}`), an *odd* graded frequency component `b ↦ ∑_{x} w_b(x)` over a negation-symmetric
subset, where `w_b(-x) = -w_b(x)` for an odd-graded weight `w_b`, vanishes identically. Hence the
count `#bad_{2n}(k, odd)` of distinct nonzero such vectors is `0` — there are none.

Stated abstractly over any additive commutative group `M` of values inside a target where `2`
is cancellable (here we use `ℤ`/`ℚ`-style: the sum equals its own negation ⇒ it is `0`), and a
*generic* index set `S` that is closed under an involution `σ` with `w ∘ σ = -w`.

Issue #444, E6 (odd half).
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB05

variable {ι : Type*} [DecidableEq ι]

/-- **Antipodal odd vanishing (core).** Let `σ : ι → ι` be an involution (`σ ∘ σ = id`) that
maps the finite set `S` into itself, and let `w : ι → ℤ` be *odd* across `σ`, i.e.
`w (σ x) = - w x`. Then `∑_{x ∈ S} w x = 0`.

This is the exact mechanism behind E6's odd half: `σ = (· * (-1))` is the antipodal involution
of `μ_{2n}` (negation by the order-2 root `-1`), `S` a negation-closed subset, and `w` an
odd-graded frequency weight. The sum is invariant under reindexing by `σ` yet `w` flips sign,
forcing `T = -T`, hence `T = 0`. No `μ_n`-structure or field characteristic is used. -/
theorem antipodal_odd_sum_zero {S : Finset ι} {σ : ι → ι}
    (hinv : ∀ x, σ (σ x) = x)
    (hmap : ∀ x ∈ S, σ x ∈ S)
    (w : ι → ℤ) (hodd : ∀ x, w (σ x) = - w x) :
    ∑ x ∈ S, w x = 0 := by
  -- The image of S under σ is S itself (σ is an involution mapping S into S).
  have himg : S.image σ = S := by
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hmap x hx
    · intro x hx
      rw [Finset.mem_image]
      exact ⟨σ x, hmap x hx, hinv x⟩
  have hσinj : ∀ x ∈ S, ∀ y ∈ S, σ x = σ y → x = y := by
    intro x _ y _ h
    have := congrArg σ h
    rwa [hinv, hinv] at this
  -- reindex the sum by the involution σ : sum is unchanged
  have hbij : ∑ x ∈ S, w x = ∑ x ∈ S, w (σ x) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image hσinj]
  -- but w (σ x) = - w x, so the sum equals its own negation
  have hsneg : ∑ x ∈ S, (- w x) = - ∑ x ∈ S, w x := Finset.sum_neg_distrib (s := S) w
  have hcongr : ∑ x ∈ S, w (σ x) = ∑ x ∈ S, (- w x) :=
    Finset.sum_congr rfl (fun x _ => hodd x)
  have hself : ∑ x ∈ S, w x = - ∑ x ∈ S, w x := hbij.trans (hcongr.trans hsneg)
  omega

/-- **Odd-graded count is zero (E6 odd half).** Package the vanishing as: under the antipodal
involution hypotheses, the value of the graded component is `0`, so it cannot be a *nonzero*
graded vector. Hence the set of indices `b` whose odd-graded component is nonzero is empty —
i.e. `#bad_{2n}(k, odd) = 0`. -/
theorem antipodal_odd_count_zero {B : Finset ι} {S : ι → Finset ι} {σ : ι → ι}
    (hinv : ∀ x, σ (σ x) = x)
    (hmap : ∀ b, ∀ x ∈ S b, σ x ∈ S b)
    (w : ι → ι → ℤ) (hodd : ∀ b, ∀ x, w b (σ x) = - w b x) :
    (B.filter (fun b => ∑ x ∈ S b, w b x ≠ 0)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _
  simp only [ne_eq, not_not]
  exact antipodal_odd_sum_zero hinv (hmap b) (w b) (hodd b)

end ArkLib.ProximityGap.BridgeB05

#print axioms ArkLib.ProximityGap.BridgeB05.antipodal_odd_sum_zero
#print axioms ArkLib.ProximityGap.BridgeB05.antipodal_odd_count_zero
