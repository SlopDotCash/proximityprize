/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic

/-!
# Count-balanced tuples are zero-sum (char-free converse, lifted to `Fin m → F`) — #444

The negation-symmetric strata count of `N0 μ_n 6` (kb note
`docs/kb/e3-exact-via-negation-symmetric-strata.md`) needs the value-tuple form of the
antipodal converse:

> a tuple `c : Fin m → F` avoiding `0` (over a field with `(2:F) ≠ 0`) whose value fibers
> are antipodally balanced (`#{i : c i = z} = #{i : c i = -z}` ∀z) sums to `0`.

This is the **easy, char-free** half of `zero-sum ⟺ count-balanced` (the forward half is
char-0 Lam–Leung, the open `RepThree`). The in-tree multiset converse
`LamLeungMultisetAntipodal.sum_eq_zero_of_count_antipodal` is stated under a spurious
`[CharZero L]` (incompatible with the finite `μ_n ⊂ F_p`), so we reprove it char-free here
with the pairing `z ↦ −z` and `(2:F) ≠ 0` for fixed-point-freeness.
-/

set_option linter.style.longLine false
set_option autoImplicit false


open Finset

namespace ArkLib.ProximityGap.Frontier.E3NegSymConverse

variable {F : Type*} [Field F] [DecidableEq F]

/-- In a field with `(2:F) ≠ 0`, `a = -a` forces `a = 0`. -/
private theorem eq_zero_of_eq_neg {a : F} (h2 : (2 : F) ≠ 0) (h : a = -a) : a = 0 := by
  have h2a : (2 : F) * a = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2a with h' | h'
  · exact absurd h' h2
  · exact h'

/-- **Count-balanced multiset ⟹ zero-sum (char-free).** A multiset `M` over a field with
`(2:F) ≠ 0`, avoiding `0`, whose counts are antipodally balanced, sums to `0`. Pairs each
value `z` with `−z` (`Finset.sum_involution`); fixed-point-free since `z ≠ −z` for `z ≠ 0`. -/
theorem multiset_sum_eq_zero_of_count_antipodal {M : Multiset F} (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ M) (hbal : ∀ z : F, M.count z = M.count (-z)) :
    M.sum = 0 := by
  have hsc : M.sum = ∑ z ∈ M.toFinset, M.count z • z := by
    conv_lhs => rw [← Multiset.map_id M]
    rw [Finset.sum_multiset_map_count]; rfl
  rw [hsc]
  refine Finset.sum_involution (g := fun z _ => -z) ?_ ?_ ?_ ?_
  · intro a _
    rw [← hbal a, smul_neg, add_neg_cancel]
  · intro a ha _ hcontra
    have haM : a ∈ M := Multiset.mem_toFinset.mp ha
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ haM)
    exact ha0 (eq_zero_of_eq_neg h2 (by linear_combination -hcontra))
  · intro a ha
    have haM : a ∈ M := Multiset.mem_toFinset.mp ha
    have hpos : 0 < M.count a := Multiset.count_pos.mpr haM
    have hpos' : 0 < M.count (-a) := hbal a ▸ hpos
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hpos')
  · intro a _
    exact neg_neg a


/-- **Count-balanced tuple ⟹ zero-sum.** If `c : Fin m → F` (field, `(2:F) ≠ 0`) never hits
`0` and its value fibers are antipodally balanced, then `∑ i, c i = 0`. Lifts
`multiset_sum_eq_zero_of_count_antipodal` along `M = (univ.val).map c`. -/
theorem sum_eq_zero_of_fiber_balanced {m : ℕ} (h2 : (2 : F) ≠ 0) (c : Fin m → F)
    (h0 : ∀ i, c i ≠ 0)
    (hbal : ∀ z : F, (Finset.univ.filter (fun i => c i = z)).card
                   = (Finset.univ.filter (fun i => c i = -z)).card) :
    ∑ i, c i = 0 := by
  classical
  set M : Multiset F := (Finset.univ.val).map c with hM
  have hsum : M.sum = ∑ i, c i := by rw [hM]; rfl
  have hcount : ∀ z : F, M.count z = (Finset.univ.filter (fun i => c i = z)).card := by
    intro z
    rw [hM, Multiset.count_map]
    simp only [Finset.filter]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  have hM0 : (0 : F) ∉ M := by
    rw [hM, Multiset.mem_map]
    rintro ⟨i, _, hi⟩
    exact h0 i hi
  have hbalM : ∀ z : F, M.count z = M.count (-z) := by
    intro z; rw [hcount z, hcount (-z)]; exact hbal z
  rw [← hsum]
  exact multiset_sum_eq_zero_of_count_antipodal h2 hM0 hbalM

end ArkLib.ProximityGap.Frontier.E3NegSymConverse

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.E3NegSymConverse.multiset_sum_eq_zero_of_count_antipodal
#print axioms ArkLib.ProximityGap.Frontier.E3NegSymConverse.sum_eq_zero_of_fiber_balanced
