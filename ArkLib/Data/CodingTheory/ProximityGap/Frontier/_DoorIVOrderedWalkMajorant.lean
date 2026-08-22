/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

/-!
# Door IV ordered-walk maximal excursion majorizes the endpoint (#444)

DIR9 from the 2026-06-21 Door-IV frontier note isolates the ordered partial-sum walk at the
adversarial frequency `b*`.  If `S k` is the ordered prefix sum, its endpoint `S n` is the Gauss
period, while the maximal excursion `max_{k≤n} ‖S k‖` is a Doob/van-der-Corput
style object outside the `b`-summed polynomial dichotomy.

This file kernels only the finite, non-analytic scaffold: the endpoint norm is one of the
prefix norms, so the maximal excursion is a genuine majorant of the period endpoint.  Bounding the ordered-walk
maximal function therefore bounds `M`, but this theorem supplies no cancellation and makes no CORE
claim.  It is the citable normalization for any later DIR9 maximal-inequality attempt.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The finite set of prefix norms `‖S k‖` for `0 ≤ k ≤ n`. -/
noncomputable def prefixNorms (S : ℕ → E) (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image (fun k => ‖S k‖)

/-- The endpoint norm belongs to the finite prefix-norm set. -/
theorem endpoint_norm_mem_prefixNorms (S : ℕ → E) (n : ℕ) :
    ‖S n‖ ∈ prefixNorms S n := by
  unfold prefixNorms
  exact Finset.mem_image.mpr ⟨n, by simp, rfl⟩

/-- The prefix-norm set is nonempty: it contains the endpoint norm. -/
theorem prefixNorms_nonempty (S : ℕ → E) (n : ℕ) : (prefixNorms S n).Nonempty :=
  ⟨‖S n‖, endpoint_norm_mem_prefixNorms S n⟩

/-- The ordered-walk maximal excursion, implemented as the maximum of the finite
prefix-norm set. -/
noncomputable def maximalExcursion (S : ℕ → E) (n : ℕ) : ℝ :=
  (prefixNorms S n).max' (prefixNorms_nonempty S n)

/-- **DIR9 scaffold:** the endpoint norm is bounded by the ordered-walk maximal excursion.
Thus the Doob/ordered-walk object is a genuine majorant of the Gauss-period endpoint. -/
theorem endpoint_norm_le_maximalExcursion (S : ℕ → E) (n : ℕ) :
    ‖S n‖ ≤ maximalExcursion S n := by
  unfold maximalExcursion
  exact Finset.le_max' (prefixNorms S n) ‖S n‖
    (endpoint_norm_mem_prefixNorms S n)

/-- Any uniform bound on every ordered-walk maximal excursion immediately bounds the corresponding
endpoint.  This is the normalization consumed by a future DIR9 maximal-inequality proof: prove the
maximal bound, and the period endpoint follows for free. -/
theorem endpoint_bound_of_maximalExcursion_bound {S : ℕ → E} {n : ℕ} {C : ℝ}
    (h : maximalExcursion S n ≤ C) :
    ‖S n‖ ≤ C :=
  le_trans (endpoint_norm_le_maximalExcursion S n) h

end ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant

open ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant

#print axioms endpoint_norm_mem_prefixNorms
#print axioms endpoint_norm_le_maximalExcursion
#print axioms endpoint_bound_of_maximalExcursion_bound
