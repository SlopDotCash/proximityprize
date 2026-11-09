/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# LANE G105 (#466): depth-graded ledgers are lossless average-census re-slicings

This file formalizes the G104 referee's binding obstruction in its smallest reusable form.
The current signed-depth program partitions relation/census mass by a depth label and proves
per-depth sign facts, for example a positive deep floor at one depth and a vanishing singleton
fiber at another.  Those facts are honest bookkeeping, but the grading itself is **lossless**:
summing the observed depth buckets is exactly the original census/energy total.  Consequently any
target stated only as a bound on the sum of depth anomalies is equivalent to the ungraded total
bound.  Per-depth floors can only consume the same total budget; they cannot create a new
sup-side certificate or bypass the average-moment wall.

The theorem payload is deliberately abstract over the graded objects.  Instantiate `U` as the
finite relation/census universe, `depth : α → σ` as collision-depth/intersection-size, and
`w : α → ℝ` as the signed anomaly weight.  The depth label type `σ` may be infinite, such as
`ℕ`; all full-ledger sums are taken over the finite observed set `U.image depth`.

* `sum_depthLedgers_eq_total` is the losslessness identity over observed depths:
  `Σ_{s∈depth(U)} Σ_{x∈U, depth x=s} w x = Σ_{x∈U} w x`.
* `depthLedger_target_iff_total_target` says a graded target on the observed full depth sum is
  literally the ungraded target.
* `floor_consumes_remaining_budget` and `depthFloor_consumes_remaining_budget` record the
  circularity of deep floors: if a collection of observed depth buckets has already contributed
  at least `L`, then any proof of total budget `B` must force all remaining observed buckets into
  `≤ B-L`.  The floor does not help the target; it spends slack.
* `depthLedger_eq_zero_of_no_depth` records the G104-style empty-fiber pin: an absent depth bucket
  contributes exactly zero, hence no compensating negative mass.

Honest scope: this closes the depth-grading/per-depth-sign ladder as a route to the prize-facing
sup wall.  It does not rule out a genuinely new non-Fourier small-difference counting certificate;
it says only that re-slicing an average census by depth remains the same average census.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo

variable {α σ R : Type*}

/-- The depth bucket of `U` at label `t`: all objects whose depth/grade is `t`. -/
noncomputable def depthBucket [DecidableEq α] [DecidableEq σ]
    (U : Finset α) (depth : α → σ) (t : σ) : Finset α :=
  U.filter (fun x => depth x = t)

/-- The signed ledger contribution of one depth bucket. -/
noncomputable def depthLedger [DecidableEq α] [DecidableEq σ] [AddCommMonoid R]
    (U : Finset α) (depth : α → σ) (w : α → R) (t : σ) : R :=
  ∑ x ∈ depthBucket U depth t, w x

/-- **Losslessness of the depth grading.**  Summing every observed depth bucket gives exactly the
original ungraded signed total.  This is the kernel of the G104 no-go: a depth ledger re-indexes
the census; it does not change the net object.  The depth label type can be infinite; only the
finite observed set `U.image depth` is summed. -/
theorem sum_depthLedgers_eq_total [DecidableEq α] [DecidableEq σ]
    [AddCommMonoid R] (U : Finset α) (depth : α → σ) (w : α → R) :
    (∑ t ∈ U.image depth, depthLedger U depth w t) = ∑ x ∈ U, w x := by
  classical
  simpa [depthLedger, depthBucket] using
    (Finset.sum_fiberwise_of_maps_to (s := U) (t := U.image depth)
      (g := depth) (fun _ hx => Finset.mem_image_of_mem depth hx) w)

/-- **Full graded target iff ungraded target.**  Any bound stated only on the sum over observed
depth buckets is definitionally the same budget as the original total bound. -/
theorem depthLedger_target_iff_total_target [DecidableEq α] [DecidableEq σ]
    (U : Finset α) (depth : α → σ) (w : α → ℝ) (B : ℝ) :
    ((∑ t ∈ U.image depth, depthLedger U depth w t) ≤ B) ↔ (∑ x ∈ U, w x ≤ B) := by
  rw [sum_depthLedgers_eq_total (U := U) (depth := depth) (w := w)]

/-- Empty depth buckets contribute exactly zero.  This is the abstract form of a `depthFiber = 0`
pin: useful bookkeeping, but no negative compensation for the full ledger. -/
theorem depthLedger_eq_zero_of_no_depth [DecidableEq α] [DecidableEq σ] [AddCommMonoid R]
    (U : Finset α) (depth : α → σ) (w : α → R) (t : σ)
    (h : ∀ x ∈ U, depth x ≠ t) :
    depthLedger U depth w t = 0 := by
  classical
  have hb : depthBucket U depth t = ∅ := by
    ext x
    by_cases hx : x ∈ U
    · simp only [depthBucket, Finset.mem_filter, hx, true_and, notMem_empty, iff_false]
      exact h x hx
    · simp only [depthBucket, Finset.mem_filter, hx, false_and, notMem_empty]
  simp [depthLedger, hb]

/-- **Floors spend slack.**  If a set of grades `F` already contributes at least `L`, then any
total budget `B` forces the remaining grades to fit inside `B - L`.  This is the algebraic reason
positive deep floors do not help a ledger target: they make the residual obligation harder by the
same amount. -/
theorem floor_consumes_remaining_budget {σ : Type*} [DecidableEq σ]
    (T F : Finset σ) (a : σ → ℝ) {L B : ℝ}
    (hF : F ⊆ T) (hfloor : L ≤ ∑ t ∈ F, a t)
    (htarget : ∑ t ∈ T, a t ≤ B) :
    ∑ t ∈ T \ F, a t ≤ B - L := by
  have hsplit := Finset.sum_sdiff (s₁ := F) (s₂ := T) (f := a) hF
  linarith

/-- **Depth-floor circularity, in ledger form.**  Applying `floor_consumes_remaining_budget` to the
lossless depth ledger: once some observed depth set has a lower floor `L`, a proof of the original
total budget must extract a `B - L` bound from the complement.  The grading supplies no independent
saving; the hard work is pushed into the remaining observed buckets. -/
theorem depthFloor_consumes_remaining_budget [DecidableEq α] [DecidableEq σ]
    (U : Finset α) (depth : α → σ) (w : α → ℝ) (F : Finset σ) {L B : ℝ}
    (hF : F ⊆ U.image depth)
    (hfloor : L ≤ ∑ t ∈ F, depthLedger U depth w t)
    (htarget : ∑ x ∈ U, w x ≤ B) :
    ∑ t ∈ U.image depth \ F, depthLedger U depth w t ≤ B - L := by
  classical
  refine floor_consumes_remaining_budget (T := U.image depth) (F := F)
    (a := depthLedger U depth w) hF hfloor ?_
  simpa using
    (depthLedger_target_iff_total_target (U := U) (depth := depth) (w := w) (B := B)).2 htarget

#print axioms ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo.sum_depthLedgers_eq_total
#print axioms ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo.depthLedger_target_iff_total_target
#print axioms ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo.depthLedger_eq_zero_of_no_depth
#print axioms ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo.floor_consumes_remaining_budget
#print axioms ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo.depthFloor_consumes_remaining_budget

end ArkLib.ProximityGap.Frontier.G105DepthLedgerLosslessNoGo
