/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# BCS compiler soundness error accounting (issue #62)

The total-error monotonicity + bcs_union_bound (IOP-soundness + Merkle-binding + FS error union)
+ two-phase accounting. The full compiler construction is separate.
-/

open scoped NNReal
open scoped BigOperators

namespace ArkLibScratch.Issue62

/-! ## 1. The BCS total error: ε_interaction + Σ ε_open

`m` is the number of committed oracle messages (the `pSpec.MessageIdx ≃ Fin m`
ordering in `BCSTransform`). `εInteraction` is the interaction-phase soundness
error; `εOpen i` is the soundness/binding error of the `i`-th per-message opening
proof. The total compiled error is their union-bound sum. -/

/-- The total soundness error of a BCS-compiled protocol with `m` committed
messages: the interaction-phase error plus the sum of the per-message opening
errors. This is the `ε_interaction + Σ ε_open(i)` accounting target. -/
def bcsTotalError {m : ℕ} (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0) : ℝ≥0 :=
  εInteraction + ∑ i, εOpen i

/-- With zero committed messages the opening phase is empty, so the BCS error is
just the interaction-phase error. (Empty opening schedule base case.) -/
@[simp] theorem bcsTotalError_zero (εInteraction : ℝ≥0) (εOpen : Fin 0 → ℝ≥0) :
    bcsTotalError εInteraction εOpen = εInteraction := by
  simp [bcsTotalError]

/-- The `cons` (one-more-message) recurrence for the BCS total error:
peeling off message `0` adds its opening error and recurses on the rest.
This is the inductive step matching `BCSOpeningSchedule.toOpeningStatements_cons`
in the source file. -/
theorem bcsTotalError_succ {m : ℕ} (εInteraction : ℝ≥0) (εOpen : Fin (m + 1) → ℝ≥0) :
    bcsTotalError εInteraction εOpen
      = εOpen 0 + bcsTotalError εInteraction (fun i => εOpen i.succ) := by
  unfold bcsTotalError
  rw [Fin.sum_univ_succ]
  ring

/-- Single committed message: the BCS error is the interaction error plus the one
opening error. This is the shape that matches `Reduction.append interaction
opening` with a single per-message opening, i.e. `Verifier.append_soundness`'s
additive error `soundnessError₁ + soundnessError₂`. -/
theorem bcsTotalError_one (εInteraction : ℝ≥0) (εOpen : Fin 1 → ℝ≥0) :
    bcsTotalError εInteraction εOpen = εInteraction + εOpen 0 := by
  simp [bcsTotalError]

/-- Splitting a concatenated opening-error vector splits the BCS total error into the left
batch's total plus the right batch's opening-error sum. This is the algebraic accounting rule for
grouping opening proofs into two consecutive batches. -/
theorem bcsTotalError_append {m n : ℕ}
    (εInteraction : ℝ≥0) (εLeft : Fin m → ℝ≥0) (εRight : Fin n → ℝ≥0) :
    bcsTotalError εInteraction (Fin.append εLeft εRight) =
      bcsTotalError εInteraction εLeft + ∑ i, εRight i := by
  unfold bcsTotalError
  rw [Fin.sum_univ_add]
  simp [Fin.append]
  ring

/-- Appending an empty left batch leaves the BCS total error unchanged. -/
theorem bcsTotalError_append_zero_left {m : ℕ}
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0) :
    bcsTotalError εInteraction (Fin.append (Fin.elim0 : Fin 0 → ℝ≥0) εOpen) =
      bcsTotalError εInteraction εOpen := by
  rw [bcsTotalError_append]
  simp [bcsTotalError]

/-- Appending an empty right batch leaves the BCS total error unchanged. -/
theorem bcsTotalError_append_zero_right {m : ℕ}
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0) :
    bcsTotalError εInteraction (Fin.append εOpen (Fin.elim0 : Fin 0 → ℝ≥0)) =
      bcsTotalError εInteraction εOpen := by
  rw [bcsTotalError_append]
  simp [bcsTotalError]

/-- The BCS total error is monotone in the interaction error. -/
theorem bcsTotalError_mono_interaction {m : ℕ} {ε₁ ε₂ : ℝ≥0} (εOpen : Fin m → ℝ≥0)
    (h : ε₁ ≤ ε₂) : bcsTotalError ε₁ εOpen ≤ bcsTotalError ε₂ εOpen := by
  unfold bcsTotalError
  gcongr

/-- The BCS total error is monotone in the per-message opening errors (pointwise).
Monotonicity is exactly what is needed to relax binding errors upward, mirroring
`soundness.mono_error` in `Security/Basic.lean`. -/
theorem bcsTotalError_mono_open {m : ℕ} (εInteraction : ℝ≥0)
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0} (h : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInteraction εOpen₁ ≤ bcsTotalError εInteraction εOpen₂ := by
  unfold bcsTotalError
  gcongr with i
  exact h i

/-- Joint monotonicity in both the interaction error and the opening errors. -/
theorem bcsTotalError_mono {m : ℕ} {εInt₁ εInt₂ : ℝ≥0}
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0}
    (hInt : εInt₁ ≤ εInt₂) (hOpen : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInt₁ εOpen₁ ≤ bcsTotalError εInt₂ εOpen₂ :=
  le_trans (bcsTotalError_mono_open εInt₁ hOpen)
    (bcsTotalError_mono_interaction εOpen₂ hInt)

/-- Relax the interaction and per-opening budgets, then expose the successor recurrence for the
relaxed BCS total error. -/
theorem bcsTotalError_succ_mono_error {m : ℕ}
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    {εOpen₁ εOpen₂ : Fin (m + 1) → ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hOpen : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInteraction₁ εOpen₁
      ≤ εOpen₂ 0 + bcsTotalError εInteraction₂ (fun i : Fin m => εOpen₂ i.succ) := by
  calc
    bcsTotalError εInteraction₁ εOpen₁ ≤ bcsTotalError εInteraction₂ εOpen₂ :=
      bcsTotalError_mono hInteraction hOpen
    _ = εOpen₂ 0 + bcsTotalError εInteraction₂ (fun i : Fin m => εOpen₂ i.succ) :=
      bcsTotalError_succ εInteraction₂ εOpen₂

/-- Relax the interaction budget for the no-opening total-error base case. -/
theorem bcsTotalError_zero_mono_error
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂) :
    bcsTotalError εInteraction₁ (Fin.elim0 : Fin 0 → ℝ≥0) ≤ εInteraction₂ := by
  calc
    bcsTotalError εInteraction₁ (Fin.elim0 : Fin 0 → ℝ≥0) = εInteraction₁ :=
      bcsTotalError_zero εInteraction₁ (Fin.elim0 : Fin 0 → ℝ≥0)
    _ ≤ εInteraction₂ := hInteraction

/-- Relax the interaction and opening budgets for the one-opening total-error base case. -/
theorem bcsTotalError_one_mono_error
    {εInteraction₁ εInteraction₂ εOpen₁ εOpen₂ : ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hOpen : εOpen₁ ≤ εOpen₂) :
    bcsTotalError εInteraction₁ (fun _ : Fin 1 => εOpen₁) ≤ εInteraction₂ + εOpen₂ := by
  calc
    bcsTotalError εInteraction₁ (fun _ : Fin 1 => εOpen₁)
        ≤ bcsTotalError εInteraction₂ (fun _ : Fin 1 => εOpen₂) :=
      bcsTotalError_mono hInteraction (fun _ => hOpen)
    _ = εInteraction₂ + εOpen₂ :=
      bcsTotalError_one εInteraction₂ (fun _ : Fin 1 => εOpen₂)

/-- Relax the interaction and both opening-batch budgets for the total-error append split. -/
theorem bcsTotalError_append_mono_error {m n : ℕ}
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    {εLeft₁ εLeft₂ : Fin m → ℝ≥0} {εRight₁ εRight₂ : Fin n → ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hLeft : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight : ∀ i, εRight₁ i ≤ εRight₂ i) :
    bcsTotalError εInteraction₁ (Fin.append εLeft₁ εRight₁)
      ≤ bcsTotalError εInteraction₂ εLeft₂ + ∑ i, εRight₂ i := by
  calc
    bcsTotalError εInteraction₁ (Fin.append εLeft₁ εRight₁)
        = bcsTotalError εInteraction₁ εLeft₁ + ∑ i, εRight₁ i :=
          bcsTotalError_append εInteraction₁ εLeft₁ εRight₁
    _ ≤ bcsTotalError εInteraction₂ εLeft₂ + ∑ i, εRight₂ i :=
      add_le_add (bcsTotalError_mono hInteraction hLeft)
        (Finset.sum_le_sum fun i _ => hRight i)

/-- Relax the interaction and both opening-batch budgets while keeping the target as the full
appended BCS total error. This is the consumer-facing companion to
`bcsTotalError_append_mono_error` when callers do not want to split the appended schedule. -/
theorem bcsTotalError_append_full_mono_error {m n : ℕ}
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    {εLeft₁ εLeft₂ : Fin m → ℝ≥0} {εRight₁ εRight₂ : Fin n → ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hLeft : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight : ∀ i, εRight₁ i ≤ εRight₂ i) :
    bcsTotalError εInteraction₁ (Fin.append εLeft₁ εRight₁)
      ≤ bcsTotalError εInteraction₂ (Fin.append εLeft₂ εRight₂) := by
  refine bcsTotalError_mono hInteraction ?_
  intro i
  cases i using Fin.addCases with
  | left i => simpa [Fin.append] using hLeft i
  | right i => simpa [Fin.append] using hRight i

/-- Relax the interaction and opening budgets for the left-empty total-error append split. -/
theorem bcsTotalError_append_zero_left_mono_error {m : ℕ}
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hOpen : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInteraction₁ (Fin.append (Fin.elim0 : Fin 0 → ℝ≥0) εOpen₁)
      ≤ bcsTotalError εInteraction₂ εOpen₂ := by
  calc
    bcsTotalError εInteraction₁ (Fin.append (Fin.elim0 : Fin 0 → ℝ≥0) εOpen₁)
        = bcsTotalError εInteraction₁ εOpen₁ :=
          bcsTotalError_append_zero_left εInteraction₁ εOpen₁
    _ ≤ bcsTotalError εInteraction₂ εOpen₂ :=
      bcsTotalError_mono hInteraction hOpen

/-- Relax the interaction and opening budgets for the right-empty total-error append split. -/
theorem bcsTotalError_append_zero_right_mono_error {m : ℕ}
    {εInteraction₁ εInteraction₂ : ℝ≥0}
    {εOpen₁ εOpen₂ : Fin m → ℝ≥0}
    (hInteraction : εInteraction₁ ≤ εInteraction₂)
    (hOpen : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    bcsTotalError εInteraction₁ (Fin.append εOpen₁ (Fin.elim0 : Fin 0 → ℝ≥0))
      ≤ bcsTotalError εInteraction₂ εOpen₂ := by
  calc
    bcsTotalError εInteraction₁ (Fin.append εOpen₁ (Fin.elim0 : Fin 0 → ℝ≥0))
        = bcsTotalError εInteraction₁ εOpen₁ :=
          bcsTotalError_append_zero_right εInteraction₁ εOpen₁
    _ ≤ bcsTotalError εInteraction₂ εOpen₂ :=
      bcsTotalError_mono hInteraction hOpen

/-! ## 2. The abstract union-bound accounting

We model "probability of a bad event" abstractly as an `ℝ≥0`-valued functional
`P` on events, satisfying only the two facts a union bound needs:
  * monotonicity (`P` of a smaller event ≤ `P` of a bigger event), and
  * subadditivity over a `cons` (the union bound for two events).

We then show: if the interaction-phase failure event has `P ≤ εInteraction`, and
the `i`-th opening-failure event has `P ≤ εOpen i`, then the overall BCS failure
(modelled as the union of all these events) has `P ≤ bcsTotalError εInteraction
εOpen`. This is precisely the soundness-composition accounting, abstracted away
from the specific probability monad so it is provable today.

`E` is the (opaque) type of events; `union` is binary event union; `none` is the
empty (never-fires) event. -/

variable {E : Type*}

/-- The structure of a probability functional that admits a union bound:
a monotone, finitely-subadditive `ℝ≥0`-valued measure of "bad events". This is
the minimal interface that the ArkLib `Pr[·]`/`probEvent` functional satisfies
(`probEvent_mono` and finite union subadditivity), recorded abstractly so the
accounting below is provable without the probability monad. -/
structure UnionBoundPr (E : Type*) where
  /-- Probability of an event. -/
  pr : E → ℝ≥0
  /-- The empty event. -/
  empty : E
  /-- Binary union of events. -/
  union : E → E → E
  /-- The empty event never fires. -/
  pr_empty : pr empty = 0
  /-- Union bound for two events (finite subadditivity). -/
  pr_union_le : ∀ a b, pr (union a b) ≤ pr a + pr b

/-- Union of a finite family of events, folded over `Fin m`. -/
def UnionBoundPr.unionFin (μ : UnionBoundPr E) :
    ∀ {m : ℕ}, (Fin m → E) → E
  | 0, _ => μ.empty
  | _ + 1, f => μ.union (f 0) (μ.unionFin (fun i => f i.succ))

/-- Finite union bound: the probability of a union of `m` events is at most the
sum of their probabilities. This is the standard union bound, proved by induction
on `m` from binary subadditivity. It is the probabilistic core of the BCS
soundness accounting over the `m` per-message opening proofs. -/
theorem UnionBoundPr.pr_unionFin_le (μ : UnionBoundPr E) :
    ∀ {m : ℕ} (f : Fin m → E), μ.pr (μ.unionFin f) ≤ ∑ i, μ.pr (f i) := by
  intro m
  induction m with
  | zero =>
      intro f
      simp [UnionBoundPr.unionFin, μ.pr_empty]
  | succ m ih =>
      intro f
      calc
        μ.pr (μ.unionFin f)
            = μ.pr (μ.union (f 0) (μ.unionFin (fun i : Fin m => f i.succ))) := rfl
        _ ≤ μ.pr (f 0) + μ.pr (μ.unionFin (fun i : Fin m => f i.succ)) :=
              μ.pr_union_le _ _
        _ ≤ μ.pr (f 0) + ∑ i : Fin m, μ.pr (f i.succ) := by
              gcongr
              exact ih (fun i : Fin m => f i.succ)
        _ = ∑ i, μ.pr (f i) := by rw [Fin.sum_univ_succ]

/-- **BCS soundness-error union bound (accounting form).**

Given a probability functional with a union bound, an interaction-phase bad event
`badInteraction` bounded by `εInteraction`, and per-message opening-failure events
`badOpen i` each bounded by `εOpen i`, the union of all bad events is bounded by
the BCS total error `εInteraction + Σ εOpen`.

This is the `ℝ≥0` skeleton of "IOP-soundness + per-message binding ⟹ argument
soundness": the probabilistic composition reduces to exactly this accounting once
each phase's failure probability is controlled. It is fully proved (no sorry),
using only monotonicity + subadditivity. -/
theorem bcs_union_bound {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ bcsTotalError εInteraction εOpen := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ μ.pr badInteraction + μ.pr (μ.unionFin badOpen) := μ.pr_union_le _ _
    _ ≤ εInteraction + ∑ i, μ.pr (badOpen i) :=
          add_le_add hInteraction (μ.pr_unionFin_le badOpen)
    _ ≤ εInteraction + ∑ i, εOpen i := by
          gcongr with i
          exact hOpen i
    _ = bcsTotalError εInteraction εOpen := rfl

/-- No-opening union bound. This is the probabilistic base case matching
`bcsTotalError_zero`: with no committed messages, the bad event is bounded by
the interaction-phase error alone. -/
theorem bcs_union_bound_zero (μ : UnionBoundPr E)
    (badInteraction : E) (εInteraction : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.elim0 : Fin 0 → E)))
      ≤ εInteraction := by
  have h := bcs_union_bound (m := 0) μ badInteraction
    (Fin.elim0 : Fin 0 → E) εInteraction (Fin.elim0 : Fin 0 → ℝ≥0)
    hInteraction (fun i => Fin.elim0 i)
  simpa [bcsTotalError] using h

/-- One-more-opening union-bound recurrence. This is the probabilistic companion
to `bcsTotalError_succ`: peeling the first opening event contributes its opening
error, then recurses on the remaining opening schedule. -/
theorem bcs_union_bound_succ {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin (m + 1) → E)
    (εInteraction : ℝ≥0) (εOpen : Fin (m + 1) → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εOpen 0 + bcsTotalError εInteraction (fun i : Fin m => εOpen i.succ) := by
  have h := bcs_union_bound (m := m + 1) μ badInteraction badOpen εInteraction εOpen
    hInteraction hOpen
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ bcsTotalError εInteraction εOpen := h
    _ = εOpen 0 + bcsTotalError εInteraction (fun i : Fin m => εOpen i.succ) :=
        bcsTotalError_succ εInteraction εOpen

/-- Batched-opening union bound for a left/right split of the committed-message openings.

This is the probabilistic companion to `bcsTotalError_append`: if the opening failures have been
grouped into two consecutive batches, the union of the appended opening failures is bounded by the
left batch's BCS total plus the right batch's opening-error sum. -/
theorem bcs_union_bound_append {m n : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badLeft : Fin m → E) (badRight : Fin n → E)
    (εInteraction : ℝ≥0) (εLeft : Fin m → ℝ≥0) (εRight : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight i) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.append badLeft badRight)))
      ≤ bcsTotalError εInteraction εLeft + ∑ i, εRight i := by
  have hOpen : ∀ i : Fin (m + n),
      μ.pr ((Fin.append badLeft badRight) i) ≤ (Fin.append εLeft εRight) i := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa using hLeft i
    | right i => simpa using hRight i
  have h := bcs_union_bound (m := m + n) μ badInteraction
    (Fin.append badLeft badRight) εInteraction (Fin.append εLeft εRight)
    hInteraction hOpen
  simpa [bcsTotalError_append] using h

/-- Left-empty batched-opening union bound. This is the probabilistic corollary matching
`bcsTotalError_append_zero_left`: appending no left opening failures leaves the ordinary BCS
union-bound target unchanged. -/
theorem bcs_union_bound_append_zero_left {n : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin n → E)
    (εInteraction : ℝ≥0) (εOpen : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen)))
      ≤ bcsTotalError εInteraction εOpen := by
  have h := bcs_union_bound_append (m := 0) (n := n) μ badInteraction
    (Fin.elim0 : Fin 0 → E) badOpen εInteraction (Fin.elim0 : Fin 0 → ℝ≥0) εOpen
    hInteraction (fun i => Fin.elim0 i) hOpen
  simpa [bcsTotalError] using h

/-- Right-empty batched-opening union bound. This is the probabilistic corollary matching
`bcsTotalError_append_zero_right`: appending no right opening failures leaves the ordinary BCS
union-bound target unchanged. -/
theorem bcs_union_bound_append_zero_right {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E))))
      ≤ bcsTotalError εInteraction εOpen := by
  have h := bcs_union_bound_append (m := m) (n := 0) μ badInteraction
    badOpen (Fin.elim0 : Fin 0 → E) εInteraction εOpen (Fin.elim0 : Fin 0 → ℝ≥0)
    hInteraction hOpen (fun i => Fin.elim0 i)
  simpa [bcsTotalError] using h

/-- Relax the interaction/opening budgets after applying the generic BCS union bound. This is the
error-accounting wrapper used when phase-local analyses prove sharper bounds than the final
compiler budget records. -/
theorem bcs_union_bound_mono_error {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ bcsTotalError εInteraction₂ εOpen₂ :=
  le_trans
    (bcs_union_bound μ badInteraction badOpen εInteraction₁ εOpen₁ hInteraction hOpen)
    (bcsTotalError_mono hInteraction_mono hOpen_mono)

/-- Relax the interaction budget for the no-opening generic BCS union-bound base case. -/
theorem bcs_union_bound_zero_mono_error (μ : UnionBoundPr E)
    (badInteraction : E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.elim0 : Fin 0 → E)))
      ≤ εInteraction₂ :=
  le_trans
    (bcs_union_bound_zero μ badInteraction εInteraction₁ hInteraction)
    hInteraction_mono

/-- Relax the interaction and opening budgets for the single-opening generic BCS union-bound
base case. -/
theorem bcs_union_bound_one_mono_error (μ : UnionBoundPr E)
    (badInteraction badOpen : E)
    (εInteraction₁ εInteraction₂ εOpen₁ εOpen₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : μ.pr badOpen ≤ εOpen₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : εOpen₁ ≤ εOpen₂) :
    μ.pr (μ.union badInteraction (μ.unionFin (fun _ : Fin 1 => badOpen)))
      ≤ εInteraction₂ + εOpen₂ := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin (fun _ : Fin 1 => badOpen)))
        ≤ bcsTotalError εInteraction₂ (fun _ : Fin 1 => εOpen₂) :=
      bcs_union_bound_mono_error μ badInteraction (fun _ : Fin 1 => badOpen)
        εInteraction₁ εInteraction₂ (fun _ : Fin 1 => εOpen₁) (fun _ : Fin 1 => εOpen₂)
        hInteraction (fun _ => hOpen) hInteraction_mono (fun _ => hOpen_mono)
    _ = εInteraction₂ + εOpen₂ :=
      bcsTotalError_one εInteraction₂ (fun _ : Fin 1 => εOpen₂)

/-- Relax the interaction and opening budgets for the one-more-opening generic union-bound
recurrence. -/
theorem bcs_union_bound_succ_mono_error {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin (m + 1) → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin (m + 1) → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εOpen₂ 0 + bcsTotalError εInteraction₂ (fun i : Fin m => εOpen₂ i.succ) := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ bcsTotalError εInteraction₂ εOpen₂ :=
      bcs_union_bound_mono_error μ badInteraction badOpen
        εInteraction₁ εInteraction₂ εOpen₁ εOpen₂
        hInteraction hOpen hInteraction_mono hOpen_mono
    _ = εOpen₂ 0 + bcsTotalError εInteraction₂ (fun i : Fin m => εOpen₂ i.succ) :=
        bcsTotalError_succ εInteraction₂ εOpen₂

/-- Relax the interaction and both opening-batch budgets after applying the batched BCS union
bound. -/
theorem bcs_union_bound_append_mono_error {m n : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badLeft : Fin m → E) (badRight : Fin n → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εLeft₁ εLeft₂ : Fin m → ℝ≥0) (εRight₁ εRight₂ : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft₁ i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hLeft_mono : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight_mono : ∀ i, εRight₁ i ≤ εRight₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.append badLeft badRight)))
      ≤ bcsTotalError εInteraction₂ εLeft₂ + ∑ i, εRight₂ i := by
  refine le_trans
    (bcs_union_bound_append μ badInteraction badLeft badRight
      εInteraction₁ εLeft₁ εRight₁ hInteraction hLeft hRight) ?_
  exact add_le_add
    (bcsTotalError_mono hInteraction_mono hLeft_mono)
    (Finset.sum_le_sum fun i _ => hRight_mono i)

/-- Relax the interaction and both opening-batch budgets after applying the batched BCS union
bound, keeping the final target as the full appended BCS total error. -/
theorem bcs_union_bound_append_full_mono_error {m n : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badLeft : Fin m → E) (badRight : Fin n → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εLeft₁ εLeft₂ : Fin m → ℝ≥0) (εRight₁ εRight₂ : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft₁ i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hLeft_mono : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight_mono : ∀ i, εRight₁ i ≤ εRight₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.append badLeft badRight)))
      ≤ bcsTotalError εInteraction₂ (Fin.append εLeft₂ εRight₂) := by
  have hOpen : ∀ i : Fin (m + n),
      μ.pr ((Fin.append badLeft badRight) i) ≤ (Fin.append εLeft₁ εRight₁) i := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa [Fin.append] using hLeft i
    | right i => simpa [Fin.append] using hRight i
  exact bcs_union_bound_mono_error μ badInteraction (Fin.append badLeft badRight)
    εInteraction₁ εInteraction₂ (Fin.append εLeft₁ εRight₁)
    (Fin.append εLeft₂ εRight₂) hInteraction hOpen hInteraction_mono (by
      intro i
      cases i using Fin.addCases with
      | left i => simpa [Fin.append] using hLeft_mono i
      | right i => simpa [Fin.append] using hRight_mono i)

/-- Relax the interaction and opening budgets for the left-empty generic append split. -/
theorem bcs_union_bound_append_zero_left_mono_error {n : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin n → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen)))
      ≤ bcsTotalError εInteraction₂ εOpen₂ := by
  have h := bcs_union_bound_append_mono_error (m := 0) (n := n) μ badInteraction
    (Fin.elim0 : Fin 0 → E) badOpen
    εInteraction₁ εInteraction₂ (Fin.elim0 : Fin 0 → ℝ≥0)
    (Fin.elim0 : Fin 0 → ℝ≥0) εOpen₁ εOpen₂ hInteraction
    (fun i => Fin.elim0 i) hOpen hInteraction_mono (fun i => Fin.elim0 i) hOpen_mono
  simpa [bcsTotalError] using h

/-- Relax the interaction and opening budgets for the right-empty generic append split. -/
theorem bcs_union_bound_append_zero_right_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E))))
      ≤ bcsTotalError εInteraction₂ εOpen₂ := by
  have h := bcs_union_bound_append_mono_error (m := m) (n := 0) μ badInteraction
    badOpen (Fin.elim0 : Fin 0 → E)
    εInteraction₁ εInteraction₂ εOpen₁ εOpen₂
    (Fin.elim0 : Fin 0 → ℝ≥0) (Fin.elim0 : Fin 0 → ℝ≥0) hInteraction
    hOpen (fun i => Fin.elim0 i) hInteraction_mono hOpen_mono (fun i => Fin.elim0 i)
  simpa [bcsTotalError] using h

/-- Opening-phase union bound. If each per-message opening failure is bounded by its local
opening error, then the composite opening-failure event is bounded by the sum of those local
errors. This isolates the query-log opening phase from the interaction-phase event. -/
theorem bcs_opening_union_bound {m : ℕ} (μ : UnionBoundPr E)
    (badOpen : Fin m → E) (εOpen : Fin m → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.unionFin badOpen) ≤ ∑ i, εOpen i := by
  calc
    μ.pr (μ.unionFin badOpen) ≤ ∑ i, μ.pr (badOpen i) :=
      μ.pr_unionFin_le badOpen
    _ ≤ ∑ i, εOpen i := by
      exact Finset.sum_le_sum fun i _ => hOpen i

/-- Empty opening-phase union bound. With no per-message openings, the composite opening failure
is empty and has probability at most zero. -/
theorem bcs_opening_union_bound_zero (μ : UnionBoundPr E) :
    μ.pr (μ.unionFin (Fin.elim0 : Fin 0 → E)) ≤ 0 := by
  simp [UnionBoundPr.unionFin, μ.pr_empty]

/-- Single-opening opening-phase union bound. With one per-message opening failure, the composite
opening failure is bounded by that one local opening budget. -/
theorem bcs_opening_union_bound_one (μ : UnionBoundPr E)
    (badOpen : E) (εOpen : ℝ≥0)
    (hOpen : μ.pr badOpen ≤ εOpen) :
    μ.pr (μ.unionFin (fun _ : Fin 1 => badOpen)) ≤ εOpen := by
  have h := bcs_opening_union_bound μ (fun _ : Fin 1 => badOpen)
    (fun _ : Fin 1 => εOpen) (fun _ => hOpen)
  simpa using h

/-- One-more-opening recurrence for the opening-phase union bound. Peeling the first opening
failure contributes its local opening error, then recurses on the remaining opening schedule. -/
theorem bcs_opening_union_bound_succ {m : ℕ} (μ : UnionBoundPr E)
    (badOpen : Fin (m + 1) → E) (εOpen : Fin (m + 1) → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.unionFin badOpen) ≤ εOpen 0 + ∑ i : Fin m, εOpen i.succ := by
  calc
    μ.pr (μ.unionFin badOpen) ≤ ∑ i : Fin (m + 1), εOpen i :=
      bcs_opening_union_bound μ badOpen εOpen hOpen
    _ = εOpen 0 + ∑ i : Fin m, εOpen i.succ := by
      rw [Fin.sum_univ_succ]

/-- Relax the opening budget for the single-opening opening-phase union bound. -/
theorem bcs_opening_union_bound_one_mono_error (μ : UnionBoundPr E)
    (badOpen : E) (εOpen₁ εOpen₂ : ℝ≥0)
    (hOpen : μ.pr badOpen ≤ εOpen₁)
    (hOpen_mono : εOpen₁ ≤ εOpen₂) :
    μ.pr (μ.unionFin (fun _ : Fin 1 => badOpen)) ≤ εOpen₂ :=
  le_trans
    (bcs_opening_union_bound_one μ badOpen εOpen₁ hOpen)
    hOpen_mono

/-- Relax the per-opening budgets for the one-more-opening recurrence at the opening-phase
union-bound surface. -/
theorem bcs_opening_union_bound_succ_mono_error {m : ℕ} (μ : UnionBoundPr E)
    (badOpen : Fin (m + 1) → E)
    (εOpen₁ εOpen₂ : Fin (m + 1) → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.unionFin badOpen) ≤ εOpen₂ 0 + ∑ i : Fin m, εOpen₂ i.succ := by
  calc
    μ.pr (μ.unionFin badOpen) ≤ εOpen₁ 0 + ∑ i : Fin m, εOpen₁ i.succ :=
      bcs_opening_union_bound_succ μ badOpen εOpen₁ hOpen
    _ ≤ εOpen₂ 0 + ∑ i : Fin m, εOpen₂ i.succ := by
      exact add_le_add (hOpen_mono 0) (Finset.sum_le_sum fun i _ => hOpen_mono i.succ)

/-- Left/right split for the opening-phase union bound. This isolates the composite opening
failure when the query-log openings are grouped into two consecutive batches. -/
theorem bcs_opening_union_bound_append {m n : ℕ} (μ : UnionBoundPr E)
    (badLeft : Fin m → E) (badRight : Fin n → E)
    (εLeft : Fin m → ℝ≥0) (εRight : Fin n → ℝ≥0)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight i) :
    μ.pr (μ.unionFin (Fin.append badLeft badRight))
      ≤ (∑ i, εLeft i) + ∑ i, εRight i := by
  have hOpen : ∀ i : Fin (m + n),
      μ.pr ((Fin.append badLeft badRight) i) ≤ (Fin.append εLeft εRight) i := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa using hLeft i
    | right i => simpa using hRight i
  calc
    μ.pr (μ.unionFin (Fin.append badLeft badRight))
        ≤ ∑ i : Fin (m + n), (Fin.append εLeft εRight) i :=
      bcs_opening_union_bound μ (Fin.append badLeft badRight)
        (Fin.append εLeft εRight) hOpen
    _ = (∑ i, εLeft i) + ∑ i, εRight i := by
      rw [Fin.sum_univ_add]
      simp [Fin.append]

/-- Relax both opening-batch budgets after proving the left/right opening-phase split. -/
theorem bcs_opening_union_bound_append_mono_error {m n : ℕ}
    (μ : UnionBoundPr E) (badLeft : Fin m → E) (badRight : Fin n → E)
    (εLeft₁ εLeft₂ : Fin m → ℝ≥0) (εRight₁ εRight₂ : Fin n → ℝ≥0)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft₁ i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight₁ i)
    (hLeft_mono : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight_mono : ∀ i, εRight₁ i ≤ εRight₂ i) :
    μ.pr (μ.unionFin (Fin.append badLeft badRight))
      ≤ (∑ i, εLeft₂ i) + ∑ i, εRight₂ i :=
  le_trans
    (bcs_opening_union_bound_append μ badLeft badRight εLeft₁ εRight₁ hLeft hRight)
    (add_le_add
      (Finset.sum_le_sum fun i _ => hLeft_mono i)
      (Finset.sum_le_sum fun i _ => hRight_mono i))

/-- Left-empty opening-phase split. Appending no left opening failures leaves the ordinary
opening-union bound target unchanged. -/
theorem bcs_opening_union_bound_append_zero_left {n : ℕ}
    (μ : UnionBoundPr E) (badOpen : Fin n → E) (εOpen : Fin n → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen))
      ≤ ∑ i, εOpen i := by
  have h := bcs_opening_union_bound_append (m := 0) (n := n) μ
    (Fin.elim0 : Fin 0 → E) badOpen (Fin.elim0 : Fin 0 → ℝ≥0) εOpen
    (fun i => Fin.elim0 i) hOpen
  simpa using h

/-- Right-empty opening-phase split. Appending no right opening failures leaves the ordinary
opening-union bound target unchanged. -/
theorem bcs_opening_union_bound_append_zero_right {m : ℕ}
    (μ : UnionBoundPr E) (badOpen : Fin m → E) (εOpen : Fin m → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E)))
      ≤ ∑ i, εOpen i := by
  have h := bcs_opening_union_bound_append (m := m) (n := 0) μ
    badOpen (Fin.elim0 : Fin 0 → E) εOpen (Fin.elim0 : Fin 0 → ℝ≥0)
    hOpen (fun i => Fin.elim0 i)
  simpa using h

/-- Relax the opening budget for the left-empty opening-phase split. -/
theorem bcs_opening_union_bound_append_zero_left_mono_error {n : ℕ}
    (μ : UnionBoundPr E) (badOpen : Fin n → E)
    (εOpen₁ εOpen₂ : Fin n → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen))
      ≤ ∑ i, εOpen₂ i := by
  have h := bcs_opening_union_bound_append_mono_error (m := 0) (n := n) μ
    (Fin.elim0 : Fin 0 → E) badOpen
    (Fin.elim0 : Fin 0 → ℝ≥0) (Fin.elim0 : Fin 0 → ℝ≥0) εOpen₁ εOpen₂
    (fun i => Fin.elim0 i) hOpen (fun i => Fin.elim0 i) hOpen_mono
  simpa using h

/-- Relax the opening budget for the right-empty opening-phase split. -/
theorem bcs_opening_union_bound_append_zero_right_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badOpen : Fin m → E)
    (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E)))
      ≤ ∑ i, εOpen₂ i := by
  have h := bcs_opening_union_bound_append_mono_error (m := m) (n := 0) μ
    badOpen (Fin.elim0 : Fin 0 → E)
    εOpen₁ εOpen₂ (Fin.elim0 : Fin 0 → ℝ≥0) (Fin.elim0 : Fin 0 → ℝ≥0)
    hOpen (fun i => Fin.elim0 i) hOpen_mono (fun i => Fin.elim0 i)
  simpa using h

/-- Relax the per-message opening budgets after proving the composite opening-union bound. -/
theorem bcs_opening_union_bound_mono_error {m : ℕ} (μ : UnionBoundPr E)
    (badOpen : Fin m → E) (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.unionFin badOpen) ≤ ∑ i, εOpen₂ i := by
  exact le_trans
    (bcs_opening_union_bound μ badOpen εOpen₁ hOpen)
    (Finset.sum_le_sum fun i _ => hOpen_mono i)

/-- Two-phase BCS append accounting when the opening phase is already packaged as the composite
union of all per-message opening failures. This is the direct bridge from a query-log opening
union bound to the interaction-plus-opening compiler budget. -/
theorem bcs_append_accounting_of_opening_bound {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction εOpenTotal : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpenTotal : μ.pr (μ.unionFin badOpen) ≤ εOpenTotal) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction + εOpenTotal := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ μ.pr badInteraction + μ.pr (μ.unionFin badOpen) := μ.pr_union_le _ _
    _ ≤ εInteraction + εOpenTotal := add_le_add hInteraction hOpenTotal

/-- Relax the interaction and composite-opening budgets after the opening phase has already been
packaged as a single query-log failure event. -/
theorem bcs_append_accounting_of_opening_bound_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction₁ εInteraction₂ εOpenTotal₁ εOpenTotal₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpenTotal : μ.pr (μ.unionFin badOpen) ≤ εOpenTotal₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpenTotal_mono : εOpenTotal₁ ≤ εOpenTotal₂) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction₂ + εOpenTotal₂ :=
  le_trans
    (bcs_append_accounting_of_opening_bound μ badInteraction badOpen
      εInteraction₁ εOpenTotal₁ hInteraction hOpenTotal)
    (add_le_add hInteraction_mono hOpenTotal_mono)

/-- Two-phase BCS append accounting where the composite opening phase is generated from
per-message opening failures and their local error bounds. -/
theorem bcs_append_accounting_of_opening_batch {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction + ∑ i, εOpen i :=
  bcs_append_accounting_of_opening_bound μ badInteraction badOpen
    εInteraction (∑ i, εOpen i) hInteraction
    (bcs_opening_union_bound μ badOpen εOpen hOpen)

/-- Relax the interaction and per-message opening budgets after packaging the opening phase as a
single composite query-log failure event. -/
theorem bcs_append_accounting_of_opening_batch_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction₂ + ∑ i, εOpen₂ i :=
  bcs_append_accounting_of_opening_bound μ badInteraction badOpen
    εInteraction₂ (∑ i, εOpen₂ i)
    (le_trans hInteraction hInteraction_mono)
    (bcs_opening_union_bound_mono_error μ badOpen εOpen₁ εOpen₂
      hOpen hOpen_mono)

/-- Append accounting with an empty opening batch. The interaction failure unioned with the empty
opening phase is bounded by the interaction-phase budget alone. -/
theorem bcs_append_accounting_of_opening_zero (μ : UnionBoundPr E)
    (badInteraction : E) (εInteraction : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.elim0 : Fin 0 → E)))
      ≤ εInteraction := by
  have h := bcs_append_accounting_of_opening_bound μ badInteraction
    (Fin.elim0 : Fin 0 → E) εInteraction 0 hInteraction
    (bcs_opening_union_bound_zero μ)
  simpa using h

/-- Append accounting with a single per-message opening failure. This is the
interaction-plus-opening companion to `bcs_opening_union_bound_one`. -/
theorem bcs_append_accounting_of_opening_one (μ : UnionBoundPr E)
    (badInteraction badOpen : E) (εInteraction εOpen : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : μ.pr badOpen ≤ εOpen) :
    μ.pr (μ.union badInteraction (μ.unionFin (fun _ : Fin 1 => badOpen)))
      ≤ εInteraction + εOpen :=
  bcs_append_accounting_of_opening_bound μ badInteraction (fun _ : Fin 1 => badOpen)
    εInteraction εOpen hInteraction
    (bcs_opening_union_bound_one μ badOpen εOpen hOpen)

/-- One-more-opening recurrence at the interaction-plus-opening append-accounting surface. Peeling
the first opening failure contributes its local opening budget and recurses over the remaining
opening schedule. -/
theorem bcs_append_accounting_of_opening_succ {m : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badOpen : Fin (m + 1) → E)
    (εInteraction : ℝ≥0) (εOpen : Fin (m + 1) → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction + (εOpen 0 + ∑ i : Fin m, εOpen i.succ) := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ εInteraction + ∑ i : Fin (m + 1), εOpen i :=
      bcs_append_accounting_of_opening_batch μ badInteraction badOpen
        εInteraction εOpen hInteraction hOpen
    _ = εInteraction + (εOpen 0 + ∑ i : Fin m, εOpen i.succ) := by
      rw [Fin.sum_univ_succ]

/-- Left/right opening-batch split at the interaction-plus-opening append-accounting surface. This
packages the composite opening phase as two consecutive query-log opening batches. -/
theorem bcs_append_accounting_of_opening_append {m n : ℕ} (μ : UnionBoundPr E)
    (badInteraction : E) (badLeft : Fin m → E) (badRight : Fin n → E)
    (εInteraction : ℝ≥0) (εLeft : Fin m → ℝ≥0) (εRight : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight i) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.append badLeft badRight)))
      ≤ εInteraction + ((∑ i, εLeft i) + ∑ i, εRight i) :=
  bcs_append_accounting_of_opening_bound μ badInteraction
    (Fin.append badLeft badRight) εInteraction ((∑ i, εLeft i) + ∑ i, εRight i)
    hInteraction (bcs_opening_union_bound_append μ badLeft badRight
      εLeft εRight hLeft hRight)

/-- Relax the interaction budget for the empty opening-batch append-accounting base case. -/
theorem bcs_append_accounting_of_opening_zero_mono_error (μ : UnionBoundPr E)
    (badInteraction : E) (εInteraction₁ εInteraction₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.elim0 : Fin 0 → E)))
      ≤ εInteraction₂ :=
  le_trans
    (bcs_append_accounting_of_opening_zero μ badInteraction εInteraction₁ hInteraction)
    hInteraction_mono

/-- Relax the interaction and opening budgets for the single-opening append-accounting surface. -/
theorem bcs_append_accounting_of_opening_one_mono_error (μ : UnionBoundPr E)
    (badInteraction badOpen : E)
    (εInteraction₁ εInteraction₂ εOpen₁ εOpen₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : μ.pr badOpen ≤ εOpen₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : εOpen₁ ≤ εOpen₂) :
    μ.pr (μ.union badInteraction (μ.unionFin (fun _ : Fin 1 => badOpen)))
      ≤ εInteraction₂ + εOpen₂ :=
  le_trans
    (bcs_append_accounting_of_opening_one μ badInteraction badOpen
      εInteraction₁ εOpen₁ hInteraction hOpen)
    (add_le_add hInteraction_mono hOpen_mono)

/-- Relax the interaction and per-opening budgets for the one-more-opening append-accounting
recurrence. -/
theorem bcs_append_accounting_of_opening_succ_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin (m + 1) → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin (m + 1) → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
      ≤ εInteraction₂ + (εOpen₂ 0 + ∑ i : Fin m, εOpen₂ i.succ) := by
  calc
    μ.pr (μ.union badInteraction (μ.unionFin badOpen))
        ≤ εInteraction₂ + ∑ i : Fin (m + 1), εOpen₂ i :=
      bcs_append_accounting_of_opening_batch_mono_error μ badInteraction badOpen
        εInteraction₁ εInteraction₂ εOpen₁ εOpen₂
        hInteraction hOpen hInteraction_mono hOpen_mono
    _ = εInteraction₂ + (εOpen₂ 0 + ∑ i : Fin m, εOpen₂ i.succ) := by
      rw [Fin.sum_univ_succ]

/-- Relax the interaction and both opening-batch budgets for the left/right opening split at the
append-accounting surface. -/
theorem bcs_append_accounting_of_opening_append_mono_error {m n : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badLeft : Fin m → E)
    (badRight : Fin n → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εLeft₁ εLeft₂ : Fin m → ℝ≥0) (εRight₁ εRight₂ : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hLeft : ∀ i, μ.pr (badLeft i) ≤ εLeft₁ i)
    (hRight : ∀ i, μ.pr (badRight i) ≤ εRight₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hLeft_mono : ∀ i, εLeft₁ i ≤ εLeft₂ i)
    (hRight_mono : ∀ i, εRight₁ i ≤ εRight₂ i) :
    μ.pr (μ.union badInteraction (μ.unionFin (Fin.append badLeft badRight)))
      ≤ εInteraction₂ + ((∑ i, εLeft₂ i) + ∑ i, εRight₂ i) := by
  refine bcs_append_accounting_of_opening_bound μ badInteraction
    (Fin.append badLeft badRight) εInteraction₂
    ((∑ i, εLeft₂ i) + ∑ i, εRight₂ i)
    (le_trans hInteraction hInteraction_mono) ?_
  exact le_trans
    (bcs_opening_union_bound_append μ badLeft badRight εLeft₁ εRight₁ hLeft hRight)
    (add_le_add
      (Finset.sum_le_sum fun i _ => hLeft_mono i)
      (Finset.sum_le_sum fun i _ => hRight_mono i))

/-- Left-empty opening-batch split at the interaction-plus-opening append-accounting surface. -/
theorem bcs_append_accounting_of_opening_append_zero_left {n : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin n → E)
    (εInteraction : ℝ≥0) (εOpen : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen)))
      ≤ εInteraction + ∑ i, εOpen i := by
  have h := bcs_append_accounting_of_opening_append (m := 0) (n := n) μ
    badInteraction (Fin.elim0 : Fin 0 → E) badOpen εInteraction
    (Fin.elim0 : Fin 0 → ℝ≥0) εOpen hInteraction (fun i => Fin.elim0 i) hOpen
  simpa using h

/-- Right-empty opening-batch split at the interaction-plus-opening append-accounting surface. -/
theorem bcs_append_accounting_of_opening_append_zero_right {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction : ℝ≥0) (εOpen : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E))))
      ≤ εInteraction + ∑ i, εOpen i := by
  have h := bcs_append_accounting_of_opening_append (m := m) (n := 0) μ
    badInteraction badOpen (Fin.elim0 : Fin 0 → E) εInteraction
    εOpen (Fin.elim0 : Fin 0 → ℝ≥0) hInteraction hOpen (fun i => Fin.elim0 i)
  simpa using h

/-- Relax the interaction and opening budgets for the left-empty append-accounting split. -/
theorem bcs_append_accounting_of_opening_append_zero_left_mono_error {n : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin n → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin n → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append (Fin.elim0 : Fin 0 → E) badOpen)))
      ≤ εInteraction₂ + ∑ i, εOpen₂ i := by
  have h := bcs_append_accounting_of_opening_append_mono_error (m := 0) (n := n) μ
    badInteraction (Fin.elim0 : Fin 0 → E) badOpen
    εInteraction₁ εInteraction₂ (Fin.elim0 : Fin 0 → ℝ≥0)
    (Fin.elim0 : Fin 0 → ℝ≥0) εOpen₁ εOpen₂ hInteraction
    (fun i => Fin.elim0 i) hOpen hInteraction_mono (fun i => Fin.elim0 i) hOpen_mono
  simpa using h

/-- Relax the interaction and opening budgets for the right-empty append-accounting split. -/
theorem bcs_append_accounting_of_opening_append_zero_right_mono_error {m : ℕ}
    (μ : UnionBoundPr E) (badInteraction : E) (badOpen : Fin m → E)
    (εInteraction₁ εInteraction₂ : ℝ≥0)
    (εOpen₁ εOpen₂ : Fin m → ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : ∀ i, μ.pr (badOpen i) ≤ εOpen₁ i)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : ∀ i, εOpen₁ i ≤ εOpen₂ i) :
    μ.pr (μ.union badInteraction
        (μ.unionFin (Fin.append badOpen (Fin.elim0 : Fin 0 → E))))
      ≤ εInteraction₂ + ∑ i, εOpen₂ i := by
  have h := bcs_append_accounting_of_opening_append_mono_error (m := m) (n := 0) μ
    badInteraction badOpen (Fin.elim0 : Fin 0 → E)
    εInteraction₁ εInteraction₂ εOpen₁ εOpen₂
    (Fin.elim0 : Fin 0 → ℝ≥0) (Fin.elim0 : Fin 0 → ℝ≥0) hInteraction
    hOpen (fun i => Fin.elim0 i) hInteraction_mono hOpen_mono (fun i => Fin.elim0 i)
  simpa using h

/-! ## 3. Specialization to the two-phase `append` shape

The reduction-level `OracleReduction.BCSTransform` is literally
`Reduction.append interaction opening`. When the opening phase is treated as a
single composite reduction with error `εOpen`, the BCS error is the additive
`εInteraction + εOpen` of `Verifier.append_soundness`. We record that this is the
`m = 1` instance of the union bound, so the two-phase compiler error and the
`m`-message error are the same accounting. -/

/-- The two-phase `append` accounting: interaction error plus a single composite
opening error, matching `Verifier.append_soundness`'s additive
`soundnessError₁ + soundnessError₂`. -/
theorem bcs_append_accounting (μ : UnionBoundPr E)
    (badInteraction badOpen : E) (εInteraction εOpen : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction)
    (hOpen : μ.pr badOpen ≤ εOpen) :
    μ.pr (μ.union badInteraction (μ.union badOpen μ.empty))
      ≤ εInteraction + εOpen := by
  have h := bcs_union_bound (m := 1) μ badInteraction (fun _ => badOpen)
    εInteraction (fun _ => εOpen) hInteraction (fun _ => hOpen)
  -- `unionFin` on a `Fin 1` family is `union (badOpen) empty`; total error is
  -- `εInteraction + εOpen` by `bcsTotalError_one`.
  simpa [UnionBoundPr.unionFin, bcsTotalError_one] using h

/-- Relax the interaction and composite-opening budgets after applying the two-phase append
accounting. -/
theorem bcs_append_accounting_mono_error (μ : UnionBoundPr E)
    (badInteraction badOpen : E)
    (εInteraction₁ εInteraction₂ εOpen₁ εOpen₂ : ℝ≥0)
    (hInteraction : μ.pr badInteraction ≤ εInteraction₁)
    (hOpen : μ.pr badOpen ≤ εOpen₁)
    (hInteraction_mono : εInteraction₁ ≤ εInteraction₂)
    (hOpen_mono : εOpen₁ ≤ εOpen₂) :
    μ.pr (μ.union badInteraction (μ.union badOpen μ.empty))
      ≤ εInteraction₂ + εOpen₂ :=
  le_trans
    (bcs_append_accounting μ badInteraction badOpen εInteraction₁ εOpen₁ hInteraction hOpen)
    (add_le_add hInteraction_mono hOpen_mono)

/-- Consistency check: the two-phase total and the `m = 1` `bcsTotalError` agree,
so collapsing the opening phase to one composite reduction loses no accounting. -/
theorem bcs_two_phase_total_eq (εInteraction εOpen : ℝ≥0) :
    bcsTotalError εInteraction (fun _ : Fin 1 => εOpen) = εInteraction + εOpen :=
  bcsTotalError_one _ _

/-! ## 4. A concrete witness that `UnionBoundPr` is inhabited (sanity)

To confirm the abstract interface is not vacuous, we exhibit a concrete model:
events are `ℝ≥0` "weights", `pr` is the identity, union is `max` (which is
subadditive over `ℝ≥0`), and the empty event is `0`. This shows the hypotheses of
`bcs_union_bound` are simultaneously satisfiable, so the bound is non-vacuous. -/

/-- A trivial concrete `UnionBoundPr` on `ℝ≥0`: `pr = id`, `union = max`. -/
def maxUnionBoundPr : UnionBoundPr ℝ≥0 where
  pr := id
  empty := 0
  union := max
  pr_empty := rfl
  pr_union_le a b := by
    -- `max a b ≤ a + b` for nonnegative `a, b`.
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_add_right le_rfl

/-- Sanity: the union bound instantiates on the concrete model, so the abstract
accounting is not vacuous. -/
example (εInteraction : ℝ≥0) (εOpen : Fin 3 → ℝ≥0) :
    maxUnionBoundPr.pr
        (maxUnionBoundPr.union εInteraction (maxUnionBoundPr.unionFin εOpen))
      ≤ bcsTotalError εInteraction εOpen :=
  bcs_union_bound maxUnionBoundPr εInteraction εOpen εInteraction εOpen
    le_rfl (fun _ => le_rfl)

/-! ## Source audit -/

#print axioms bcsTotalError
#print axioms bcsTotalError_zero
#print axioms bcsTotalError_succ
#print axioms bcsTotalError_one
#print axioms bcsTotalError_append
#print axioms bcsTotalError_append_zero_left
#print axioms bcsTotalError_append_zero_right
#print axioms bcsTotalError_mono_interaction
#print axioms bcsTotalError_mono_open
#print axioms bcsTotalError_mono
#print axioms bcsTotalError_succ_mono_error
#print axioms bcsTotalError_zero_mono_error
#print axioms bcsTotalError_one_mono_error
#print axioms bcsTotalError_append_mono_error
#print axioms bcsTotalError_append_full_mono_error
#print axioms bcsTotalError_append_zero_left_mono_error
#print axioms bcsTotalError_append_zero_right_mono_error
#print axioms UnionBoundPr
#print axioms UnionBoundPr.unionFin
#print axioms UnionBoundPr.pr_unionFin_le
#print axioms bcs_union_bound
#print axioms bcs_union_bound_zero
#print axioms bcs_union_bound_succ
#print axioms bcs_union_bound_append
#print axioms bcs_union_bound_append_zero_left
#print axioms bcs_union_bound_append_zero_right
#print axioms bcs_union_bound_mono_error
#print axioms bcs_union_bound_zero_mono_error
#print axioms bcs_union_bound_one_mono_error
#print axioms bcs_union_bound_succ_mono_error
#print axioms bcs_union_bound_append_mono_error
#print axioms bcs_union_bound_append_full_mono_error
#print axioms bcs_union_bound_append_zero_left_mono_error
#print axioms bcs_union_bound_append_zero_right_mono_error
#print axioms bcs_opening_union_bound
#print axioms bcs_opening_union_bound_zero
#print axioms bcs_opening_union_bound_one
#print axioms bcs_opening_union_bound_succ
#print axioms bcs_opening_union_bound_one_mono_error
#print axioms bcs_opening_union_bound_succ_mono_error
#print axioms bcs_opening_union_bound_append
#print axioms bcs_opening_union_bound_append_mono_error
#print axioms bcs_opening_union_bound_append_zero_left
#print axioms bcs_opening_union_bound_append_zero_right
#print axioms bcs_opening_union_bound_append_zero_left_mono_error
#print axioms bcs_opening_union_bound_append_zero_right_mono_error
#print axioms bcs_opening_union_bound_mono_error
#print axioms bcs_append_accounting_of_opening_bound
#print axioms bcs_append_accounting_of_opening_bound_mono_error
#print axioms bcs_append_accounting_of_opening_batch
#print axioms bcs_append_accounting_of_opening_batch_mono_error
#print axioms bcs_append_accounting_of_opening_zero
#print axioms bcs_append_accounting_of_opening_one
#print axioms bcs_append_accounting_of_opening_succ
#print axioms bcs_append_accounting_of_opening_append
#print axioms bcs_append_accounting_of_opening_zero_mono_error
#print axioms bcs_append_accounting_of_opening_one_mono_error
#print axioms bcs_append_accounting_of_opening_succ_mono_error
#print axioms bcs_append_accounting_of_opening_append_mono_error
#print axioms bcs_append_accounting_of_opening_append_zero_left
#print axioms bcs_append_accounting_of_opening_append_zero_right
#print axioms bcs_append_accounting_of_opening_append_zero_left_mono_error
#print axioms bcs_append_accounting_of_opening_append_zero_right_mono_error
#print axioms bcs_append_accounting
#print axioms bcs_append_accounting_mono_error
#print axioms bcs_two_phase_total_eq
#print axioms maxUnionBoundPr

end ArkLibScratch.Issue62
