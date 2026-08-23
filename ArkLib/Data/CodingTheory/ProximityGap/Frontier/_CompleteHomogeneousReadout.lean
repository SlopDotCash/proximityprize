/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Issue407SaturatedIncidence

/-!
# Complete-homogeneous readout adapter for #407

The latest #407 demand-side correction says that the worst monomial pencils are governed by
complete-homogeneous readouts

`h_j(T) = [T] X^(|T|-1+j)`,

not only by the elementary/subset-sum spectrum.  The in-tree Schur/Lagrange bridge already
formalizes the divided-difference value `[T] X^b` as `dividedDifferencePow`.

This scratch adapter gives the #407 profile interface a concrete Lean-facing name for the
readout value and records the deterministic anchors/recurrence:

* `h_0(T)=1`;
* `h_1(T)=sum(T)`;
* `h_2(T)` and `h_3(T)` in terms of the node polynomial coefficients;
* the general Schur recurrence transports directly to the `h_j` readout scale.

No theorem here claims a closed form for the worst-direction profile `J(w)`.
-/

namespace ProximityGap.Frontier.CompleteHomogeneousReadout

open Finset Polynomial
open ProximityGap.SchurLagrange

variable {F ι : Type*} [Field F] [DecidableEq ι]

/--
The complete-homogeneous readout on a finite node set `s`:

`completeHomReadout s v j = h_j(v_s) = [s] X^(|s|-1+j)`.

For `|s| = w`, this is the value called `h_j(T)` in the #407 complete-homogeneous
worst-direction profile.
-/
noncomputable def completeHomReadout (s : Finset ι) (v : ι → F) (j : ℕ) : F :=
  dividedDifferencePow s v (#s - 1 + j)

/-- Anchor `h_0 = 1` for nonempty node sets. -/
theorem completeHomReadout_zero {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    completeHomReadout s v 0 = 1 := by
  unfold completeHomReadout
  rw [add_zero]
  exact dividedDifferencePow_eq_one hvs hs

/-- Anchor `h_1 = e_1 = ∑ v_i` for nonempty node sets. -/
theorem completeHomReadout_one {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    completeHomReadout s v 1 = ∑ i ∈ s, v i := by
  unfold completeHomReadout
  have hcard : #s - 1 + 1 = #s := Nat.sub_add_cancel (Finset.card_pos.mpr hs)
  rw [hcard]
  exact dividedDifferencePow_card_eq_sum hvs hs

/-- Closed formula for `h_2`: `h_2 = e_1^2 - e_2`, with `e_2` read from the node polynomial. -/
theorem completeHomReadout_two {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : 2 ≤ #s) :
    completeHomReadout s v 2
      = (∑ i ∈ s, v i) ^ 2 - (∏ i ∈ s, (X - C (v i))).coeff (#s - 2) := by
  unfold completeHomReadout
  have hcard : #s - 1 + 2 = #s + 1 := by omega
  rw [hcard]
  exact dividedDifferencePow_card_add_one hvs hs

/--
Closed formula for `h_3`: `h_3 = e_1^3 - 2 e_1 e_2 + e_3`, with `e_2,e_3` read from the
node polynomial coefficient convention used by `SchurLagrangeBridge`.
-/
theorem completeHomReadout_three {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : 3 ≤ #s) :
    completeHomReadout s v 3
      = (∑ i ∈ s, v i) ^ 3
        - 2 * (∑ i ∈ s, v i) * (∏ i ∈ s, (X - C (v i))).coeff (#s - 2)
        - (∏ i ∈ s, (X - C (v i))).coeff (#s - 3) := by
  unfold completeHomReadout
  have hcard : #s - 1 + 3 = #s + 2 := by omega
  rw [hcard]
  exact dividedDifferencePow_card_add_two hvs hs

/--
Schur recurrence in complete-homogeneous coordinates.  For a node set of size `N = |s|`,
the readout `h_{j+1}` is a linear combination of earlier readouts, with coefficients from the
node polynomial `∏(X-v_i)`.
-/
theorem completeHomReadout_recurrence {s : Finset ι} {v : ι → F} (j : ℕ) :
    completeHomReadout s v (j + 1)
      = - ∑ m ∈ range #s, (∏ i ∈ s, (X - C (v i))).coeff m
          * dividedDifferencePow s v (#s - 1 + (j + 1) - #s + m) := by
  unfold completeHomReadout
  exact dividedDifferencePow_recurrence (#s - 1 + (j + 1)) (by omega)

/--
The #407 profile-level condition `h_j(T)=0` and readout `h_{j+1}(T)` for a concrete node set.
This is the value-level object whose distinct image sizes feed the envelope `J(w)` in
`Issue407SaturatedIncidence`.
-/
def CompleteHomReadoutEvent (s : Finset ι) (v : ι → F) (j : ℕ) : Prop :=
  completeHomReadout s v j = 0

/-- Refutation hook for the `h_j=0` constraint. -/
theorem not_completeHomReadoutEvent_of_ne {s : Finset ι} {v : ι → F} {j : ℕ}
    (h : completeHomReadout s v j ≠ 0) :
    ¬ CompleteHomReadoutEvent s v j := by
  intro hevent
  exact h hevent

/-- The `h_0=0` constraint is impossible on a nonempty node set.  Thus the #407 envelope starts at
genuine positive readout index `j ≥ 1`. -/
theorem not_completeHomReadoutEvent_zero {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ¬ CompleteHomReadoutEvent s v 0 := by
  apply not_completeHomReadoutEvent_of_ne
  rw [completeHomReadout_zero hvs hs]
  exact one_ne_zero

end ProximityGap.Frontier.CompleteHomogeneousReadout

set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout_zero
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout_one
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout_two
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout_three
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.completeHomReadout_recurrence
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.not_completeHomReadoutEvent_of_ne
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.CompleteHomogeneousReadout.not_completeHomReadoutEvent_zero
