/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVZLagrangeBound

/-!
# Degree envelope for the even/odd descent `Z`-term (#444, SEAM A / door-iv adjacent)

`_DoorIVZLagrangeBound` locked the Lagrange rung

`#{y ∈ B : P(y)^2 = y Q(y)^2} ≤ natDegree (P^2 - X Q^2)`.

This file adds the consumer envelope that turns the abstract quadform degree into the word-degree
budget actually used by the G1 descent argument:

`natDegree (P^2 - X Q^2) ≤ max (2 * natDegree P) (1 + 2 * natDegree Q)`.

Thus the non-symmetric single-fibre `Z` term pays exactly the polynomial support exponent of the
two branches. This is a bookkeeping/constraint theorem only: no CORE bound, no cancellation, no
completion, no moment route, and no capacity claim. CORE remains open.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset Polynomial

variable {F : Type*} [Field F]

/-- **Degree envelope for the descent quadform.** The explicit polynomial
`R = Pp^2 - X * Qp^2` has degree at most the larger of the even branch degree `2 deg Pp` and the
odd branch degree `1 + 2 deg Qp`. This is the exact support-exponent budget behind the Lagrange
`Z`-term. -/
theorem descentQuadform_natDegree_le_max (Pp Qp : F[X]) :
    (descentQuadform Pp Qp).natDegree ≤
      max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) := by
  calc
    (descentQuadform Pp Qp).natDegree
        ≤ max (Pp ^ 2).natDegree (X * Qp ^ 2 : F[X]).natDegree := by
          exact Polynomial.natDegree_sub_le (Pp ^ 2) (X * Qp ^ 2 : F[X])
    _ ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) := by
      apply max_le_max
      · simpa [pow_two, two_mul] using (Polynomial.natDegree_pow_le (p := Pp) (n := 2))
      · calc
          (X * Qp ^ 2 : F[X]).natDegree ≤ (X : F[X]).natDegree + (Qp ^ 2).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 + 2 * Qp.natDegree := by
            gcongr
            · simp [Polynomial.natDegree_X]
            · simpa [pow_two, two_mul] using (Polynomial.natDegree_pow_le (p := Qp) (n := 2))

variable [DecidableEq F]

/-- **Consumer form: the non-symmetric descent `Z` count is bounded by the support envelope.**
Combines Lagrange with the explicit degree bound for `Pp^2 - X·Qp^2`. -/
theorem descentZ_card_le_degreeEnvelope {Pp Qp : F[X]}
    (hR : descentQuadform Pp Qp ≠ 0) (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  le_trans (descentZ_card_le_natDegree hR B) (descentQuadform_natDegree_le_max Pp Qp)

/-- Indicator-sum form of the same degree-envelope bound, matching the descent identity's
`Z` term. -/
theorem descentZ_indicator_sum_le_degreeEnvelope {Pp Qp : F[X]}
    (hR : descentQuadform Pp Qp ≠ 0) (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) := by
  have hsum :
      (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
        = (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card := by
    rw [Finset.card_filter]
  rw [hsum]
  exact descentZ_card_le_degreeEnvelope hR B

end ArkLib.ProximityGap.EvenOddDescent

#print axioms ArkLib.ProximityGap.EvenOddDescent.descentQuadform_natDegree_le_max
#print axioms ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degreeEnvelope
#print axioms ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degreeEnvelope
