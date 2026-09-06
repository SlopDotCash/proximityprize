/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Higher coordinate moments collapse to the failed second-moment jaw

For a family of `P` aligned sets let `d(x)` be the number containing coordinate
`x`.  Any attempt to use an `r`th incidence moment while retaining only the
known pairwise-intersection information must upper-bound it through
`d(x)^r ≤ P^(r-2)d(x)^2`.  Thus every higher moment pays the full trivial
maximum-degree factor and contains no more information than the second moment.

This does not rule out higher moments carrying *new algebraic constraints* on
which pencils meet at a coordinate.  It rules out the purely combinatorial
upgrade that simply replaces Cauchy--Schwarz by a higher power.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterHigherMomentIncidenceNoGo

/-- Pointwise collapse of an `r`th moment to the second moment under the
trivial degree cap `d ≤ P`. -/
theorem pow_le_pow_sub_two_mul_sq {d P r : ℕ} (hr : 2 ≤ r) (hd : d ≤ P) :
    d ^ r ≤ P ^ (r - 2) * d ^ 2 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left, pow_add]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d ^ 2) (Nat.pow_le_pow_left hd q)

/-- Summed form for an arbitrary finite coordinate set. -/
theorem sum_pow_le_pow_sub_two_mul_sum_sq
    {ι : Type*} [DecidableEq ι] (X : Finset ι) (d : ι → ℕ) (P r : ℕ)
    (hr : 2 ≤ r) (hd : ∀ x ∈ X, d x ≤ P) :
    ∑ x ∈ X, d x ^ r ≤ P ^ (r - 2) * ∑ x ∈ X, d x ^ 2 := by
  calc
    ∑ x ∈ X, d x ^ r
        ≤ ∑ x ∈ X, P ^ (r - 2) * d x ^ 2 :=
          Finset.sum_le_sum fun x hx => pow_le_pow_sub_two_mul_sq hr (hd x hx)
    _ = P ^ (r - 2) * ∑ x ∈ X, d x ^ 2 := by
          rw [Finset.mul_sum]

/-- Incidence degrees of a `P`-set family satisfy the required trivial cap. -/
theorem incidenceDegree_le_familyCard
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (Fam : Finset κ) (A : κ → Finset ι) (x : ι) :
    (Fam.filter (fun j => x ∈ A j)).card ≤ Fam.card :=
  Finset.card_filter_le _ _

/-- **Higher-moment incidence no-go.**  For aligned-set incidences, every
`r ≥ 2` moment is bounded by the second moment times the trivial factor
`|Fam|^(r-2)`.  Hence pairwise overlap data alone cannot make a higher-moment
jaw stronger than the already-failed P1 second-moment jaw. -/
theorem alignedFamily_higherMoment_le_secondMoment
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Finset ι) (Fam : Finset κ) (A : κ → Finset ι) (r : ℕ)
    (hr : 2 ≤ r) :
    ∑ x ∈ X, (Fam.filter (fun j => x ∈ A j)).card ^ r ≤
      Fam.card ^ (r - 2) *
        ∑ x ∈ X, (Fam.filter (fun j => x ∈ A j)).card ^ 2 :=
  sum_pow_le_pow_sub_two_mul_sum_sq X
    (fun x => (Fam.filter (fun j => x ∈ A j)).card) Fam.card r hr
    (fun x _ => incidenceDegree_le_familyCard Fam A x)

end ArkLib.ProximityGap.Frontier.P1RateQuarterHigherMomentIncidenceNoGo

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterHigherMomentIncidenceNoGo

#print axioms pow_le_pow_sub_two_mul_sq
#print axioms sum_pow_le_pow_sub_two_mul_sum_sq
#print axioms incidenceDegree_le_familyCard
#print axioms alignedFamily_higherMoment_le_secondMoment
