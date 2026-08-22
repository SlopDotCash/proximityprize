/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOrderedWalkMajorant

/-!
# Door-IV ordered-walk / Doob majorant transfer

This file kernels the safe, non-analytic part of Shaw's DIR9 ordered-walk formulation.  If an
order-dependent maximal-excursion radius `R_i` dominates the endpoint period norm at each family member,
then any prize-scale theorem for `R` transfers verbatim to the original endpoint periods.  No Doob,
van-der-Corput, cancellation, moment, completion, or CORE estimate is asserted here; the file only records
exactly what a future ordered-walk maximal inequality would have to prove and how it would be consumed.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant

open ProximityGap.Frontier.ShawValueCapstone

/-- A per-family ordered-walk radius is a Door-IV endpoint majorant when it dominates the norm of the
endpoint period at every member.  In DIR9 notation this abstracts `R(b)=sup_k |S_k(b)| ≥ |S_n(b)|`. -/
def EndpointDominated {ι E : Type*} [SeminormedAddCommGroup E]
    (endpoint : ι → E) (R : ι → ℝ) : Prop :=
  ∀ i : ι, ‖endpoint i‖ ≤ R i

/-- The local consumption rule for the ordered-walk/Doob radius: once the endpoint is one of the partial
sums included in the maximal excursion, the endpoint norm is bounded by the radius.  This is the formal
`R(b) ≥ |η_b|` rung, separated from any analytic estimate on `R`. -/
theorem endpoint_norm_le_radius {ι E : Type*} [SeminormedAddCommGroup E]
    {endpoint : ι → E} {R : ι → ℝ} (hdom : EndpointDominated endpoint R) (i : ι) :
    ‖endpoint i‖ ≤ R i :=
  hdom i

/-- **Ordered-walk majorant transfer.**  A uniform prize-scale bound for the ordered maximal-excursion
radius `R` immediately gives the same uniform prize-scale bound for the endpoint periods `‖endpoint‖`.
This is the citable DIR9 consumer: the remaining open obligation is a genuine per-`b*` maximal-inequality
bound for `R`, not another normalization step. -/
theorem corePrizeBoundOn_endpoint_of_orderedWalkMajorant {ι E : Type*} [SeminormedAddCommGroup E]
    {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : EndpointDominated endpoint R) (hR : CorePrizeBoundOn q n R) :
    CorePrizeBoundOn q n (fun i : ι => ‖endpoint i‖) := by
  exact corePrizeBoundOn_of_le (M := R) (M' := fun i : ι => ‖endpoint i‖) hdom hR

/-- Positive-scale Shaw-value form of the same transfer: if the ordered-walk radius has a prize bound,
then the endpoint periods have bounded Shaw value. -/
theorem shawOOne_endpoint_of_orderedWalkMajorant {ι E : Type*} [SeminormedAddCommGroup E]
    {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i))
    (hdom : EndpointDominated endpoint R) (hR : CorePrizeBoundOn q n R) :
    ShawOOneOn q n (fun i : ι => ‖endpoint i‖) := by
  exact shawOOneOn_of_le_corePrizeBoundOn (M := R) (M' := fun i : ι => ‖endpoint i‖)
    hscale hdom hR

/-- Contrapositive-facing obstruction form: if the endpoint periods do not satisfy the raw prize bound,
then no dominating ordered-walk radius can satisfy that prize bound either.  Thus DIR9 is an exact
reformulation target: a successful Doob/vdC bound for `R` would have to be as strong as the original
Paley/BGK wall. -/
theorem not_corePrizeBoundOn_radius_of_endpoint_not_core {ι E : Type*} [SeminormedAddCommGroup E]
    {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : EndpointDominated endpoint R)
    (hnot : ¬ CorePrizeBoundOn q n (fun i : ι => ‖endpoint i‖)) :
    ¬ CorePrizeBoundOn q n R := by
  intro hR
  exact hnot (corePrizeBoundOn_endpoint_of_orderedWalkMajorant hdom hR)

/-- Concrete DIR9 consumer for the finite maximal-prefix scaffold already formalized as
`maximalExcursion`: a prize-scale theorem for the ordered prefix maximum transfers directly to the
endpoint period. -/
theorem corePrizeBoundOn_endpoint_of_maximalExcursion_bound {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hR : CorePrizeBoundOn q n
      (fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i))) :
    CorePrizeBoundOn q n (fun i : ι => ‖S i (N i)‖) := by
  exact corePrizeBoundOn_endpoint_of_orderedWalkMajorant
    (endpoint := fun i : ι => S i (N i))
    (R := fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
      (S i) (N i))
    (fun i => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_norm_le_maximalExcursion
      (S i) (N i)) hR

/-- Positive-scale Shaw-value version of the concrete finite maximal-prefix consumer. -/
theorem shawOOne_endpoint_of_maximalExcursion_bound {ι E : Type*} [SeminormedAddCommGroup E]
    {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i))
    (hR : CorePrizeBoundOn q n
      (fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i))) :
    ShawOOneOn q n (fun i : ι => ‖S i (N i)‖) := by
  exact shawOOne_endpoint_of_orderedWalkMajorant
    (endpoint := fun i : ι => S i (N i))
    (R := fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
      (S i) (N i)) hscale
    (fun i => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_norm_le_maximalExcursion
      (S i) (N i)) hR

/-- Contrapositive concrete DIR9 form: if endpoint periods are not prize-bounded, the finite ordered
maximal prefix excursion cannot be prize-bounded either. -/
theorem not_corePrizeBoundOn_maximalExcursion_of_endpoint_not_core {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hnot : ¬ CorePrizeBoundOn q n (fun i : ι => ‖S i (N i)‖)) :
    ¬ CorePrizeBoundOn q n
      (fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i)) := by
  exact not_corePrizeBoundOn_radius_of_endpoint_not_core
    (endpoint := fun i : ι => S i (N i))
    (R := fun i : ι => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
      (S i) (N i))
    (fun i => ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_norm_le_maximalExcursion
      (S i) (N i)) hnot

end ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant

#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.endpoint_norm_le_radius
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_orderedWalkMajorant
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.shawOOne_endpoint_of_orderedWalkMajorant
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_radius_of_endpoint_not_core
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_maximalExcursion_bound
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.shawOOne_endpoint_of_maximalExcursion_bound
#print axioms ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_maximalExcursion_of_endpoint_not_core
