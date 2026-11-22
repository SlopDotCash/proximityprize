/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterCoreWeightedJets
import ArkLib.Research.ProximityGap.Frontier.DoubleInterpolationCommonFactor

/-! # Shared companion degrees at 533,150,000 quarter-rate errors

The resultant charges all noncommon factors together. Common nonlinear factors share
the total scalar/value degree of the companion. The written geometric argument supplies
the individual tangent prices used by the population theorem.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.QuarterCommonFactorDegrees
open Finset Polynomial HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation
open QuarterCoreWeightedJets (SectionSurface rowCount columnCount card_rows card_columns
  uniform_received_surface)

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 268435455
abbrev e : ℕ := 533150000
abbrev t : ℕ := n - e
abbrev core : ℕ := t - 8192
abbrev bound : ℕ := 2128352044

/-- The two ordinary interpolants have positive exact rank surplus on any received pair. -/
theorem ranks :
    columnCount 75769 72 d (36*t) = n * rowCount 75769 36 + 15151548 ∧
    columnCount 3565 142 d (71*t) = n * rowCount 3565 71 + 14490855831 := by decide +kernel

/-- The two surfaces capture all polynomial sections at the specified agreement count. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 71 else 36
    let b := if companion then 142 else 72
    let s := if companion then 3565 else 75769
    SectionSurface dom u v s b d (r*t) (fun S => t ≤ S.card) := by
  cases companion
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn,card_rows,card_columns]
    exact ranks.1 ▸ Nat.lt_add_of_pos_right (by decide)
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn,card_rows,card_columns]
    exact ranks.2 ▸ Nat.lt_add_of_pos_right (by decide)

/-- Apply this to the product of the primary factors outside the companion. Its entire
set of assigned scalar labels fits a single resultant budget. -/
theorem noncommon_labels {F : Type} [Field F] (P Q : F[X][X][X]) (prim : P.IsPrimitive)
    (G : Finset F) (w : F → F[X]) (s m : ℕ)
    (hp : WeightedSylvesterDegree.TotalDegreeLe P s)
    (hq : WeightedSylvesterDegree.TotalDegreeLe Q m)
    (roots : ∀ z ∈ G, P.eval₂ (evalRingHom (C z)) (w z) = 0 ∧
      Q.eval₂ (evalRingHom (C z)) (w z) = 0)
    (outside : ∀ f : F[X][X][X], Irreducible f → 0 < f.natDegree → f ∣ P → ¬ f ∣ Q) :
    G.card ≤ P.natDegree*m + Q.natDegree*s := by
  by_contra! tooMany
  obtain ⟨f,hirr,hpos,hdvd,hq'⟩ :=
    DoubleInterpolationCommonFactor.exists_common prim G w roots hp hq tooMany
  exact outside f hirr hpos hdvd hq'

private def ceilDiv (a b : ℕ) := (a+b-1)/b

private def discreteUnion (j : ℕ) : ℕ :=
  let a := j/2
  ceilDiv (2*a*j*core-j*(j-1)*d) (a*(a+1))

/-- Assigned scalar population on the rich polynomial heads. -/
def headMass (j : ℕ) : ℕ :=
  if j < 3 then j*(e+1) else
    let u := max (discreteUnion j) (ceilDiv (j*core*core) (core+(j-1)*d))
    min (j*(e+1)) (j*n-(j-1)*u)

/-- Bound per unit of actual companion degree. The low range uses ordinary lines,
the high range degree-four Veronese polars. Four or more heads supply a transverse gap. -/
def unitPrice (j : ℕ) (high : Bool) : ℕ :=
  let M := if high then 3565-j else 12
  let b := min (72-j) M
  let w := 36*t-1-j*d
  let H := (6*b+2)*w
  let R := (2*b-1)*n
  let p := if high then min j 3 else min j 2
  let polar := if high then
      4*(M-1)+ceilDiv ((15-p)*(3*R+4*H)) (45*t-10*n-40*d-3*p*8192)
    else M-1+ceilDiv ((3-p)*(R+H)) (3*t-n-2*d-p*8192)
  let transverse := M-1+ceilDiv (H+R) (discreteUnion j+t-(n+d))
  4*b-2+(if j ≥ 4 then transverse else polar)

/-- Largest applicable per-degree price for common nonlinear factors. -/
def commonPrice (j : ℕ) :=
  if 72-j < 2 then 0 else max (unitPrice j false) (unitPrice j true)

private def otherLabels (j : ℕ) : ℕ :=
  headMass j + 75769 + (75769*142+72*3565) + (72-j)*75769 + (3565-j)*17

/-- All denominators in the two determinant tests, the common-head tests, and
the individual transverse comparisons satisfy their strict hypotheses. -/
theorem parameters :
    n+2*d < 3*core ∧ e < 8192*75769 ∧ 4*n ≤ 16*(t-d) ∧
    10*n+40*d+9*8192 < 45*t ∧ n+2*d+2*8192 < 3*t ∧
    ∀ j : Fin 73, 4 ≤ j.val → n+d < discreteUnion j.val+t := by decide +kernel

private theorem group_bound (j : Fin 73) :
    otherLabels j.val + (3565-j.val)*commonPrice j.val ≤ bound := by
  revert j
  decide +kernel

/-- Combine both degree ranges and every nonlinear component using their actual shared
companion degree. The five other classes are the rich heads, scalar-only factors,
noncommon factors, small polynomial heads and nonaffine linear factors. -/
theorem allocation {α : Type*} (j : Fin 73) (S : Finset α) (deg pop : α → ℕ)
    (heads scalar onlyPrimary smallHeads linear : ℕ)
    (hheads : heads ≤ headMass j.val) (hscalar : scalar ≤ 75769)
    (hprimary : onlyPrimary ≤ 75769*142+72*3565)
    (hsmall : smallHeads ≤ (72-j.val)*75769) (hlinear : linear ≤ (3565-j.val)*17)
    (htotal : ∑ i ∈ S, deg i ≤ 3565-j.val)
    (hcost : ∀ i ∈ S, pop i ≤ deg i * commonPrice j.val) :
    heads+scalar+onlyPrimary+smallHeads+linear+∑ i ∈ S, pop i ≤ bound := by
  have sumCost := sum_le_sum hcost
  rw [← sum_mul] at sumCost
  have limit := Nat.mul_le_mul_right (commonPrice j.val) htotal
  have hg := group_bound j
  unfold otherLabels at hg
  omega

#print axioms surfaces
#print axioms noncommon_labels
#print axioms parameters
#print axioms allocation
end ArkLib.ProximityGap.Frontier.QuarterCommonFactorDegrees
