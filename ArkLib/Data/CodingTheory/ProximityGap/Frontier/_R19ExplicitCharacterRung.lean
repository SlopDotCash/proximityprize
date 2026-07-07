/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18SigmaEquidistribution
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19ChiDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19DepletedConstant

/-!
# R19 explicit character-family consumer

This lane wires the explicit `χ`-generated family from `_R19ChiDecomposition` into the R18
sigma-equidistribution consumers.

The payoff is a narrower r = 2 interface for the concrete subgroup `Gχ`: the
`ChiDecompositionOff`, `GaussSumSizeBound`, and `hSig` inputs are all discharged.  The remaining
nontrivial analytic input is the fourth-moment twist bound plus the explicit constant gate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19DepletedConstant
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `MulChar F ℂ` needs classical decidable equality for thinned `Finset` operations. -/
noncomputable local instance : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- The explicit nontrivial character family has size at most the character order. -/
theorem chiFamily_card_le_order (χ : MulChar F ℂ) :
    ((chiFamily χ).card : ℝ) ≤ (orderOf χ : ℝ) := by
  rw [chiFamily_card]
  exact_mod_cast Nat.sub_le (orderOf χ) 1

/-- For a nontrivial generated family (`orderOf χ ≥ 2`), `chiFamily χ` is nonempty. -/
theorem chiFamily_nonempty_of_two_le_order (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    (chiFamily χ).Nonempty := by
  exact Finset.card_pos.mp (by rw [chiFamily_card]; omega)

/-- The full explicit family is too large for the R18 exact-rung size gate:
`15 * |chiFamily χ|² ≤ orderOf χ` is impossible once `orderOf χ ≥ 2`.

This records an important obstruction: the current `15|X|² ≤ m` exact-rung consumer cannot be
closed by simply taking all nontrivial powers of `χ`; a depleted/thinned family or a stronger
constant route is needed. -/
theorem not_fifteen_chiFamily_card_sq_le_order (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (chiFamily χ).card ^ 2 ≤ orderOf χ := by
  intro h
  rw [chiFamily_card] at h
  have hreal : ((15 * (orderOf χ - 1) ^ 2 : ℕ) : ℝ) ≤ (orderOf χ : ℝ) := by
    exact_mod_cast h
  have hsub : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, hsub] at hreal
  have hmreal : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  nlinarith [sq_nonneg ((orderOf χ : ℝ) - 2)]

/-- Real-valued companion to `not_fifteen_chiFamily_card_sq_le_order`. -/
theorem not_fifteen_chiFamily_card_sq_le_order_real (χ : MulChar F ℂ)
    (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (((chiFamily χ).card : ℝ) ^ 2) ≤ (orderOf χ : ℝ) := by
  intro h
  rw [chiFamily_card] at h
  have hsub : ((orderOf χ - 1 : ℕ) : ℝ) = (orderOf χ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one]
  rw [hsub] at h
  have hmreal : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  nlinarith [sq_nonneg ((orderOf χ : ℝ) - 2)]

/-! ### Thin subfamilies: what survives restriction -/

/-- Gauss-sum size bounds restrict from the full explicit `chiFamily` to any subfamily. -/
theorem gaussSumSizeBound_chiSubfamily (χ : MulChar F ℂ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) :
    GaussSumSizeBound Y (fun χ' => gaussSum χ' ψ) := by
  intro χ' hχ'
  exact gaussSumSizeBound_holds χ hψ χ' (hY hχ')

/-- Fourth-moment twist bounds restrict to subfamilies. -/
theorem fourthMomentTwistBound_mono {G : Finset F} {X Y : Finset (MulChar F ℂ)} {Cw : ℝ}
    (hY : Y ⊆ X) (h4 : FourthMomentTwistBound G X Cw) :
    FourthMomentTwistBound G Y Cw := by
  intro χ' hχ'
  exact h4 χ' (hY hχ')

/-- The per-character quartic-Weil input restricts to subfamilies. -/
theorem quarticWeilInput_mono {G : Finset F} {X Y : Finset (MulChar F ℂ)}
    (hY : Y ⊆ X)
    (hW :
      ∀ χ' ∈ X,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G) :
    ∀ χ' ∈ Y,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G := by
  intro χ' hχ'
  exact hW χ' (hY hχ')

/-- The quartic-Weil-to-fourth-moment adapter is compatible with thinning the explicit
`chiFamily`: any subfamily inherits `FourthMomentTwistBound` with constant `6`. -/
theorem fourthMomentTwistBound_chiSubfamily_of_quarticWeilInput
    (χ : MulChar F ℂ) (G : Finset F) {Y : Finset (MulChar F ℂ)}
    (hY : Y ⊆ chiFamily χ)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    FourthMomentTwistBound G Y 6 :=
  ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.fourthMomentTwistBound_of_quarticWeilInput
    G Y (quarticWeilInput_mono hY hW) hn4q

/-- The omitted-character residual for a proposed thinned `chiFamily` decomposition. -/
noncomputable def chiSubfamilyResidual (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F)
    (Y : Finset (MulChar F ℂ)) (s₀ : F) : ℂ :=
  ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀

/-- The omitted-character residual vanishes at every offset outside `D`. -/
def ChiSubfamilyResidualVanishesOff (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (G D : Finset F) (Y : Finset (MulChar F ℂ)) : Prop :=
  ∀ s₀ : F, s₀ ∉ D → chiSubfamilyResidual χ ψ G Y s₀ = 0

/-- The residual vanishes identically for the full explicit family. -/
theorem chiSubfamilyResidual_full_eq_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G : Finset F) (s₀ : F) :
    chiSubfamilyResidual χ ψ G (chiFamily χ) s₀ = 0 := by
  classical
  unfold chiSubfamilyResidual
  rw [Finset.sdiff_self, Finset.sum_empty]

/-- Off-set vanishing base case for the full explicit family. -/
theorem chiSubfamilyResidualVanishesOff_full
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G D : Finset F) :
    ChiSubfamilyResidualVanishesOff χ ψ G D (chiFamily χ) := by
  intro s₀ _hs₀
  exact chiSubfamilyResidual_full_eq_zero χ ψ G s₀

/-- Exact decomposition for a thinned subfamily plus the explicit omitted-character residual.
This is the precise identity behind the thinned-family route: proving `ChiDecompositionOff` for
`Y` alone is equivalent to controlling or canceling this residual. -/
theorem chiSubfamily_decomposition_with_residual
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀
      = -(G.card : ℂ)
        + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
        + chiSubfamilyResidual χ ψ G Y s₀ := by
  classical
  have hfull := chiDecompositionOff_holds χ hψ hGD s₀ hs₀
  unfold chiSubfamilyResidual
  calc (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀
      = -(G.card : ℂ)
          + ∑ χ' ∈ chiFamily χ, gaussSum χ' ψ * twistedThinSum χ' G s₀ := hfull
    _ = -(G.card : ℂ)
          + (∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀) := by
        rw [← Finset.sum_sdiff hY]
        ring_nf
    _ = -(G.card : ℂ)
        + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
        + ∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀ := by
        ring

/-- A thinned `chiFamily` has an exact `ChiDecompositionOff` identity iff its omitted-character
residual vanishes off the deleted set.  This is the formal target exposed by the thinning route. -/
theorem chiSubfamily_chiDecompositionOff_iff_residual_vanishes
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) :
    ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ)
      ↔ ChiSubfamilyResidualVanishesOff χ ψ G D Y := by
  constructor
  · intro hdec s₀ hs₀
    have hres := chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀
    have hthin := hdec s₀ hs₀
    set A : ℂ := -(G.card : ℂ) + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
    have hA : A + chiSubfamilyResidual χ ψ G Y s₀ = A + 0 := by
      calc A + chiSubfamilyResidual χ ψ G Y s₀
          = (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀ := by
            exact hres.symm
        _ = A := by
            exact hthin
        _ = A + 0 := by rw [add_zero]
    exact add_left_cancel hA
  · intro hzero s₀ hs₀
    rw [chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀, hzero s₀ hs₀, add_zero]

/-- The residual framework recovers the full-family decomposition as the zero-residual base
case.  This is a sanity check for the thinned-family formulation. -/
theorem chiDecompositionOff_holds_of_residual_full
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) :
    ChiDecompositionOff ψ G (Gchi χ) D (chiFamily χ) (fun χ' => gaussSum χ' ψ) (orderOf χ) :=
  (chiSubfamily_chiDecompositionOff_iff_residual_vanishes χ hψ hGD (Subset.rfl)).2
    (chiSubfamilyResidualVanishesOff_full χ ψ G D)

/-- Crude but useful residual norm bound: if every omitted character has
`‖T_χ(s₀)‖ ≤ T`, then the omitted-character residual is at most
`#(chiFamily χ \ Y) * √q * T`.  This turns the thinned-family decomposition residual into a
rate target. -/
theorem norm_chiSubfamilyResidual_le_card_mul
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (Y : Finset (MulChar F ℂ)) (s₀ : F) {T : ℝ}
    (hT : ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T) :
    ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  classical
  unfold chiSubfamilyResidual
  have hterm : ∀ χ' ∈ chiFamily χ \ Y,
      ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        ≤ Real.sqrt (Fintype.card F : ℝ) * T := by
    intro χ' hχ'
    have hχfam : χ' ∈ chiFamily χ := (Finset.mem_sdiff.mp hχ').1
    rw [norm_mul]
    have hg := gaussSumSizeBound_holds χ hψ χ' hχfam
    have hthin := hT χ' hχ'
    have hgnonneg : 0 ≤ ‖gaussSum χ' ψ‖ := norm_nonneg _
    have htnonneg : 0 ≤ ‖twistedThinSum χ' G s₀‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_nonneg _
    exact mul_le_mul hg hthin htnonneg hsqrt
  calc ‖∑ χ' ∈ chiFamily χ \ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
      ≤ ∑ χ' ∈ chiFamily χ \ Y, ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _χ' ∈ chiFamily χ \ Y, Real.sqrt (Fintype.card F : ℝ) * T := by
        exact Finset.sum_le_sum (fun χ' hχ' => hterm χ' hχ')
    _ = ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- High-moment rate version of the residual bound.  If every omitted character has an away-Wick
bound at rung `r` strong enough to force `‖T_χ(s₀)‖ ≤ T`, then the residual obeys the same
cardinality times `√q·T` estimate. -/
theorem norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) (Y : Finset (MulChar F ℂ)) {s₀ : F} (hs₀ : s₀ ∉ D)
    (r : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hr : 1 ≤ r)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r)) :
    ‖chiSubfamilyResidual χ ψ G Y s₀‖
      ≤ ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
  exact norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀
    (fun χ' hχ' =>
      twistedThinSum_le_of_shifted_awayWickAt_rate χ' G D r hT0 hr (hwick χ' hχ') hrate hs₀)

/-- Pointwise incidence bound from a thinned character family plus a residual norm cap.  This is
the approximate analogue of the R17 pointwise bound: the thin contribution costs
`|Y|√q·T`, while omitted characters enter only through `R`. -/
theorem incidenceSum_le_of_chiSubfamily_residual_bound
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) {T R : ℝ}
    (hT : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T)
    (hR : ‖chiSubfamilyResidual χ ψ G Y s₀‖ ≤ R) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ) + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T + R := by
  classical
  have hdecs := chiSubfamily_decomposition_with_residual χ hψ hGD hY hs₀
  have hnorm : (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
    have heq : ‖(orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀‖
        = ‖-(G.card : ℂ)
            + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + chiSubfamilyResidual χ ψ G Y s₀‖ := by rw [hdecs]
    calc (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
        = ‖(orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖-(G.card : ℂ)
            + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
            + chiSubfamilyResidual χ ψ G Y s₀‖ := heq
      _ ≤ ‖-(G.card : ℂ)‖
            + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
            + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
          calc ‖-(G.card : ℂ)
                + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀
                + chiSubfamilyResidual χ ψ G Y s₀‖
              ≤ ‖-(G.card : ℂ)
                    + ∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
                  + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := norm_add_le _ _
            _ ≤ (‖-(G.card : ℂ)‖
                    + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖)
                  + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right
                    (norm_add_le (-(G.card : ℂ))
                      (∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀))
                    ‖chiSubfamilyResidual χ ψ G Y s₀‖
            _ = ‖-(G.card : ℂ)‖
                    + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
                    + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by ring
      _ = (G.card : ℝ)
            + ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
            + ‖chiSubfamilyResidual χ ψ G Y s₀‖ := by
          rw [norm_neg, Complex.norm_natCast]
  have hsum : ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
      ≤ (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
    calc ‖∑ χ' ∈ Y, gaussSum χ' ψ * twistedThinSum χ' G s₀‖
        ≤ ∑ χ' ∈ Y, ‖gaussSum χ' ψ * twistedThinSum χ' G s₀‖ := norm_sum_le Y _
      _ ≤ ∑ _χ' ∈ Y, Real.sqrt (Fintype.card F : ℝ) * T := by
          refine Finset.sum_le_sum fun χ' hχ' => ?_
          rw [norm_mul]
          have hg := gaussSumSizeBound_holds χ hψ χ' (hY hχ')
          have htw := hT χ' hχ'
          exact mul_le_mul hg htw (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  linarith

/-- Pointwise incidence bound with the residual cap discharged by direct pointwise bounds on the
kept and omitted character sums.  This is the practical approximate-thinning estimate:
kept characters cost `|Y|√q·T_in`, omitted characters cost
`|chiFamily χ \ Y|√q·T_out`. -/
theorem incidenceSum_le_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) {T_in T_out : ℝ}
    (hTin : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout : ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
  exact incidenceSum_le_of_chiSubfamily_residual_bound χ hψ G D hGD hY hs₀ hTin
    (norm_chiSubfamilyResidual_le_card_mul χ hψ G Y s₀ hTout)

/-- High-moment-rate version of
`incidenceSum_le_of_chiSubfamily_pointwise_bounds`, with the omitted-character bound supplied by
shifted away-Wick hypotheses. -/
theorem incidenceSum_le_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {s₀ : F} (hs₀ : s₀ ∉ D) (r : ℕ) {T_in T_out : ℝ}
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin : ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r)) :
    (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖
      ≤ (G.card : ℝ)
        + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
        + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out := by
  exact incidenceSum_le_of_chiSubfamily_residual_bound χ hψ G D hGD hY hs₀ hTin
    (norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate χ hψ G D Y hs₀
      r hTout0 hr hwick hrate)

/-- A crude pointwise-to-away-fourth bridge for approximate decompositions.  If every surviving
offset obeys `m‖I(s₀)‖ ≤ B`, then the diagonal-subtracted fourth moment obeys
`m⁴ S₂^D ≤ |F \ D| B⁴`.  This is intentionally elementary: it exposes exactly what a
pointwise residual estimate buys before any Wick-scale averaging is recovered. -/
theorem incidenceMomentAway_two_mul_le_of_pointwise_order_bound
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B : ℝ}
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4 := by
  classical
  unfold incidenceMomentAway
  rw [mul_sum]
  calc ∑ s₀ ∈ (Finset.univ : Finset F) \ D,
        (orderOf χ : ℝ) ^ 4 * ‖incidenceSum ψ G (Gchi χ) s₀‖ ^ (2 * 2)
      ≤ ∑ _s₀ ∈ (Finset.univ : Finset F) \ D, B ^ 4 := by
        refine Finset.sum_le_sum fun s₀ hs₀ => ?_
        have hsD : s₀ ∉ D := (Finset.mem_sdiff.mp hs₀).2
        have hpt := hpoint s₀ hsD
        have hnonneg :
            0 ≤ (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ := by positivity
        have hpow :
            ((orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖) ^ 4 ≤ B ^ 4 :=
          pow_le_pow_left₀ hnonneg hpt 4
        calc (orderOf χ : ℝ) ^ 4 * ‖incidenceSum ψ G (Gchi χ) s₀‖ ^ 4
            = ((orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖) ^ 4 := by ring
          _ ≤ B ^ 4 := hpow
    _ = (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4 := by
        simp only [Finset.sum_const, nsmul_eq_mul]

/-- Away-fourth-moment consequence of uniform thin-family pointwise bounds.  This is the
fully composed crude residual route: prove pointwise bounds for the kept characters and the
omitted residual characters on every surviving offset, and get an explicit fourth-moment bound
for the incidence sum. -/
theorem incidenceMomentAway_two_mul_le_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out : ℝ}
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4 := by
  exact incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY hs₀
        (hTin s₀ hs₀) (hTout s₀ hs₀))

/-- Away-fourth-moment consequence when the omitted-character side is supplied by shifted
away-Wick rate hypotheses.  The remaining pointwise input is only on the kept subfamily `Y`. -/
theorem incidenceMomentAway_two_mul_le_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out : ℝ} (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r)) :
    (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4 := by
  exact incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY hs₀ r
        hTout0 hr (hTin s₀ hs₀) hwick hrate)

/-- Constant-rung bridge from a pointwise order-scaled incidence bound.  The only numerical
content is the explicit gate comparing the crude pointwise fourth-moment total to the desired
R16 constant-`C` Wick scale. -/
theorem wickAwayAtWithConstant_two_of_pointwise_order_bound
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hm : 1 ≤ orderOf χ)
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  unfold WickAwayAtWithConstant
  have hmreal : (0 : ℝ) < (orderOf χ : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hm
  have hm4 : (0 : ℝ) < (orderOf χ : ℝ) ^ 4 := by positivity
  have hmoment := incidenceMomentAway_two_mul_le_of_pointwise_order_bound ψ χ G D hpoint
  have hmul :
      (orderOf χ : ℝ) ^ 4 * incidenceMomentAway ψ G (Gchi χ) D 2
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2)) :=
    le_trans hmoment hgate
  exact le_of_mul_le_mul_left hmul hm4

/-- Constant-rung bridge with the pointwise bound supplied by uniform thin-family estimates. -/
theorem wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  exact wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY hs₀
        (hTin s₀ hs₀) (hTout s₀ hs₀))
    hgate

/-- Constant-rung bridge for the residual route with omitted characters controlled by shifted
away-Wick rate hypotheses. -/
theorem wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ)
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    WickAwayAtWithConstant ψ G (Gchi χ) D 2 C := by
  exact wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm
    (fun s₀ hs₀ =>
      incidenceSum_le_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY hs₀ r
        hTout0 hr (hTin s₀ hs₀) hwick hrate)
    hgate

/-- Raw fourth-moment endpoint from an abstract pointwise order-scaled incidence bound and the
explicit constant-`≤ 1` numerical gate. -/
theorem rawFourthMomentWithDiagonal_of_pointwise_order_bound_gate
    (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (G D : Finset F) {B C : ℝ}
    (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hpoint :
      ∀ s₀ : F, s₀ ∉ D →
        (orderOf χ : ℝ) * ‖incidenceSum ψ G (Gchi χ) s₀‖ ≤ B)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ) * B ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_pointwise_order_bound ψ χ G D hm hpoint hgate)

/-- Raw fourth-moment endpoint from uniform thin-family pointwise bounds and the explicit
constant-`≤ 1` numerical gate. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_pointwise_bounds_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hTout :
      ∀ s₀ : F, s₀ ∉ D →
        ∀ χ' ∈ chiFamily χ \ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_out)
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds χ hψ G D hGD hY
      hm hTin hTout hgate)

/-- Raw fourth-moment endpoint for the approximate residual route.  Once the explicit numeric
gate puts the pointwise-residual constant at `C ≤ 1`, R16 collapses the constant-rung statement
back to the exact R15 `RawFourthMomentWithDiagonal` target. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_gate
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)} (hGD : G ⊆ D) (hY : Y ⊆ chiFamily χ)
    (r : ℕ) {T_in T_out C : ℝ} (hm : 1 ≤ orderOf χ) (hC : C ≤ 1)
    (hTout0 : 0 ≤ T_out) (hr : 1 ≤ r)
    (hTin :
      ∀ s₀ : F, s₀ ∉ D → ∀ χ' ∈ Y, ‖twistedThinSum χ' G s₀‖ ≤ T_in)
    (hwick :
      ∀ χ' ∈ chiFamily χ \ Y,
        ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ' G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T_out ^ (2 * r))
    (hgate :
      (((Finset.univ : Finset F) \ D).card : ℝ)
        * ((G.card : ℝ)
          + (Y.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_in
          + ((chiFamily χ \ Y).card : ℝ) * Real.sqrt (Fintype.card F : ℝ) * T_out) ^ 4
        ≤ (orderOf χ : ℝ) ^ 4
          * (C * ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * 2 - 1) : ℝ)
            * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2))) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D :=
  rawFourthMomentWithDiagonal_of_wickAwayAtWithConstant_two_le_one G (Gchi χ) D hC
    (wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate χ hψ G D hGD hY
      r hm hTout0 hr hTin hwick hrate hgate)

/-- **Thin-subfamily exact-rung consumer.**  If a subfamily `Y ⊆ chiFamily χ` has its own exact
`ChiDecompositionOff` identity, then all other explicit-character inputs are discharged:
Gauss-sum sizes come from `_R19ChiDecomposition`, the fourth-moment twist from the per-character
quartic-Weil input on the full family, and `hSig` from R18 sigma-equidistribution.  This isolates
the true missing ingredient for a thinned route: proving the decomposition with the deleted
characters accounted for. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hY : Y ⊆ chiFamily χ)
    (hX : Y.Nonempty) (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  exact wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D Y (fun χ' => gaussSum χ' ψ) χ hm hn hX horder hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY)
    (quarticWeilInput_mono hY hW) hq1 hnq hn4q hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) {Y : Finset (MulChar F ℂ)}
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hY : Y ⊆ chiFamily χ)
    (hX : Y.Nonempty) (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) D Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  exact rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D Y (fun χ' => gaussSum χ' ψ) χ hm hn hX horder hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY)
    (quarticWeilInput_mono hY hW) hq1 hnq hn4q hreg

/-- **Explicit-character R18 exact away-Wick consumer.**  For `H = Gχ` and the explicit
nontrivial family `chiFamily χ`, the decomposition, Gauss-sum size bound, and Σ lower bound are
proved internally.  The remaining hypotheses are exactly the fourth-moment twist bound, the
constant gate, and the size regime. -/
theorem wickForIncidenceAwayAt_two_of_chiFamily_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hC :
      32 * (Cw * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (h4 : FourthMomentTwistBound G (chiFamily χ) Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  exact wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hCw hC
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    h4 hq1 hnq hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiFamily_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hC :
      32 * (Cw * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (h4 : FourthMomentTwistBound G (chiFamily χ) Cw)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  exact rawFourthMomentWithDiagonal_of_gchi_of_constant_le_one
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hCw hC
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    h4 hq1 hnq hreg

/-- Fully quartic-Weil version of
`wickForIncidenceAwayAt_two_of_chiFamily_of_constant_le_one`: the fourth-moment twist bound is
itself discharged from the per-character quartic-Weil input on the explicit `chiFamily`. -/
theorem wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    (hC :
      32 * (6 * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  exact wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_constant_le_one
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hC
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hW hq1 hnq hn4q hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_quarticWeil_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    (hC :
      32 * (6 * ((chiFamily χ).card : ℝ) ^ 4 + 1) / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  exact rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_constant_le_one
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hC
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hW hq1 hnq hn4q hreg

/-- Nat-order quartic-Weil exact-rung consumer for the explicit `chiFamily`.  This is the
same size gate as the generic R18 quartic-Weil route, with the decomposition and Gauss-sum
inputs discharged by `_R19ChiDecomposition`. -/
theorem wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    (hX : (chiFamily χ).Nonempty)
    (horder : 15 * (chiFamily χ).card ^ 2 ≤ orderOf χ)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  exact wickForIncidenceAwayAt_two_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hX horder
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hW hq1 hnq hn4q hreg

/-- Raw fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat`. -/
theorem rawFourthMomentWithDiagonal_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    (hX : (chiFamily χ).Nonempty)
    (horder : 15 * (chiFamily χ).card ^ 2 ≤ orderOf χ)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) D := by
  exact rawFourthMomentWithDiagonal_of_gchi_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G D (chiFamily χ) (fun χ' => gaussSum χ' ψ) χ hm hn hX horder
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hW hq1 hnq hn4q hreg

/-- **Explicit-character R19 linear-`K` depleted rung.**  For `H = Gχ`, the decomposition,
Gauss-sum size bound, `|X| ≤ m`, and Σ lower bound are discharged for `chiFamily χ`; only the
cubic quadruple-family mass bound remains as analytic input. -/
theorem r19_linearK_incidenceMomentAway_of_chiFamily
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G D : Finset F) (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ D)
    {C₄ : ℝ} (hC₄ : 0 ≤ C₄)
    (hfam : FamilyQuarticCubicBound G (chiFamily χ) C₄)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    incidenceMomentAway ψ G (Gchi χ) D 2
      ≤ 32 * (C₄ + 1) * (orderOf χ : ℝ) * (Fintype.card F : ℝ)
          * (∑ b ∈ Gchi χ, ‖eta ψ G b‖ ^ 2) ^ 2 := by
  exact r19_linearK_rung ψ G (Gchi χ) D (chiFamily χ)
    (fun χ' => gaussSum χ' ψ) (orderOf χ) (le_trans (by norm_num) hm) hC₄
    (chiDecompositionOff_holds χ hψ hGD)
    (gaussSumSizeBound_holds χ hψ)
    hfam
    (chiFamily_card_le_order χ)
    hq1 hnq
    (hSig_of_regime hψ G hm hn hreg)

#print axioms chiFamily_card_le_order
#print axioms chiFamily_nonempty_of_two_le_order
#print axioms not_fifteen_chiFamily_card_sq_le_order
#print axioms not_fifteen_chiFamily_card_sq_le_order_real
#print axioms gaussSumSizeBound_chiSubfamily
#print axioms fourthMomentTwistBound_mono
#print axioms quarticWeilInput_mono
#print axioms fourthMomentTwistBound_chiSubfamily_of_quarticWeilInput
#print axioms chiSubfamilyResidual_full_eq_zero
#print axioms chiSubfamilyResidualVanishesOff_full
#print axioms chiSubfamily_decomposition_with_residual
#print axioms chiSubfamily_chiDecompositionOff_iff_residual_vanishes
#print axioms chiDecompositionOff_holds_of_residual_full
#print axioms norm_chiSubfamilyResidual_le_card_mul
#print axioms norm_chiSubfamilyResidual_le_card_mul_of_shifted_awayWickAt_rate
#print axioms incidenceSum_le_of_chiSubfamily_residual_bound
#print axioms incidenceSum_le_of_chiSubfamily_pointwise_bounds
#print axioms incidenceSum_le_of_chiSubfamily_shifted_omitted_rate
#print axioms incidenceMomentAway_two_mul_le_of_pointwise_order_bound
#print axioms incidenceMomentAway_two_mul_le_of_chiSubfamily_pointwise_bounds
#print axioms incidenceMomentAway_two_mul_le_of_chiSubfamily_shifted_omitted_rate
#print axioms wickAwayAtWithConstant_two_of_pointwise_order_bound
#print axioms wickAwayAtWithConstant_two_of_chiSubfamily_pointwise_bounds
#print axioms wickAwayAtWithConstant_two_of_chiSubfamily_shifted_omitted_rate
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_shifted_omitted_rate_gate
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms wickForIncidenceAwayAt_two_of_chiFamily_of_constant_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_of_constant_le_one
#print axioms wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_constant_le_one
#print axioms rawFourthMomentWithDiagonal_of_chiFamily_quarticWeil_of_constant_le_one
#print axioms
  wickForIncidenceAwayAt_two_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms
  rawFourthMomentWithDiagonal_of_chiFamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
#print axioms r19_linearK_incidenceMomentAway_of_chiFamily

end ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
