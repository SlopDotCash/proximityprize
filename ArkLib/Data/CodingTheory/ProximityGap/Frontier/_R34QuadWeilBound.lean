/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R33QuadViaWeights

/-!
# LANE B2 (#466 round 34): the four-`J` correlations are surface-Weil-small — the cross
  class of the r = 3 decomposition, bounded

Round 33 made every balanced four-`J` correlation exact:
`∑_j J_{j+t₁}J_{j+t₂}·conj(J_{j+s₁}J_j) = m·∑_{u∈G}∑_w W_{t₂−t₁}(u·w)·conj(W_{s₁}(w))·λ_{t₁}(w)`.
Each inner `w`-sum is (after expanding the two pair-weights) a THREE-free-variable complete
character sum — the Deligne surface class, with expected cancellation `C·q^{3/2}`.  This brick
names that input and lands the machine-checked consumer:

  **`quad_correlation_bound`** : under `SurfaceWeilInput`, for all lag data,
  `‖∑_j J_{j+t₁}J_{j+t₂}·conj(J_{j+s₁}J_j)‖ ≤ m·|G|·C·q^{3/2}`.

Against the trivial scale `m·q²` (four coefficients of modulus `√q`, `m` terms), this is a
`√q`-saving — the exact analogue at the pair level of round 31's bound at the singleton
level.  With it, the r = 3 matching decomposition's cross class is CONTROLLED (mod the named
surface input); the sole remaining open object is the fully-unmatched sextic class.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 34, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R34QuadWeilBound

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation
open ArkLib.ProximityGap.Frontier.R33QuadViaWeights

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- **Named input (surface Weil, Deligne class)**: the `w`-sums of the round-33 collapse have
`q^{3/2}` cancellation, uniformly over `u ∈ G` and lag data with `t₁ ≠ 0`.  After expanding
both pair-weights this is a three-free-variable complete character sum over an explicit
surface; the classical input mirrors rounds 17/31 one level up. -/
def SurfaceWeilInput (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ u ∈ G, ∀ a b t : ZMod m, t ≠ 0 →
    ‖∑ w : F, pairWeight χ lam a (u * w)
        * (starRingEnd ℂ) (pairWeight χ lam b w) * lam t w‖
      ≤ C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)

/-- Monotonicity of the surface-Weil input in the cancellation constant. -/
theorem surfaceWeilInput_mono {C C' : ℝ} (hCC' : C ≤ C')
    (hC : SurfaceWeilInput χ lam G C) :
    SurfaceWeilInput χ lam G C' := by
  intro u hu a b t ht
  exact (hC u hu a b t ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC' (by positivity)) (by positivity))

/-- Off-diagonal pair-weight correlation budget: the round-33 surface sum only for leading
lag `t₁ ≠ 0`, matching the actual domain of the surface-Weil input. -/
def OffDiagPairWeightCorrelationBound
    (χ : F → ℂ) (lam : ZMod m → F → ℂ) (G : Finset F) (B : ℝ) : Prop :=
  ∀ t₁ t₂ s₁ : ZMod m, t₁ ≠ 0 →
    ‖∑ u ∈ G, ∑ w : F,
        pairWeight χ lam (t₂ - t₁) (u * w)
          * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖ ≤ B

/-- Monotonicity of the off-diagonal pair-weight budget. -/
theorem offDiagPairWeightCorrelationBound_mono {B B' : ℝ} (hBB' : B ≤ B')
    (hB : OffDiagPairWeightCorrelationBound χ lam G B) :
    OffDiagPairWeightCorrelationBound χ lam G B' := by
  intro t₁ t₂ s₁ ht₁
  exact (hB t₁ t₂ s₁ ht₁).trans hBB'

/-- The all-lag pair-weight correlation budget from round 33 supplies the off-diagonal
budget used by the surface-Weil consumer. -/
theorem offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound
    {B : ℝ} (hB : PairWeightCorrelationBound χ lam G B) :
    OffDiagPairWeightCorrelationBound χ lam G B := by
  intro t₁ t₂ s₁ _ht₁
  exact hB t₁ t₂ s₁

/-- The surface-Weil input supplies the off-diagonal round-33 pair-weight correlation budget
after summing over `u ∈ G`.  The later four-`J` bound then only loses the forced factor `m`. -/
theorem offDiagPairWeightCorrelationBound_of_surfaceWeilInput
    {C : ℝ} (hweil : SurfaceWeilInput χ lam G C) :
    OffDiagPairWeightCorrelationBound χ lam G
      ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ))) := by
  intro t₁ t₂ s₁ ht₁
  calc ‖∑ u ∈ G, ∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
        * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖
      ≤ ∑ u ∈ G, ‖∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
          * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ G, C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        exact hweil u hu (t₂ - t₁) s₁ t₁ ht₁
    _ = (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Four-`J` bound from the off-diagonal pair-weight budget. -/
theorem quad_correlation_bound_of_offDiagPairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : OffDiagPairWeightCorrelationBound χ lam G B)
    {t₁ t₂ s₁ : ZMod m} (ht₁ : t₁ ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * B := by
  rw [quad_correlation_via_weights hfam hgrp t₁ t₂ s₁]
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hB t₁ t₂ s₁ ht₁) (by positivity)

/-- Four-`J` bound from a sharper off-diagonal pair-weight budget, spent at a looser budget. -/
theorem quad_correlation_bound_of_offDiagPairWeightCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : OffDiagPairWeightCorrelationBound χ lam G B)
    {t₁ t₂ s₁ : ZMod m} (ht₁ : t₁ ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * B' :=
  quad_correlation_bound_of_offDiagPairWeightCorrelationBound hfam hgrp
    (offDiagPairWeightCorrelationBound_mono hBB' hB) ht₁

/-- Off-diagonal four-`J` bound from the all-lag pair-weight budget. -/
theorem offDiag_quad_correlation_bound_of_pairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : PairWeightCorrelationBound χ lam G B)
    {t₁ t₂ s₁ : ZMod m} (ht₁ : t₁ ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * B :=
  quad_correlation_bound_of_offDiagPairWeightCorrelationBound hfam hgrp
    (offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound hB) ht₁

/-- Off-diagonal four-`J` bound from a sharper all-lag pair-weight budget, spent at a looser
budget. -/
theorem offDiag_quad_correlation_bound_of_pairWeightCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : PairWeightCorrelationBound χ lam G B)
    {t₁ t₂ s₁ : ZMod m} (ht₁ : t₁ ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * B' :=
  quad_correlation_bound_of_offDiagPairWeightCorrelationBound_le hfam hgrp hBB'
    (offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound hB) ht₁

/-- Aggregate off-diagonal four-`J` energy from the named pair-weight budget. -/
theorem offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : OffDiagPairWeightCorrelationBound χ lam G B) :
    ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B) ^ 2) := by
  classical
  have hpoint : ∀ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
      ∀ t₂ s₁ : ZMod m,
        ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
            * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
          ≤ (((m : ℝ) * B) ^ 2) := by
    intro t₁ ht₁ t₂ s₁
    have ht₁0 : t₁ ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp ht₁).2
      simpa using hnot
    exact pow_le_pow_left₀ (norm_nonneg _)
      (quad_correlation_bound_of_offDiagPairWeightCorrelationBound hfam hgrp hB ht₁0
        (t₂ := t₂) (s₁ := s₁)) 2
  calc ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ ∑ _t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
          ∑ _t₂ : ZMod m, ∑ _s₁ : ZMod m, ((m : ℝ) * B) ^ 2 := by
        refine Finset.sum_le_sum (fun t₁ ht₁ => ?_)
        refine Finset.sum_le_sum (fun t₂ _ => ?_)
        exact Finset.sum_le_sum (fun s₁ _ => hpoint t₁ ht₁ t₂ s₁)
    _ = (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
        rw [Finset.card_sdiff]
        have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
        have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
        simp [ZMod.card, Nat.cast_sub hm1]
        ring

/-- Aggregate off-diagonal four-`J` energy from a sharper named pair-weight budget, spent at a
looser budget. -/
theorem offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : OffDiagPairWeightCorrelationBound χ lam G B) :
    ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B') ^ 2) :=
  offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound hfam hgrp
    (offDiagPairWeightCorrelationBound_mono hBB' hB)

/-- Aggregate off-diagonal four-`J` energy from the all-lag pair-weight budget. -/
theorem offDiag_quad_correlation_energy_bound_of_pairWeightCorrelationBound
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B : ℝ} (hB : PairWeightCorrelationBound χ lam G B) :
    ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B) ^ 2) :=
  offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound hfam hgrp
    (offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound hB)

/-- Aggregate off-diagonal four-`J` energy from a sharper all-lag pair-weight budget, spent at a
looser budget. -/
theorem offDiag_quad_correlation_energy_bound_of_pairWeightCorrelationBound_le
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    {B B' : ℝ} (hBB' : B ≤ B') (hB : PairWeightCorrelationBound χ lam G B) :
    ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (((m : ℝ) * B') ^ 2) :=
  offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound_le hfam hgrp hBB'
    (offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound hB)

/-- **THE QUAD-CORRELATION BOUND (round-34 main theorem).**  Under the named surface input,
every balanced four-`J` correlation at lag `t₁ ≠ 0` satisfies
`‖∑_j J_{j+t₁}J_{j+t₂}·conj(J_{j+s₁}J_j)‖ ≤ m·|G|·C·q^{3/2}` — the cross class of the r = 3
matching decomposition is controlled. -/
theorem quad_correlation_bound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hweil : SurfaceWeilInput χ lam G C)
    {t₁ t₂ s₁ : ZMod m} (ht₁ : t₁ ≠ 0) :
    ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
        * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖
      ≤ (m : ℝ) * (G.card : ℝ) * C
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)) := by
  rw [quad_correlation_via_weights hfam hgrp t₁ t₂ s₁]
  rw [norm_mul, Complex.norm_natCast]
  have hsum : ‖∑ u ∈ G, ∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
        * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖
      ≤ (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)) := by
    calc ‖∑ u ∈ G, ∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
          * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖
        ≤ ∑ u ∈ G, ‖∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
            * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖ := norm_sum_le _ _
      _ ≤ ∑ _u ∈ G, C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ) :=
          Finset.sum_le_sum (fun u hu => hweil u hu (t₂ - t₁) s₁ t₁ ht₁)
      _ = (G.card : ℝ) * (C * Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (m : ℝ) * ‖∑ u ∈ G, ∑ w : F, pairWeight χ lam (t₂ - t₁) (u * w)
        * (starRingEnd ℂ) (pairWeight χ lam s₁ w) * lam t₁ w‖
      ≤ (m : ℝ) * ((G.card : ℝ) * (C * Real.sqrt (Fintype.card F)
          * (Fintype.card F : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ) * (G.card : ℝ) * C
          * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ)) := by ring

/-- **Aggregate cross-class energy bound.**  Summing the pointwise round-34 estimate over all
lag triples with the leading lag `t₁ ≠ 0` gives the `L²` budget consumed by variance-style
r = 3 decompositions. -/
theorem offDiag_quad_correlation_energy_bound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam)
    {C : ℝ} (hweil : SurfaceWeilInput χ lam G C) :
    ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * (G.card : ℝ) * C
              * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ))) ^ 2) := by
  classical
  let B : ℝ := (m : ℝ) * (G.card : ℝ) * C
    * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ))
  have hpoint : ∀ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
      ∀ t₂ s₁ : ZMod m,
        ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
            * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
          ≤ B ^ 2 := by
    intro t₁ ht₁ t₂ s₁
    have ht₁0 : t₁ ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp ht₁).2
      simpa using hnot
    have hle := quad_correlation_bound hfam hgrp hweil ht₁0 (t₂ := t₂) (s₁ := s₁)
    dsimp [B] at hle ⊢
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc ∑ t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
        ∑ t₂ : ZMod m, ∑ s₁ : ZMod m,
          ‖∑ j : ZMod m, jacobiCoeff χ lam (j + t₁) * jacobiCoeff χ lam (j + t₂)
              * (starRingEnd ℂ) (jacobiCoeff χ lam (j + s₁) * jacobiCoeff χ lam j)‖ ^ 2
      ≤ ∑ _t₁ ∈ (Finset.univ \ ({(0 : ZMod m)} : Finset (ZMod m))),
          ∑ _t₂ : ZMod m, ∑ _s₁ : ZMod m, B ^ 2 := by
        refine Finset.sum_le_sum (fun t₁ ht₁ => ?_)
        refine Finset.sum_le_sum (fun t₂ _ => ?_)
        exact Finset.sum_le_sum (fun s₁ _ => hpoint t₁ ht₁ t₂ s₁)
    _ = (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ)) * (B ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
        rw [Finset.card_sdiff]
        have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
        have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
        simp [ZMod.card, Nat.cast_sub hm1]
        ring
    _ = (((m : ℝ) - 1) * (m : ℝ) * (m : ℝ))
          * (((m : ℝ) * (G.card : ℝ) * C
              * (Real.sqrt (Fintype.card F) * (Fintype.card F : ℝ))) ^ 2) := rfl

end ArkLib.ProximityGap.Frontier.R34QuadWeilBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R34QuadWeilBound.surfaceWeilInput_mono
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiagPairWeightCorrelationBound_mono
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiagPairWeightCorrelationBound_of_pairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiagPairWeightCorrelationBound_of_surfaceWeilInput
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms quad_correlation_bound_of_offDiagPairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms quad_correlation_bound_of_offDiagPairWeightCorrelationBound_le
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_bound_of_pairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_bound_of_pairWeightCorrelationBound_le
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_energy_bound_of_offDiagPairWeightCorrelationBound_le
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_energy_bound_of_pairWeightCorrelationBound
open ArkLib.ProximityGap.Frontier.R34QuadWeilBound in
#print axioms offDiag_quad_correlation_energy_bound_of_pairWeightCorrelationBound_le
#print axioms ArkLib.ProximityGap.Frontier.R34QuadWeilBound.quad_correlation_bound
#print axioms ArkLib.ProximityGap.Frontier.R34QuadWeilBound.offDiag_quad_correlation_energy_bound
