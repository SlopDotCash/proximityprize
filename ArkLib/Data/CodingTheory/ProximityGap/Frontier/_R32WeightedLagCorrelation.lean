/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R31LagSpectrumWeilBound

/-!
# LANE B2 (#466 round 32): the WEIGHTED lag-correlation collapse — the master identity
  subsuming round 30 and powering the r = 3 cross terms

For arbitrary weights `f, g : F → ℂ` and the λ-transforms `c_f(i) = ∑_z f(z)·λ_i(z)`:

  **`weighted_lag_correlation`** :
  `∑_i c_f(i+t)·conj(c_g(i)) = m · ∑_{u∈G} ∑_w f(u·w)·conj(g(w))·λ_t(w)`.

Round 30 is the special case `f = g = χ(1−·)`.  The r = 3 decomposition's four-`J` cross
terms are the case of pair-product weights (each `J_{j+a}·J_j` is itself a λ-transform of a
two-variable convolution weight, by the `pureFace_sq` mechanism) — so this ONE lemma collapses
every balanced correlation of every derived sequence in the tower.  Pure orthogonality.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 32, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R24InvolutionNoGo
open ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- The λ-transform of a weight: `c_f(i) = ∑_z f(z)·λ_i(z)`. -/
noncomputable def lamTransform (lam : ZMod m → F → ℂ) (f : F → ℂ) (i : ZMod m) : ℂ :=
  ∑ z : F, f z * lam i z

/-- **THE WEIGHTED LAG-CORRELATION COLLAPSE (round-32 main theorem).** -/
theorem weighted_lag_correlation
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam)
    (f g : F → ℂ) (hf0 : f 0 = 0) (t : ZMod m) :
    ∑ i : ZMod m, lamTransform lam f (i + t) * (starRingEnd ℂ) (lamTransform lam g i)
      = (m : ℂ) * ∑ u ∈ G, ∑ w : F, f (u * w) * (starRingEnd ℂ) (g w) * lam t w := by
  classical
  have hexp : ∀ i : ZMod m,
      lamTransform lam f (i + t) * (starRingEnd ℂ) (lamTransform lam g i)
        = ∑ z : F, ∑ w : F, (f z * (starRingEnd ℂ) (g w))
            * (lam (i + t) z * (starRingEnd ℂ) (lam i w)) := by
    intro i
    rw [lamTransform, lamTransform, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i)]
  rw [Finset.sum_comm]
  have hswap : ∀ z : F,
      ∑ i : ZMod m, ∑ w : F, (f z * (starRingEnd ℂ) (g w))
          * (lam (i + t) z * (starRingEnd ℂ) (lam i w))
      = ∑ w : F, ∑ i : ZMod m, (f z * (starRingEnd ℂ) (g w))
          * (lam (i + t) z * (starRingEnd ℂ) (lam i w)) := fun z => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun z _ => hswap z)]
  have hinner : ∀ z w : F, w ≠ 0 →
      ∑ i : ZMod m, lam (i + t) z * (starRingEnd ℂ) (lam i w)
        = lam t z * ((m : ℂ) * (if z * w⁻¹ ∈ G then 1 else 0)) := by
    intro z w hw
    have hpt : ∀ i : ZMod m, lam (i + t) z * (starRingEnd ℂ) (lam i w)
        = lam t z * lam i (z * w⁻¹) := by
      intro i
      calc lam (i + t) z * (starRingEnd ℂ) (lam i w)
          = (lam i z * lam i w⁻¹) * lam t z := by
            rw [hgrp.add_eq_mul i t z, ← lam_inv_eq_conj hfam hgrp i hw]
            ring
        _ = lam t z * lam i (z * w⁻¹) := by
            rw [← hfam.map_mul i z w⁻¹]
            ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.mul_sum,
      hfam.indicator (z * w⁻¹)]
  have hw0 : ∀ z : F,
      ∑ i : ZMod m, (f z * (starRingEnd ℂ) (g (0:F)))
          * (lam (i + t) z * (starRingEnd ℂ) (lam i (0:F))) = 0 := by
    intro z
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hfam.map_zero i]
    simp
  have hmain : ∑ z : F, ∑ w : F, ∑ i : ZMod m,
      (f z * (starRingEnd ℂ) (g w)) * (lam (i + t) z * (starRingEnd ℂ) (lam i w))
      = (m : ℂ) * ∑ w ∈ Finset.univ.erase (0 : F), ∑ z : F,
          (if z * w⁻¹ ∈ G then 1 else 0)
            * (f z * (starRingEnd ℂ) (g w) * lam t z) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
      (f := fun w => ∑ z : F, ∑ i : ZMod m,
        (f z * (starRingEnd ℂ) (g w)) * (lam (i + t) z * (starRingEnd ℂ) (lam i w)))
      (by simpa using Finset.sum_eq_zero (fun z _ => hw0 z))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hw' : w ≠ 0 := (Finset.mem_erase.mp hw).1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    calc ∑ i : ZMod m, (f z * (starRingEnd ℂ) (g w))
          * (lam (i + t) z * (starRingEnd ℂ) (lam i w))
        = (f z * (starRingEnd ℂ) (g w))
            * ∑ i : ZMod m, lam (i + t) z * (starRingEnd ℂ) (lam i w) := by
          rw [Finset.mul_sum]
      _ = (f z * (starRingEnd ℂ) (g w))
            * (lam t z * ((m : ℂ) * (if z * w⁻¹ ∈ G then 1 else 0))) := by
          rw [hinner z w hw']
      _ = (m : ℂ) * ((if z * w⁻¹ ∈ G then 1 else 0)
            * (f z * (starRingEnd ℂ) (g w) * lam t z)) := by ring
  rw [hmain]
  congr 1
  have hrow : ∀ w ∈ Finset.univ.erase (0 : F),
      ∑ z : F, (if z * w⁻¹ ∈ G then (1:ℂ) else 0)
          * (f z * (starRingEnd ℂ) (g w) * lam t z)
      = ∑ u ∈ G, f (u * w) * (starRingEnd ℂ) (g w) * lam t w := by
    intro w hw
    have hw0' : w ≠ 0 := (Finset.mem_erase.mp hw).1
    have hite : ∀ z : F, (if z * w⁻¹ ∈ G then (1:ℂ) else 0)
        * (f z * (starRingEnd ℂ) (g w) * lam t z)
        = (if z * w⁻¹ ∈ G then f z * (starRingEnd ℂ) (g w) * lam t z else 0) := by
      intro z
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun z _ => hite z), ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun z => z * w⁻¹) (fun u => u * w) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_assoc, mul_inv_cancel₀ hw0', mul_one]
      exact hu
    · intro z _
      dsimp only
      rw [mul_assoc, inv_mul_cancel₀ hw0', mul_one]
    · intro u _
      dsimp only
      rw [mul_assoc, mul_inv_cancel₀ hw0', mul_one]
    · intro z hz
      dsimp only
      have hmem : z * w⁻¹ ∈ G := (Finset.mem_filter.mp hz).2
      have hzw : z * w⁻¹ * w = z := by
        rw [mul_assoc, inv_mul_cancel₀ hw0', mul_one]
      rw [hzw]
      have hlam : lam t z = lam t w := by
        have hz_eq : z = (z * w⁻¹) * w := hzw.symm
        rw [hz_eq, hfam.map_mul t (z * w⁻¹) w,
          lam_eq_one_on_G hfam hgrp hmem t, one_mul]
      rw [hlam]
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0:F))]
  rw [mul_zero, hf0]
  simp

end ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R32WeightedLagCorrelation.weighted_lag_correlation
