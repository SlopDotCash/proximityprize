/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22SexticConvolutionCollapse

/-!
# LANE B2 (#466 round 23): the calibrated r = 3 named input and its consumer chain —
  plus the probe finding that NO spike correction is needed at the Jacobi level

## Probe verdict (`probe_r23_tripleconv_energy.py`, profile follow-up; collapse identity
   validated to 1e-13 against the Lean `tripleConv`)

* the triple-convolution energy satisfies `∑_d ‖(J∗J∗J)(d)‖² / (6·m³q³) ∈ [1.5, 3.2]` across
  all probed cells (n = 8/16/32, β = 2.5–4.6), FLUCTUATING and O(1)-bounded — the Gaussian
  constant 6 is right up to a small absolute factor;
* **no spike structure**: the top-5 indices carry only 5–18% of the energy (shrinking in `m`),
  and the profile is flat at `‖tc(d)‖ ≈ 3·m·q^{3/2}` — unlike level 0 (rounds 15–16), the
  Jacobi level needs NO diagonal deletion; the excess over Gaussian is distributed arithmetic
  correlation (the Gauss-angle correlations — Katz territory);
* `‖J_j‖ ∈ {1, √q}` exactly as classical theory predicts (one degenerate index).

## What this brick lands

* `TripleConvEnergyBound C` — the calibrated NAMED OPEN INPUT: `∑_d ‖(J∗J∗J)(d)‖² ≤ C·m³·q³`
  (`C = 40` covers every probed cell with ≥ 2× margin; the Gaussian prediction is `C = 6`);
* `sextic_moment_of_tripleConvEnergyBound` — the consumer: the named input yields the r = 3
  rung for the face, `∑_{s≠0} ‖T‖⁶ ≤ C·(q−1)·m³·q³`, by the round-22 exact collapse;
* `sup_pureFace_of_tripleConvEnergyBound` — the sixth-moment pointwise consequence:
  `‖T(s)‖ ≤ (C·(q−1)·m³·q³)^{1/6}` for every `s ≠ 0`.

This completes the normal-form program for the delimited open core: the r = 3 rung is ONE
named, probe-calibrated, manifestly-nonnegative inequality about an explicit sequence, with
its full consumer chain to the tower machine-checked.  CORE OPEN, ON-BGK.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 23, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R21QuarticConvolutionCollapse
open ArkLib.ProximityGap.Frontier.R22SexticConvolutionCollapse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F}

/-- **The calibrated named open input (the campaign's delimited r = 3 core).**
Triple-convolution energy of the coefficient sequence at Wick scale: probes give
ratio-to-`6m³q³` in `[1.5, 3.2]` with no spike structure; `C = 40` is comfortable. -/
def TripleConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3

/-- **Quartic convolution energy input.**  Wick-scale control of the quadratic convolution
coefficients.  By finite Young/Cauchy, this is already enough to imply the R23 sextic input
when the Jacobi coefficients satisfy `‖J_j‖² ≤ q`. -/
def SelfConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 ≤ C * (m : ℝ) * (q : ℝ) ^ 2

/-! ### Proven baseline: triangle-inequality convolution energy -/

/-- A uniform coefficient bound gives the elementary pointwise bound
`‖J∗J‖∞ ≤ m B²`.  This is the no-cancellation baseline for the quadratic convolution. -/
theorem norm_selfConv_le_card_mul_bound (J : ZMod m → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) (c : ZMod m) :
    ‖selfConv J c‖ ≤ (m : ℝ) * B ^ 2 := by
  classical
  calc ‖selfConv J c‖
      ≤ ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0),
          ‖J j * J (c - j)‖ := by
        unfold selfConv
        exact norm_sum_le _ _
    _ ≤ ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0),
          B ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_mul]
        exact (mul_le_mul (hJ j) (hJ (c - j)) (norm_nonneg _) hB0).trans_eq (by ring)
    _ = (((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card : ℝ)
          * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) * B ^ 2 := by
        have hcard : (((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card : ℝ)
            ≤ (m : ℝ) := by
          have hle : ((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card
              ≤ (Finset.univ : Finset (ZMod m)).card :=
            Finset.card_le_card (by
              intro j hj
              exact Finset.mem_univ j)
          simpa [ZMod.card] using (Nat.cast_le.mpr hle : _)
        exact mul_le_mul_of_nonneg_right hcard (sq_nonneg B)

/-- A uniform coefficient bound gives the elementary pointwise bound
`‖J∗J∗J‖∞ ≤ m² B³`.  This is pure triangle inequality; it intentionally records the
`m²` loss that the prize-scale r = 3 input must remove by arithmetic cancellation. -/
theorem norm_tripleConv_le_card_sq_mul_bound (J : ZMod m → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) (d : ZMod m) :
    ‖tripleConv J d‖ ≤ (m : ℝ) ^ 2 * B ^ 3 := by
  classical
  have hself : ∀ c : ZMod m, ‖selfConv J c‖ ≤ (m : ℝ) * B ^ 2 :=
    norm_selfConv_le_card_mul_bound J hB0 hJ
  calc ‖tripleConv J d‖
      ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, ‖selfConv J (d - j) * J j‖ := by
        unfold tripleConv
        exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, (m : ℝ) * B ^ 3 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_mul]
        calc ‖selfConv J (d - j)‖ * ‖J j‖
            ≤ ((m : ℝ) * B ^ 2) * B :=
              mul_le_mul (hself (d - j)) (hJ j) (norm_nonneg _) (by positivity)
          _ = (m : ℝ) * B ^ 3 := by ring
    _ = (((Finset.univ \ {(0 : ZMod m)}).card : ℝ) * ((m : ℝ) * B ^ 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m : ℝ) ^ 2 * B ^ 3 := by
        have hcard : (((Finset.univ \ {(0 : ZMod m)}).card : ℝ) ≤ (m : ℝ)) := by
          have hle : (Finset.univ \ {(0 : ZMod m)}).card
              ≤ (Finset.univ : Finset (ZMod m)).card :=
            Finset.card_le_card (by
              intro j hj
              exact Finset.mem_univ j)
          simpa [ZMod.card] using (Nat.cast_le.mpr hle : _)
        have hnon : 0 ≤ (m : ℝ) * B ^ 3 := by positivity
        calc (((Finset.univ \ {(0 : ZMod m)}).card : ℝ) * ((m : ℝ) * B ^ 3))
            ≤ (m : ℝ) * ((m : ℝ) * B ^ 3) :=
              mul_le_mul_of_nonneg_right hcard hnon
          _ = (m : ℝ) ^ 2 * B ^ 3 := by ring

/-- **Trivial triple-convolution energy baseline.**  If every coefficient has norm at most
`B`, then `∑d ‖J∗J∗J(d)‖² ≤ m⁵ B⁶`.  Compared with the desired Wick scale
`O(m³ q³)`, the triangle-inequality baseline loses exactly `m²` when `B² ≲ q`. -/
theorem tripleConv_energy_le_card_pow_five_mul_bound (J : ZMod m → ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hJ : ∀ j : ZMod m, ‖J j‖ ≤ B) :
    ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ (m : ℝ) ^ 5 * B ^ 6 := by
  classical
  have hpt : ∀ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ ((m : ℝ) ^ 2 * B ^ 3) ^ 2 := by
    intro d
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_tripleConv_le_card_sq_mul_bound J hB0 hJ d) 2
  calc ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ ∑ _d : ZMod m, ((m : ℝ) ^ 2 * B ^ 3) ^ 2 := Finset.sum_le_sum (fun d _ => hpt d)
    _ = ((Finset.univ : Finset (ZMod m)).card : ℝ) * ((m : ℝ) ^ 2 * B ^ 3) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) ^ 5 * B ^ 6 := by
        simp [ZMod.card]
        ring

/-! ### Young/Cauchy bridge from quartic to sextic convolution energy -/

/-- **Finite Young/Cauchy bridge.**  A square bound for the coefficient sequence and the
quadratic-convolution energy bound the triple-convolution energy by
`m² q · ∑c ‖J∗J(c)‖²`.

This is still analytic-neutral: it says that once the r = 2 convolution profile is Wick-small,
the r = 3 named input follows with no further cancellation bookkeeping. -/
theorem tripleConv_energy_le_selfConvEnergy_mul_card_sq (J : ZMod m → ℂ) (q : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) :
    ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * (m : ℝ) ^ 2 * (q : ℝ) := by
  classical
  let S : Finset (ZMod m) := Finset.univ \ {(0 : ZMod m)}
  have hJsum : ∑ j ∈ S, ‖J j‖ ^ 2 ≤ (m : ℝ) * (q : ℝ) := by
    calc ∑ j ∈ S, ‖J j‖ ^ 2
        ≤ ∑ _j ∈ S, (q : ℝ) := Finset.sum_le_sum (fun j _ => hJ j)
      _ = (S.card : ℝ) * (q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (q : ℝ) := by
          have hcard : (S.card : ℝ) ≤ (m : ℝ) := by
            have hle : S.card ≤ (Finset.univ : Finset (ZMod m)).card :=
              Finset.card_le_card (by intro j _; exact Finset.mem_univ j)
            simpa [S, ZMod.card] using (Nat.cast_le.mpr hle : (S.card : ℝ) ≤ _)
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hpoint : ∀ d : ZMod m,
      ‖tripleConv J d‖ ^ 2
        ≤ (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * ((m : ℝ) * (q : ℝ)) := by
    intro d
    have hnorm : ‖tripleConv J d‖
        ≤ ∑ j ∈ S, ‖selfConv J (d - j)‖ * ‖J j‖ := by
      calc ‖tripleConv J d‖
          ≤ ∑ j ∈ S, ‖selfConv J (d - j) * J j‖ := by
              unfold tripleConv
              exact norm_sum_le _ _
        _ = ∑ j ∈ S, ‖selfConv J (d - j)‖ * ‖J j‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [norm_mul]
    have hsqnorm :
        ‖tripleConv J d‖ ^ 2
          ≤ (∑ j ∈ S, ‖selfConv J (d - j)‖ * ‖J j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs :
        (∑ j ∈ S, ‖selfConv J (d - j)‖ * ‖J j‖) ^ 2
          ≤ (∑ j ∈ S, ‖selfConv J (d - j)‖ ^ 2) * ∑ j ∈ S, ‖J j‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S
        (fun j => ‖selfConv J (d - j)‖) (fun j => ‖J j‖)
    have hself :
        ∑ j ∈ S, ‖selfConv J (d - j)‖ ^ 2
          ≤ ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 := by
      have hsub :
          ∑ j ∈ S, ‖selfConv J (d - j)‖ ^ 2
            ≤ ∑ j : ZMod m, ‖selfConv J (d - j)‖ ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (by intro j hj; exact Finset.mem_univ j)
          (by intro j _ _; positivity)
      have hbij : Function.Bijective (fun j : ZMod m => d - j) := by
        refine ⟨?_, ?_⟩
        · intro a b hab
          linear_combination -hab
        · intro c
          refine ⟨d - c, ?_⟩
          ring
      have hreindex :
          ∑ j : ZMod m, ‖selfConv J (d - j)‖ ^ 2
            = ∑ c : ZMod m, ‖selfConv J c‖ ^ 2 := by
        exact Fintype.sum_bijective (fun j : ZMod m => d - j) hbij _ _ (fun j => rfl)
      exact hsub.trans_eq hreindex
    calc ‖tripleConv J d‖ ^ 2
        ≤ (∑ j ∈ S, ‖selfConv J (d - j)‖ * ‖J j‖) ^ 2 := hsqnorm
      _ ≤ (∑ j ∈ S, ‖selfConv J (d - j)‖ ^ 2) * ∑ j ∈ S, ‖J j‖ ^ 2 := hcs
      _ ≤ (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * ((m : ℝ) * (q : ℝ)) :=
          mul_le_mul hself hJsum (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ ∑ _d : ZMod m, (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * ((m : ℝ) * (q : ℝ)) :=
        Finset.sum_le_sum (fun d _ => hpoint d)
    _ = (m : ℝ) * ((∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * ((m : ℝ) * (q : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [ZMod.card]
    _ = (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * (m : ℝ) ^ 2 * (q : ℝ) := by ring

/-- **Quartic input ⇒ sextic input.**  If the quadratic convolution is Wick-small and
`‖J_j‖² ≤ q`, then the R23 triple-convolution energy input follows with the same constant. -/
theorem tripleConvEnergyBound_of_selfConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) {C : ℝ}
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) (hself : SelfConvEnergyBound J q C) :
    TripleConvEnergyBound J q C := by
  unfold TripleConvEnergyBound SelfConvEnergyBound at *
  have hbase := tripleConv_energy_le_selfConvEnergy_mul_card_sq J q hJ
  have hmul : (0 : ℝ) ≤ (m : ℝ) ^ 2 * (q : ℝ) := by positivity
  calc ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ (∑ c : ZMod m, ‖selfConv J c‖ ^ 2) * (m : ℝ) ^ 2 * (q : ℝ) := hbase
    _ ≤ (C * (m : ℝ) * (q : ℝ) ^ 2) * (m : ℝ) ^ 2 * (q : ℝ) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hself hmul
    _ = C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

/-- If `‖J_j‖² ≤ q`, the triangle-inequality baseline supplies the named r = 3 input with
constant `m²`.  The prize-scale problem is precisely to replace this formal `m²` by an
absolute constant using arithmetic cancellation of the Jacobi phases. -/
theorem tripleConvEnergyBound_of_uniform_sq_bound (J : ZMod m → ℂ) (q : ℕ)
    (hJ : ∀ j : ZMod m, ‖J j‖ ^ 2 ≤ (q : ℝ)) :
    TripleConvEnergyBound J q ((m : ℝ) ^ 2) := by
  classical
  have hB0 : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hJroot : ∀ j : ZMod m, ‖J j‖ ≤ Real.sqrt (q : ℝ) := by
    intro j
    have h := Real.sqrt_le_sqrt (hJ j)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hbase := tripleConv_energy_le_card_pow_five_mul_bound J hB0 hJroot
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 6 = (q : ℝ) ^ 3 := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    have hs2 : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
    calc (Real.sqrt (q : ℝ)) ^ 6
        = ((Real.sqrt (q : ℝ)) ^ 2) ^ 3 := by ring
      _ = (q : ℝ) ^ 3 := by rw [hs2]
  unfold TripleConvEnergyBound
  calc ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2
      ≤ (m : ℝ) ^ 5 * (Real.sqrt (q : ℝ)) ^ 6 := hbase
    _ = (m : ℝ) ^ 5 * (q : ℝ) ^ 3 := by rw [hsqrt]
    _ = (m : ℝ) ^ 2 * (m : ℝ) ^ 3 * (q : ℝ) ^ 3 := by ring

/-- **Consumer: the named input IS the r = 3 rung for the face** (via the round-22 exact
collapse — no analytic content in this step). -/
theorem sextic_moment_of_tripleConvEnergyBound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {C : ℝ}
    (h : TripleConvEnergyBound J (Fintype.card F) C) :
    ∑ s ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  rw [sextic_convolution_collapse hfam hgrp J]
  have hq : (0:ℝ) ≤ ((Fintype.card F - 1 : ℕ) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left h hq

/-- **Pointwise consequence: the sixth-moment sup bound.**  For every `s ≠ 0`,
`‖T(s)‖⁶ ≤ C·(q−1)·m³·q³`; taking sixth roots is left to consumers (kept in power form to
avoid `rpow` plumbing). -/
theorem sup_pureFace_of_tripleConvEnergyBound (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (J : ZMod m → ℂ) {C : ℝ}
    (h : TripleConvEnergyBound J (Fintype.card F) C) {s : F} (hs : s ≠ 0) :
    ‖pureFace J lam s‖ ^ 6
      ≤ ((Fintype.card F - 1 : ℕ) : ℝ) * (C * (m : ℝ) ^ 3 * (Fintype.card F : ℝ) ^ 3) := by
  have hmem : s ∈ Finset.univ.erase (0 : F) :=
    Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩
  have hsingle : ‖pureFace J lam s‖ ^ 6
      ≤ ∑ s' ∈ Finset.univ.erase (0 : F), ‖pureFace J lam s'‖ ^ 6 :=
    Finset.single_le_sum (f := fun s' => ‖pureFace J lam s'‖ ^ 6)
      (fun s' _ => by positivity) hmem
  exact le_trans hsingle (sextic_moment_of_tripleConvEnergyBound hfam hgrp J h)

end ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  norm_selfConv_le_card_mul_bound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  norm_tripleConv_le_card_sq_mul_bound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  tripleConv_energy_le_card_pow_five_mul_bound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  tripleConv_energy_le_selfConvEnergy_mul_card_sq
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  tripleConvEnergyBound_of_selfConvEnergyBound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  tripleConvEnergyBound_of_uniform_sq_bound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  sextic_moment_of_tripleConvEnergyBound
open ArkLib.ProximityGap.Frontier.R23TripleConvEnergyInput in
#print axioms
  sup_pureFace_of_tripleConvEnergyBound
