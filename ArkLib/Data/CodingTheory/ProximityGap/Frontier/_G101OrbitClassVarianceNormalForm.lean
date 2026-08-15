/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88CrossOrbitFirstIncidence

/-!
# G101: cleared variance normal form for the orbit-class mass profile

G88 writes the production wall as a positive quadratic form in the kernel mass `S₀` and the
nonzero class masses `Sγ`.  This file gives its exact deviation normal form:

* the number `k` of nonzero classes satisfies `n*k = q-1`;
* the pairwise deviation `D = ∑γ∑δ(Sγ-Sδ)²` satisfies
  `D = 2(k∑γ Sγ² - (∑γ Sγ)²)`;
* consequently the centered mass is the equidistributed baseline plus exactly `q*D` after clearing
  the denominator `2k`.

Thus all non-kernel profile freedom is concentrated in one manifestly nonnegative quantity `D`.
Issue #509.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm

open scoped BigOperators
open Finset
open G88CrossOrbitFirstIncidence
open ArkLib.ProximityGap.Frontier.R365CenteredShadowMassWeld
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The nonzero field values partition into `n`-element rotation classes. -/
theorem card_orbitClassSet_mul
    (g : F) (n : ℕ) (hg0 : g ≠ 0) (hn : 0 < n) (hord : orderOf g = n) :
    n * (orbitClassSet F n).card = Fintype.card F - 1 := by
  classical
  have hpart : (nonkernelValues F).card =
      ∑ γ ∈ orbitClassSet F n, (orbitClassFiber n γ).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun c : F => c ^ n) (s := nonkernelValues F) (t := orbitClassSet F n)
      (fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have hfib : ∀ γ ∈ orbitClassSet F n, (orbitClassFiber n γ).card = n := by
    intro γ hγ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hγ
    have hc0 : c ≠ 0 := (Finset.mem_filter.mp hc).2
    exact card_orbitClassFiber g n hg0 hn hord hc0
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul] at hpart
  have hnonkernel : (nonkernelValues F).card = Fintype.card F - 1 := by
    rw [nonkernelValues_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ]
  calc
    n * (orbitClassSet F n).card = (orbitClassSet F n).card * n := by ring
    _ = (nonkernelValues F).card := hpart.symm
    _ = Fintype.card F - 1 := hnonkernel

/-- Pairwise squared differences are the cleared variance around the uniform profile. -/
theorem sum_pairwise_sub_sq
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, (f i - f j) ^ 2 =
      2 * (((S.card : ℝ) * ∑ i ∈ S, (f i) ^ 2) - (∑ i ∈ S, f i) ^ 2) := by
  have hpoint : ∀ i j, (f i - f j) ^ 2 = f i ^ 2 + f j ^ 2 - 2 * (f i * f j) := by
    intros
    ring
  simp_rw [hpoint]
  let A := ∑ i ∈ S, f i ^ 2
  let B := ∑ i ∈ S, f i
  have hinner : ∀ i ∈ S,
      ∑ j ∈ S, (f i ^ 2 + f j ^ 2 - 2 * (f i * f j)) =
        (S.card : ℝ) * f i ^ 2 + A - 2 * f i * B := by
    intro i hi
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show ∑ j ∈ S, 2 * (f i * f j) = 2 * f i * B by
      simp only [B, Finset.mul_sum]; ring]
  have hprod : ∑ i ∈ S, ∑ j ∈ S, f i * f j = B ^ 2 := by
    change (∑ i ∈ S, ∑ j ∈ S, f i * f j) = (∑ i ∈ S, f i) ^ 2
    rw [sq, Finset.sum_mul_sum]
  have hcross : ∑ i ∈ S, ∑ j ∈ S, 2 * f i * f j = 2 * B ^ 2 := by
    calc
      (∑ i ∈ S, ∑ j ∈ S, 2 * f i * f j) =
          2 * (∑ i ∈ S, ∑ j ∈ S, f i * f j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2 * B ^ 2 := by rw [hprod]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [A, B, Finset.mul_sum]
  push_cast
  rw [hcross]
  ring

/-- Pairwise nonuniformity of the realized nonzero orbit-class masses. -/
noncomputable def orbitClassDeviation (g : F) (n r : ℕ) : ℝ :=
  ∑ γ ∈ orbitClassSet F n, ∑ δ ∈ orbitClassSet F n,
    (orbitClassMass g n r γ - orbitClassMass g n r δ) ^ 2

theorem orbitClassDeviation_eq (g : F) (n r : ℕ) :
    orbitClassDeviation g n r =
      2 * ((((orbitClassSet F n).card : ℝ) *
          ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2) -
        (((n : ℝ) ^ r - (repRF g n r 0 : ℝ)) ^ 2)) := by
  unfold orbitClassDeviation
  rw [sum_pairwise_sub_sq, sum_orbitClassMass_eq]

theorem orbitClassDeviation_nonneg (g : F) (n r : ℕ) :
    0 ≤ orbitClassDeviation g n r := by
  unfold orbitClassDeviation
  positivity

/-- **Exact deviation normal form.**  After clearing `2k`, G88's centered mass is the
equidistributed baseline plus exactly `q` times the pairwise deviation `D`. -/
theorem centeredShadowMass_deviation_normalForm
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) * centeredShadowMass g n m r =
      (Fintype.card F : ℝ) *
          (2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
              (repRF g n r 0 : ℝ) ^ 2 +
            2 * (((n : ℝ) ^ r - (repRF g n r 0 : ℝ)) ^ 2) +
            orbitClassDeviation g n r) -
        2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) * (n : ℝ) ^ (2 * r) := by
  have hpar := centeredShadowMass_orbitClassParseval g n m r hg0 hord hm hn hg
  have hdev := orbitClassDeviation_eq g n r
  linear_combination 2 * ((orbitClassSet F n).card : ℝ) * hpar +
    -(Fintype.card F : ℝ) * hdev

/-- **The production wall in deviation coordinates.**  The kernel mass and the pairwise class
deviation are not merely sufficient statistics: after clearing `2k`, their displayed inequality
is equivalent to `DCEnergyBound`. -/
theorem dcEnergyBound_iff_kernel_deviation_le
    (g : F) (n m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n)
    (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    ArkLib.ProximityGap.DCEnergyCorrection.DCEnergyBound
        (ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n) r ↔
      (Fintype.card F : ℝ) *
          (2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
              (repRF g n r 0 : ℝ) ^ 2 +
            2 * (((n : ℝ) ^ r - (repRF g n r 0 : ℝ)) ^ 2) +
            orbitClassDeviation g n r) ≤
        2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
          ((Fintype.card F : ℝ) *
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
                ((ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n).card : ℝ) ^ r) +
            (n : ℝ) ^ (2 * r)) := by
  have hn0 : 0 < n := by omega
  have hk0 : 0 < (orbitClassSet F n).card := by
    apply Finset.card_pos.mpr
    refine ⟨(1 : F) ^ n, Finset.mem_image.mpr ⟨1, ?_, rfl⟩⟩
    simp [nonkernelValues]
  have hscale : (0 : ℝ) < 2 * ((orbitClassSet F n).card : ℝ) := by positivity
  have hwall := dcEnergyBound_iff_orbitClassParseval_le g n m r hg0 hord hm hn hg
  have hdev := orbitClassDeviation_eq g n r
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left (hwall.mp h) hscale.le
    calc
      (Fintype.card F : ℝ) *
          (2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
              (repRF g n r 0 : ℝ) ^ 2 +
            2 * (((n : ℝ) ^ r - (repRF g n r 0 : ℝ)) ^ 2) +
            orbitClassDeviation g n r) =
          (2 * ((orbitClassSet F n).card : ℝ)) *
            ((Fintype.card F : ℝ) *
              ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
                ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2)) := by
            rw [hdev]
            ring
      _ ≤ (2 * ((orbitClassSet F n).card : ℝ)) *
          ((n : ℝ) * ((Fintype.card F : ℝ) *
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
                ((ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n).card : ℝ) ^ r)) +
            (n : ℝ) * (n : ℝ) ^ (2 * r)) := hm
      _ = 2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
          ((Fintype.card F : ℝ) *
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
                ((ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n).card : ℝ) ^ r) +
            (n : ℝ) ^ (2 * r)) := by ring
  · intro h
    apply hwall.mpr
    apply le_of_mul_le_mul_left _ hscale
    calc
      (2 * ((orbitClassSet F n).card : ℝ)) *
          ((Fintype.card F : ℝ) *
            ((n : ℝ) * (repRF g n r 0 : ℝ) ^ 2 +
              ∑ γ ∈ orbitClassSet F n, orbitClassMass g n r γ ^ 2)) =
        (Fintype.card F : ℝ) *
          (2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
              (repRF g n r 0 : ℝ) ^ 2 +
            2 * (((n : ℝ) ^ r - (repRF g n r 0 : ℝ)) ^ 2) +
            orbitClassDeviation g n r) := by
          rw [hdev]
          ring
      _ ≤ 2 * ((orbitClassSet F n).card : ℝ) * (n : ℝ) *
          ((Fintype.card F : ℝ) *
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
                ((ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n).card : ℝ) ^ r) +
            (n : ℝ) ^ (2 * r)) := h
      _ = (2 * ((orbitClassSet F n).card : ℝ)) *
          ((n : ℝ) * ((Fintype.card F : ℝ) *
              ((Nat.doubleFactorial (2 * r - 1) : ℝ) *
                ((ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy.powerRootSet g n).card : ℝ) ^ r)) +
            (n : ℝ) * (n : ℝ) ^ (2 * r)) := by ring

end ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm

#print axioms
  ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm.card_orbitClassSet_mul
#print axioms
  ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm.sum_pairwise_sub_sq
#print axioms
  ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm.centeredShadowMass_deviation_normalForm
#print axioms
  ArkLib.ProximityGap.Frontier.G101OrbitClassVarianceNormalForm.dcEnergyBound_iff_kernel_deviation_le
