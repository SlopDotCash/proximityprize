/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Mellin–Jacobi factorization, Deuring–Birch second moment, and coset trace cancellation

For an odd-characteristic finite field `F`, the Legendre elliptic character sum is
`L(λ) = ∑ z : F, χ(z * (z - 1) * (z - λ))`, which governs the fourth-moment cross-ratio
coupling `⟨V_A, L⟩` of `paley-cross-ratio-moments.md`.

This file proves, completely axiom-clean and with zero external Weil/Deligne axioms:

1. **Exact Mellin–Jacobi identity (`mellin_jacobi_identity`)**:
   For EVERY commutative ring `R` and EVERY multiplicative character `ψ : MulChar F R`
   (including `ψ = 1` and `ψ = χ`),
   `∑ lam ∈ Fˣ, ψ lam * L(lam) = χ(-1) * J(ψ, χ)²`,
   where `J(ψ, χ) = ∑ x ∈ Fˣ, ψ x * χ(1 - x)`.
2. **Exact special values and QR/NQR partition identities**:
   - `legendreTrace_zero`: `L(0) = -χ(-1)` and `legendreTrace_one`: `L(1) = -1`.
   - `sum_legendreTrace_eq_zero`: `∑ lam : F, L(lam) = 0`.
   - `sum_legendreTrace_qr` & `sum_legendreTrace_nqr`:
     `∑_{λ ∈ QR} L(λ) = χ(-1)` and `∑_{λ ∈ NQR} L(λ) = 0` identically!
3. **Exact Birch/Deuring second moment (`sum_sq_legendreTrace`)**:
   `∑ lam : F, L(lam)² = |F|² - 2|F| - 1` and `∑_{λ ≠ 0, 1} L(λ)² = |F|² - 2|F| - 3`.
4. **Exact Jacobi modulus (`jacobiSum_norm_sq_eq_card`)**:
   For every complex multiplicative character `ψ : MulChar F ℂ` with `ψ ≠ 1` and `ψ ≠ χ`,
   `‖J(ψ, χ)‖² = |F|` (proved purely from quadratic character sums and orthogonality,
   without Gauss sums), and `‖J(ψ, χ)‖² = 1` for `ψ ∈ {1, χ}`.
5. **Unconditional coset-averaged elliptic trace cancellation (`abs_sum_coset_legendreTrace_le`)**:
   For EVERY multiplicative subgroup `H ≤ Fˣ` and EVERY coset `aH`,
   `|∑ lam ∈ aH, L(lam)| ≤ |F|` — strictly beating the trivial Hasse bound `2 |H| √|F|` for
   every subgroup of size `|H| > √|F| / 2`, proved unconditionally without Deligne!
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace ProximityGap.PaleyMellinJacobi

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. Definitions and elementary quadratic character sum -/

/-- The Legendre elliptic character sum `L(λ) = ∑ z : F, χ(z * (z - 1) * (z - λ))`. -/
def legendreTrace (lam : F) : ℤ :=
  ∑ z : F, quadraticChar F (z * (z - 1) * (z - lam))

/-- The Jacobi sum `J(ψ, χ) = ∑ x ∈ Fˣ, ψ x * χ(1 - x)` valued in any commutative ring `R`. -/
def jacobiSum {R : Type*} [CommRing R] (ψ : F → R) : R :=
  ∑ x ∈ Finset.univ.erase (0 : F), ψ x * (quadraticChar F (1 - x) : R)

private theorem linear_sum_zero (hF : ringChar F ≠ 2) (a : F) :
    ∑ s : F, quadraticChar F (s - a) = 0 := by
  have hbi : Function.Bijective (fun s : F => s - a) := (Equiv.subRight a).bijective
  rw [Fintype.sum_bijective (fun s : F => s - a) hbi _ _ (fun _ => rfl)]
  exact quadraticChar_sum_zero hF

private theorem quadratic_sum_neg_one (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ s : F, quadraticChar F ((s - a) * (s - b)) = -1 := by
  classical
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hbi1 : Function.Bijective (fun u : F => a + (b - a) * u) :=
    (Equiv.addLeft a).bijective.comp (mulLeft_bijective₀ (b - a) hba)
  have hstep1 : ∑ s : F, quadraticChar F ((s - a) * (s - b)) =
      ∑ u : F, quadraticChar F (u * (u - 1)) := by
    rw [← Fintype.sum_bijective (fun u : F => a + (b - a) * u) hbi1 _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have harg : (a + (b - a) * u - a) * (a + (b - a) * u - b) = (b - a) ^ 2 * (u * (u - 1)) := by
      ring
    rw [harg, map_mul, quadraticChar_sq_one' hba, one_mul]
  rw [hstep1]
  have hstep2 : ∑ u : F, quadraticChar F (u * (u - 1)) =
      ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), zero_mul, MulChar.map_zero, zero_add]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have harg : u * (u - 1) = u ^ 2 * (1 - u⁻¹) := by field_simp [hu0]
    rw [harg, map_mul, quadraticChar_sq_one' hu0, one_mul]
  rw [hstep2]
  have hbij : ∑ u ∈ Finset.univ.erase (0 : F), quadraticChar F (1 - u⁻¹) =
      ∑ v ∈ Finset.univ.erase (1 : F), quadraticChar F v := by
    refine Finset.sum_nbij' (fun u => 1 - u⁻¹) (fun v => (1 - v)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      rw [Finset.mem_erase]
      exact ⟨fun h => inv_ne_zero hu0 (sub_eq_self.mp h), Finset.mem_univ _⟩
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      rw [Finset.mem_erase]
      exact ⟨inv_ne_zero (sub_ne_zero.mpr hv1.symm), Finset.mem_univ _⟩
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      field_simp [hu0]; ring
    · intro v hv
      have hv1 : v ≠ 1 := (Finset.mem_erase.mp hv).1
      have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
      field_simp [h1v]; ring
    · intro _ _; rfl
  rw [hbij]
  have htot := quadraticChar_sum_zero hF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F)), map_one] at htot
  omega

/-! ## 2. Exact Mellin–Jacobi identity -/

/-- **Exact Mellin–Jacobi factorization of the Legendre elliptic trace**:
for ANY commutative ring `R` and ANY function `ψ : F → R` multiplicative on `Fˣ`
(`∀ a b, a ≠ 0 → b ≠ 0 → ψ (a * b) = ψ a * ψ b`),
`∑ lam ∈ Fˣ, ψ lam * L(lam) = χ(-1) * J(ψ, χ)²`. -/
theorem mellin_jacobi_identity {R : Type*} [CommRing R] (ψ : F → R)
    (hψ : ∀ a b : F, a ≠ 0 → b ≠ 0 → ψ (a * b) = ψ a * ψ b) :
    ∑ lam ∈ Finset.univ.erase (0 : F), ψ lam * (legendreTrace lam : R) =
      (quadraticChar F (-1 : F) : R) * (jacobiSum ψ) ^ 2 := by
  classical
  have hL : ∀ lam : F, (legendreTrace lam : R) =
      ∑ z ∈ Finset.univ.erase (0 : F),
        (quadraticChar F (z * (z - 1) * (z - lam)) : R) := fun lam => by
    unfold legendreTrace
    push_cast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
      zero_mul, zero_mul, MulChar.map_zero, Int.cast_zero, zero_add]
  simp_rw [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ z ∈ Finset.univ.erase (0 : F),
      ∑ lam ∈ Finset.univ.erase (0 : F),
          ψ lam * (quadraticChar F (z * (z - 1) * (z - lam)) : R) =
        (quadraticChar F (-1 : F) : R) * (ψ z * (quadraticChar F (1 - z) : R)) * jacobiSum ψ := by
    intro z hz
    have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
    have hbij : ∑ lam ∈ Finset.univ.erase (0 : F),
          ψ lam * (quadraticChar F (z * (z - 1) * (z - lam)) : R) =
        ∑ u ∈ Finset.univ.erase (0 : F),
          ψ (z * u) * (quadraticChar F (z * (z - 1) * (z - z * u)) : R) := by
      refine Finset.sum_nbij' (fun lam => lam / z) (fun u => z * u) ?_ ?_ ?_ ?_ ?_
      · intro lam hlam
        rw [Finset.mem_erase] at hlam ⊢
        exact ⟨div_ne_zero hlam.1 hz0, Finset.mem_univ _⟩
      · intro u hu
        rw [Finset.mem_erase] at hu ⊢
        exact ⟨mul_ne_zero hz0 hu.1, Finset.mem_univ _⟩
      · intro lam _; exact mul_div_cancel₀ lam hz0
      · intro u _; exact mul_div_cancel_left₀ u hz0
      · intro lam _; rw [mul_div_cancel₀ lam hz0]
    rw [hbij, jacobiSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have harg : z * (z - 1) * (z - z * u) = z ^ 2 * ((-1) * (1 - z) * (1 - u)) := by ring
    rw [hψ z u hz0 hu0, harg, map_mul, quadraticChar_sq_one' hz0, one_mul,
      map_mul, map_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.mul_sum, jacobiSum, sq]
  ring

/-! ## 3. Special values, QR/NQR exact sums, and Deuring–Birch second moment -/

theorem legendreTrace_zero (hF : ringChar F ≠ 2) :
    legendreTrace (0 : F) = -quadraticChar F (-1 : F) := by
  unfold legendreTrace
  have hterm : ∀ z : F, quadraticChar F (z * (z - 1) * (z - 0)) =
      if z = 0 then 0 else quadraticChar F (z - 1) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · simp only [hz, ↓reduceIte, sub_zero]
      rw [show z * (z - 1) * z = z ^ 2 * (z - 1) by ring, map_mul,
        quadraticChar_sq_one' hz, one_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  simp only [↓reduceIte, zero_add]
  have hlin := linear_sum_zero hF (1 : F)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), zero_sub] at hlin
  have hcongr : ∑ z ∈ Finset.univ.erase (0 : F), (if z = 0 then (0 : ℤ) else quadraticChar F (z - 1)) =
      ∑ z ∈ Finset.univ.erase (0 : F), quadraticChar F (z - 1) :=
    Finset.sum_congr rfl fun z hz => by simp [(Finset.mem_erase.mp hz).1]
  rw [hcongr]
  omega

theorem legendreTrace_one (hF : ringChar F ≠ 2) :
    legendreTrace (1 : F) = -1 := by
  unfold legendreTrace
  have hterm : ∀ z : F, quadraticChar F (z * (z - 1) * (z - 1)) =
      if z = 1 then 0 else quadraticChar F z := by
    intro z
    by_cases hz : z = 1
    · simp [hz]
    · simp only [hz, ↓reduceIte]
      have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
      rw [show z * (z - 1) * (z - 1) = (z - 1) ^ 2 * z by ring, map_mul,
        quadraticChar_sq_one' hz1, one_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F))]
  simp only [↓reduceIte, zero_add]
  have htot := quadraticChar_sum_zero hF
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : F)), map_one] at htot
  have hcongr : ∑ z ∈ Finset.univ.erase (1 : F), (if z = 1 then (0 : ℤ) else quadraticChar F z) =
      ∑ z ∈ Finset.univ.erase (1 : F), quadraticChar F z :=
    Finset.sum_congr rfl fun z hz => by simp [(Finset.mem_erase.mp hz).1]
  rw [hcongr]
  omega

theorem sum_legendreTrace_eq_zero (hF : ringChar F ≠ 2) :
    ∑ lam : F, legendreTrace lam = 0 := by
  unfold legendreTrace
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  have hfac : ∀ lam : F, quadraticChar F (z * (z - 1) * (z - lam)) =
      quadraticChar F (-(z * (z - 1))) * quadraticChar F (lam - z) := fun lam => by
    rw [← map_mul, show -(z * (z - 1)) * (lam - z) = z * (z - 1) * (z - lam) by ring]
  simp_rw [hfac, ← Finset.mul_sum, linear_sum_zero hF z, mul_zero]

theorem jacobiSum_one (hF : ringChar F ≠ 2) :
    jacobiSum (fun _ : F => (1 : ℤ)) = -1 := by
  unfold jacobiSum
  simp only [one_mul, Int.cast_id]
  have htot := quadraticChar_sum_zero hF
  have hbi : Function.Bijective (fun x : F => 1 - x) := by
    refine ⟨fun a b h => by linear_combination -h, fun y => ⟨1 - y, by ring⟩⟩
  have hsum : ∑ x : F, quadraticChar F (1 - x) = 0 := by
    rw [Fintype.sum_bijective (fun x : F => 1 - x) hbi _ _ (fun _ => rfl)]
    exact htot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)), sub_zero, map_one] at hsum
  omega

/-- Exact quadratic Jacobi sum: `J(χ, χ) = -χ(-1)`. -/
theorem jacobiSum_quad_eq (hF : ringChar F ≠ 2) :
    jacobiSum (fun x : F => quadraticChar F x) = -quadraticChar F (-1 : F) := by
  unfold jacobiSum
  simp only [Int.cast_id]
  have hq := quadratic_sum_neg_one hF (zero_ne_one : (0 : F) ≠ 1)
  have hzero : ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x * quadraticChar F (1 - x) =
      ∑ x : F, quadraticChar F (x * (1 - x)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
      zero_mul, MulChar.map_zero, zero_add]
    exact Finset.sum_congr rfl fun x _ => (map_mul _ _ _).symm
  rw [hzero]
  have hpt : ∀ x : F, quadraticChar F (x * (1 - x)) =
      quadraticChar F (-1 : F) * quadraticChar F ((x - 0) * (x - 1)) := fun x => by
    rw [← map_mul]; congr 1; ring
  simp_rw [hpt, ← Finset.mul_sum, hq, mul_neg_one]

/-- Exact sum of Legendre elliptic traces over all quadratic residues: `∑_{λ ∈ QR} L(λ) = χ(-1)`. -/
theorem sum_legendreTrace_qr (hF : ringChar F ≠ 2) :
    ∑ lam ∈ Finset.univ.filter (fun x : F => quadraticChar F x = 1), legendreTrace lam =
      quadraticChar F (-1 : F) := by
  have h1 := mellin_jacobi_identity (R := ℤ) (fun _ : F => (1 : ℤ)) (fun _ _ _ _ => by ring)
  simp only [one_mul, Int.cast_id, jacobiSum_one hF] at h1
  have h2 := mellin_jacobi_identity (R := ℤ) (fun x => quadraticChar F x)
    (fun a b _ _ => map_mul _ a b)
  simp only [Int.cast_id, jacobiSum_quad_eq hF] at h2
  have hneg_sq : (-quadraticChar F (-1 : F)) ^ 2 = 1 := by
    rw [neg_sq]
    exact quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  rw [hneg_sq, mul_one] at h2
  rw [neg_one_sq, mul_one] at h1
  have hcomb : ∑ lam ∈ Finset.univ.erase (0 : F),
      (1 + quadraticChar F lam) * legendreTrace lam = 2 * quadraticChar F (-1 : F) := by
    have : ∀ lam : F, (1 + quadraticChar F lam) * legendreTrace lam =
        legendreTrace lam + quadraticChar F lam * legendreTrace lam := fun lam => by ring
    simp_rw [this, Finset.sum_add_distrib, h1, h2]
    ring
  have hfilt : ∑ lam ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F lam) * legendreTrace lam =
      2 * ∑ lam ∈ Finset.univ.filter (fun x : F => quadraticChar F x = 1), legendreTrace lam := by
    rw [Finset.mul_sum]
    have h0 : (Finset.univ.filter fun x : F => quadraticChar F x = 1) ⊆ Finset.univ.erase (0 : F) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      refine ⟨fun h => ?_, Finset.mem_univ _⟩
      rw [h, MulChar.map_zero] at hx
      norm_num at hx
    rw [← Finset.sum_subset h0]
    · refine Finset.sum_congr rfl fun lam hlam => ?_
      have hq := (Finset.mem_filter.mp hlam).2
      rw [hq]; ring
    · intro lam hlam hnot
      rw [Finset.mem_filter] at hnot
      have hne0 : lam ≠ 0 := (Finset.mem_erase.mp hlam).1
      rcases quadraticChar_dichotomy hne0 with h | h
      · exact absurd ⟨Finset.mem_univ _, h⟩ hnot
      · rw [h]; ring
  rw [hfilt] at hcomb
  omega

/-- Exact vanishing of Legendre elliptic traces summed over all quadratic non-residues:
`∑_{λ ∈ NQR} L(λ) = 0` identically in every odd-characteristic finite field! -/
theorem sum_legendreTrace_nqr (hF : ringChar F ≠ 2) :
    ∑ lam ∈ Finset.univ.filter (fun x : F => quadraticChar F x = -1), legendreTrace lam = 0 := by
  have h1 := mellin_jacobi_identity (R := ℤ) (fun _ : F => (1 : ℤ)) (fun _ _ _ _ => by ring)
  simp only [one_mul, Int.cast_id, jacobiSum_one hF, neg_one_sq, mul_one] at h1
  have h2 := mellin_jacobi_identity (R := ℤ) (fun x => quadraticChar F x)
    (fun a b _ _ => map_mul _ a b)
  simp only [Int.cast_id, jacobiSum_quad_eq hF] at h2
  have hneg_sq : (-quadraticChar F (-1 : F)) ^ 2 = 1 := by
    rw [neg_sq]; exact quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  rw [hneg_sq, mul_one] at h2
  have hcomb : ∑ lam ∈ Finset.univ.erase (0 : F),
      (1 - quadraticChar F lam) * legendreTrace lam = 0 := by
    have : ∀ lam : F, (1 - quadraticChar F lam) * legendreTrace lam =
        legendreTrace lam - quadraticChar F lam * legendreTrace lam := fun lam => by ring
    simp_rw [this, Finset.sum_sub_distrib, h1, h2, sub_self]
  have hfilt : ∑ lam ∈ Finset.univ.erase (0 : F), (1 - quadraticChar F lam) * legendreTrace lam =
      2 * ∑ lam ∈ Finset.univ.filter (fun x : F => quadraticChar F x = -1), legendreTrace lam := by
    rw [Finset.mul_sum]
    have h0 : (Finset.univ.filter fun x : F => quadraticChar F x = -1) ⊆ Finset.univ.erase (0 : F) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      refine ⟨fun h => ?_, Finset.mem_univ _⟩
      rw [h, MulChar.map_zero] at hx
      norm_num at hx
    rw [← Finset.sum_subset h0]
    · refine Finset.sum_congr rfl fun lam hlam => ?_
      have hq := (Finset.mem_filter.mp hlam).2
      rw [hq]; ring
    · intro lam hlam hnot
      rw [Finset.mem_filter] at hnot
      have hne0 : lam ≠ 0 := (Finset.mem_erase.mp hlam).1
      rcases quadraticChar_dichotomy hne0 with h | h
      · rw [h]; ring
      · exact absurd ⟨Finset.mem_univ _, h⟩ hnot
  rw [hfilt] at hcomb
  omega

/-- **Exact Birch/Deuring second moment of the Legendre elliptic trace**:
`∑ lam : F, L(lam)² = |F|² - 2|F| - 1` for every odd-characteristic finite field `F`. -/
theorem sum_sq_legendreTrace (hF : ringChar F ≠ 2) :
    ∑ lam : F, (legendreTrace lam) ^ 2 =
      (Fintype.card F : ℤ) ^ 2 - 2 * Fintype.card F - 1 := by
  classical
  let g (z : F) : ℤ := quadraticChar F (z * (z - 1))
  have hexp : ∀ lam : F, (legendreTrace lam) ^ 2 =
      ∑ z : F, ∑ w : F, g z * g w * quadraticChar F ((lam - z) * (lam - w)) := fun lam => by
    unfold legendreTrace
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    dsimp only [g]
    have h1 : quadraticChar F (z * (z - 1) * (z - lam)) *
          quadraticChar F (w * (w - 1) * (w - lam)) =
        quadraticChar F (z * (z - 1)) * quadraticChar F (w * (w - 1)) *
          quadraticChar F ((lam - z) * (lam - w)) := by
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1; ring
    exact h1
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∑ z : F, ∑ lam : F, ∑ w : F, g z * g w * quadraticChar F ((lam - z) * (lam - w)) =
      ∑ z : F, ∑ w : F, g z * g w * ∑ lam : F, quadraticChar F ((lam - z) * (lam - w)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have hinner : ∀ z w : F,
      ∑ lam : F, quadraticChar F ((lam - z) * (lam - w)) =
        if z = w then (Fintype.card F : ℤ) - 1 else -1 := by
    intro z w
    by_cases hzw : z = w
    · subst hzw
      simp only [↓reduceIte]
      have hterm : ∀ lam : F, quadraticChar F ((lam - z) * (lam - z)) = if lam = z then 0 else 1 := by
        intro lam
        by_cases h : lam = z
        · simp [h]
        · simp only [h, ↓reduceIte, ← sq]
          exact quadraticChar_sq_one' (sub_ne_zero.mpr h)
      rw [Finset.sum_congr rfl fun lam _ => hterm lam, ← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
      simp only [↓reduceIte, zero_add]
      have hcongr : ∑ lam ∈ Finset.univ.erase z, (if lam = z then (0 : ℤ) else 1) =
          ∑ _lam ∈ Finset.univ.erase z, (1 : ℤ) :=
        Finset.sum_congr rfl fun lam hlam => by simp [(Finset.mem_erase.mp hlam).1]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ z),
        Finset.card_univ]
      have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
      omega
    · simp only [hzw, ↓reduceIte]
      exact quadratic_sum_neg_one hF hzw
  simp_rw [hinner]
  have hsplit : ∀ z w : F,
      g z * g w * (if z = w then (Fintype.card F : ℤ) - 1 else -1) =
        (if z = w then (Fintype.card F : ℤ) * g z ^ 2 else 0) - g z * g w := by
    intro z w
    by_cases h : z = w
    · subst h; simp only [↓reduceIte]; ring
    · simp only [h, ↓reduceIte]; ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  have hdiag : ∑ z : F, ∑ w : F, (if z = w then (Fintype.card F : ℤ) * g z ^ 2 else 0) =
      (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 2) := by
    have h1 : ∀ z : F, ∑ w : F, (if z = w then (Fintype.card F : ℤ) * g z ^ 2 else 0) =
        (Fintype.card F : ℤ) * g z ^ 2 := fun z => by
      rw [Finset.sum_ite_eq Finset.univ z]
      simp
    simp_rw [h1, ← Finset.mul_sum]
    congr 1
    have hg2 : ∀ z : F, g z ^ 2 = if z = 0 ∨ z = 1 then 0 else 1 := fun z => by
      dsimp only [g]
      by_cases h0 : z = 0
      · simp [h0]
      · by_cases h1 : z = 1
        · simp [h1]
        · simp only [h0, h1, or_self, ↓reduceIte]
          exact quadraticChar_sq_one (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    simp_rw [hg2]
    have h01 : (0 : F) ≠ 1 := zero_ne_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
    simp only [true_or, ↓reduceIte, zero_add]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : F)⟩)]
    simp only [or_true, ↓reduceIte, zero_add]
    have hcongr : ∑ z ∈ (Finset.univ.erase (0 : F)).erase 1,
          (if z = 0 ∨ z = 1 then (0 : ℤ) else 1) =
        ∑ _z ∈ (Finset.univ.erase (0 : F)).erase 1, (1 : ℤ) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have h1 := (Finset.mem_erase.mp hz).1
      have h0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
      simp [h0, h1]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ (1 : F)⟩),
      Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
    have hcard2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  have hoff : ∑ z : F, ∑ w : F, g z * g w = 1 := by
    rw [← Finset.sum_mul_sum]
    have hgsum : ∑ z : F, g z = -1 := by
      have h := quadratic_sum_neg_one hF (zero_ne_one : (0 : F) ≠ 1)
      simpa only [g, sub_zero] using h
    rw [hgsum]; ring
  rw [hdiag, hoff]; ring

/-- Punctured second moment: `∑_{λ ≠ 0, 1} L(λ)² = |F|² - 2|F| - 3`. -/
theorem sum_sq_legendreTrace_punctured (hF : ringChar F ≠ 2) :
    ∑ lam ∈ (Finset.univ.erase (0 : F)).erase 1, (legendreTrace lam) ^ 2 =
      (Fintype.card F : ℤ) ^ 2 - 2 * Fintype.card F - 3 := by
  have htot := sum_sq_legendreTrace hF
  have h01 : (1 : F) ∈ Finset.univ.erase (0 : F) :=
    Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
    ← Finset.add_sum_erase _ _ h01, legendreTrace_zero hF, legendreTrace_one hF] at htot
  have hneg_sq : (-quadraticChar F (-1 : F)) ^ 2 = 1 := by
    rw [neg_sq]; exact quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
  rw [hneg_sq] at htot
  linarith

/-! ## 4. Exact Jacobi modulus `‖J(ψ, χ)‖² = |F|` and coset trace cancellation -/

/-- Exact modulus squared of the Jacobi sum `J(ψ, χ)`:
for any multiplicative map `ψ : F → ℂ` on `Fˣ` satisfying `ψ (a * b) = ψ a * ψ b`, `ψ 1 = 1`,
and unit-modulus conjugation `star (ψ a) = ψ a⁻¹`,
if `∑_{u ≠ 0} ψ u = 0` and `∑_{u ≠ 0} ψ u * χ(u) = 0`, then `‖J(ψ, χ)‖² = |F|`. -/
theorem jacobiSum_norm_sq_eq_card (hF : ringChar F ≠ 2) (ψ : F → ℂ)
    (hψ_mul : ∀ a b : F, a ≠ 0 → b ≠ 0 → ψ (a * b) = ψ a * ψ b)
    (hψ_one : ψ 1 = 1)
    (hψ_conj : ∀ a : F, a ≠ 0 → starRingEnd ℂ (ψ a) = ψ a⁻¹)
    (hψ_orth1 : ∑ u ∈ Finset.univ.erase (0 : F), ψ u = 0)
    (hψ_orth2 : ∑ u ∈ Finset.univ.erase (0 : F), ψ u * (quadraticChar F u : ℂ) = 0) :
    ‖jacobiSum ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  classical
  have hmul : jacobiSum ψ * starRingEnd ℂ (jacobiSum ψ) = (Fintype.card F : ℂ) := by
    unfold jacobiSum
    rw [map_sum, Finset.sum_mul_sum]
    have hterm : ∀ x ∈ Finset.univ.erase (0 : F), ∀ y ∈ Finset.univ.erase (0 : F),
        ψ x * (quadraticChar F (1 - x) : ℂ) * starRingEnd ℂ (ψ y * (quadraticChar F (1 - y) : ℂ)) =
          ψ (x * y⁻¹) * (quadraticChar F ((1 - x) * (1 - y)) : ℂ) := by
      intro x hx y hy
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
      rw [map_mul, hψ_conj y hy0, map_intCast, hψ_mul x y⁻¹ hx0 (inv_ne_zero hy0), map_mul]
      push_cast
      ring
    calc ∑ x ∈ Finset.univ.erase (0 : F), ∑ y ∈ Finset.univ.erase (0 : F),
            ψ x * (quadraticChar F (1 - x) : ℂ) *
              starRingEnd ℂ (ψ y * (quadraticChar F (1 - y) : ℂ))
        = ∑ y ∈ Finset.univ.erase (0 : F), ∑ x ∈ Finset.univ.erase (0 : F),
            ψ (x * y⁻¹) * (quadraticChar F ((1 - x) * (1 - y)) : ℂ) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => hterm x hx y hy
      _ = ∑ y ∈ Finset.univ.erase (0 : F), ∑ u ∈ Finset.univ.erase (0 : F),
            ψ u * (quadraticChar F ((1 - u * y) * (1 - y)) : ℂ) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
          refine Finset.sum_nbij' (fun x => x * y⁻¹) (fun u => u * y) ?_ ?_ ?_ ?_ ?_
          · intro x hx
            rw [Finset.mem_erase] at hx ⊢
            exact ⟨mul_ne_zero hx.1 (inv_ne_zero hy0), Finset.mem_univ _⟩
          · intro u hu
            rw [Finset.mem_erase] at hu ⊢
            exact ⟨mul_ne_zero hu.1 hy0, Finset.mem_univ _⟩
          · intro x _; exact inv_mul_cancel_right₀ hy0 x
          · intro u _; exact mul_inv_cancel_right₀ hy0 u
          · intro x _; rw [inv_mul_cancel_right₀ hy0 x]
      _ = ∑ u ∈ Finset.univ.erase (0 : F),
            ψ u * (∑ y ∈ Finset.univ.erase (0 : F), (quadraticChar F ((1 - u * y) * (1 - y)) : ℂ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ u ∈ Finset.univ.erase (0 : F),
            ψ u * (if u = 1 then ((Fintype.card F : ℂ) - 2)
                   else -(quadraticChar F u : ℂ) - 1) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          congr 1
          have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
          by_cases hu1 : u = 1
          · subst hu1
            simp only [↓reduceIte, one_mul]
            have hpt : ∀ y ∈ Finset.univ.erase (0 : F),
                (quadraticChar F ((1 - y) * (1 - y)) : ℂ) = if y = 1 then 0 else 1 := fun y _ => by
              by_cases hy1 : y = 1
              · simp [hy1]
              · simp only [hy1, ↓reduceIte, ← sq]
                rw [quadraticChar_sq_one' (sub_ne_zero.mpr (Ne.symm hy1))]
                simp
            rw [Finset.sum_congr rfl hpt]
            have h1mem : (1 : F) ∈ Finset.univ.erase (0 : F) :=
              Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
            rw [← Finset.add_sum_erase _ _ h1mem]
            simp only [↓reduceIte, zero_add]
            have hcongr : ∑ y ∈ (Finset.univ.erase (0 : F)).erase 1,
                  (if y = 1 then (0 : ℂ) else 1) =
                ∑ _y ∈ (Finset.univ.erase (0 : F)).erase 1, (1 : ℂ) :=
              Finset.sum_congr rfl fun y hy => by simp [(Finset.mem_erase.mp hy).1]
            rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one,
              Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem (Finset.mem_univ (0 : F)),
              Finset.card_univ]
            have hcard2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
            rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F - 1),
              Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
            push_cast; ring
          · simp only [hu1, ↓reduceIte]
            have huinv : u⁻¹ ≠ 1 := fun h => hu1 (by rw [← inv_inv u, h, inv_one])
            have hfull : ∑ y : F, quadraticChar F ((1 - u * y) * (1 - y)) = -quadraticChar F u := by
              have hpt : ∀ y : F, quadraticChar F ((1 - u * y) * (1 - y)) =
                  quadraticChar F u * quadraticChar F ((y - u⁻¹) * (y - 1)) := fun y => by
                rw [← map_mul]; congr 1; field_simp [hu0]; ring
              simp_rw [hpt, ← Finset.mul_sum, quadratic_sum_neg_one hF huinv, mul_neg_one]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
              mul_zero, sub_zero, mul_one, map_one] at hfull
            have hsum_int : ∑ y ∈ Finset.univ.erase (0 : F),
                quadraticChar F ((1 - u * y) * (1 - y)) = -quadraticChar F u - 1 := by omega
            have hsum_C : ((∑ y ∈ Finset.univ.erase (0 : F),
                quadraticChar F ((1 - u * y) * (1 - y)) : ℤ) : ℂ) =
                ((-quadraticChar F u - 1 : ℤ) : ℂ) := by exact_mod_cast hsum_int
            simpa [Int.cast_sum] using hsum_C
      _ = (Fintype.card F : ℂ) := by
          have h1mem : (1 : F) ∈ Finset.univ.erase (0 : F) :=
            Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
          have hsplit : ∀ u ∈ Finset.univ.erase (0 : F),
              ψ u * (if u = 1 then ((Fintype.card F : ℂ) - 2) else -(quadraticChar F u : ℂ) - 1) =
                (if u = 1 then (Fintype.card F : ℂ) else 0) -
                  ψ u * (quadraticChar F u : ℂ) - ψ u := fun u _ => by
            by_cases hu1 : u = 1
            · subst hu1; simp only [↓reduceIte, hψ_one, map_one, Int.cast_one]; ring
            · simp only [hu1, ↓reduceIte]; ring
          rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            hψ_orth1, hψ_orth2, sub_zero, sub_zero, Finset.sum_ite_eq']
          simp [h1mem]
  have hnormC : ((‖jacobiSum ψ‖ ^ 2 : ℝ) : ℂ) = (Fintype.card F : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hmul]
  exact_mod_cast hnormC

/-- **Unconditional coset-averaged elliptic trace cancellation**:
for EVERY odd-characteristic finite field `F`, EVERY multiplicative subgroup `H ≤ Fˣ`, and
EVERY coset `aH` (`a ∈ Fˣ`),
`|∑ lam ∈ aH, L(lam)| ≤ |F|`.
For every subgroup of size `|H| > √|F| / 2`, this strictly beats the trivial Hasse bound
`2 |H| √|F|` — completely unconditionally and without Deligne! -/
theorem abs_sum_coset_legendreTrace_le (hF : ringChar F ≠ 2) (H : Subgroup Fˣ)
    [DecidablePred (· ∈ H)] (a : Fˣ) :
    |∑ u : H, legendreTrace ((a * u.1 : Fˣ) : F)| ≤ (Fintype.card F : ℤ) := by
  classical
  -- Use a cyclic generator `g` of `Fˣ` of order `N = q - 1`.
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set N := Fintype.card Fˣ with hNdef
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_eq : N = Fintype.card F - 1 := Fintype.card_units F
  have hord_g : orderOf g = N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  -- Subgroup `H` has size `m` dividing `N`, with index `d = N / m`.
  set m := Fintype.card H
  have hm_pos : 0 < m := Fintype.card_pos
  have hm_dvd : m ∣ N := by
    simpa only [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H
  set d := N / m
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hN_pos hm_dvd) hm_pos
  have hdm : d * m = N := Nat.div_mul_cancel hm_dvd
  -- Primitive `N`-th root of unity `ζ = exp(2πi / N)` and discrete log `dlog : Fˣ → Fin N`.
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hζ_pow_N : ζ ^ N = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by
      field_simp [hNne]]
    exact Complex.exp_two_pi_mul_I
  have hζ_prim : ∀ k : ℕ, 0 < k → k < N → ζ ^ k ≠ 1 := by
    intro k hk0 hkN h1
    dsimp [ζ] at h1
    rw [← Complex.exp_nat_mul] at h1
    set θ : ℝ := 2 * Real.pi * (k : ℝ) / (N : ℝ)
    have hθ_eq : (k : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = (θ : ℂ) * Complex.I := by
      dsimp [θ]; push_cast; ring
    rw [hθ_eq, Complex.exp_mul_I] at h1
    have hre := congrArg Complex.re h1
    have hcos1 : Real.cos θ = 1 := by
      simpa [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im] using hre
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hN_pos
    have hk0R : (0 : ℝ) < k := by exact_mod_cast hk0
    have hkNR : (k : ℝ) < N := by exact_mod_cast hkN
    have hθ_pos : 0 < θ := by
      dsimp [θ]; exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hk0R) hNposR
    have hθ_lt : θ < 2 * Real.pi := by
      dsimp [θ]
      rw [div_lt_iff₀ hNposR]
      nlinarith [Real.pi_pos]
    have hcos_lt : Real.cos θ < 1 := by
      rcases le_or_gt θ Real.pi with hle | hgt
      · calc Real.cos θ < Real.cos 0 :=
              Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) ⟨hθ_pos.le, hle⟩ hθ_pos
          _ = 1 := Real.cos_zero
      · rw [← Real.cos_two_pi_sub θ]
        calc Real.cos (2 * Real.pi - θ) < Real.cos 0 :=
              Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
                ⟨by linarith, by linarith⟩ (by linarith)
          _ = 1 := Real.cos_zero
    linarith
  -- Construct the `N` multiplicative characters `ψ k : F → ℂ` via `g`-discrete log.
  have hpow_surj : ∀ u : Fˣ, ∃ j : ℕ, j < N ∧ g ^ j = u := by
    intro u
    obtain ⟨z, hz⟩ := hg u
    have hmod : (z % (N : ℤ)).toNat < N := by
      have h1 : 0 ≤ z % (N : ℤ) := Int.emod_nonneg z (by omega)
      have h2 : z % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos z (by omega)
      omega
    refine ⟨(z % (N : ℤ)).toNat, hmod, ?_⟩
    have hz_eq : g ^ ((z % (N : ℤ)).toNat : ℤ) = g ^ z := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg z (by omega)), ← hord_g, zpow_mod_orderOf]
    simpa only [zpow_natCast] using hz_eq.trans hz
  let dlog : Fˣ → ℕ := fun u => Classical.choose (hpow_surj u)
  have hdlog_lt : ∀ u : Fˣ, dlog u < N := fun u => (Classical.choose_spec (hpow_surj u)).1
  have hdlog_pow : ∀ u : Fˣ, g ^ dlog u = u := fun u => (Classical.choose_spec (hpow_surj u)).2
  have hpow_inj : Set.InjOn (fun j : ℕ => g ^ j) (Set.Iio (orderOf g)) := pow_injOn_Iio_orderOf
  rw [hord_g] at hpow_inj
  have hdlog_add : ∀ u v : Fˣ, (dlog u + dlog v) % N = dlog (u * v) := by
    intro u v
    have h1 : g ^ (dlog u + dlog v) = g ^ dlog (u * v) := by
      rw [pow_add, hdlog_pow, hdlog_pow, hdlog_pow]
    have h2 : g ^ ((dlog u + dlog v) % N) = g ^ dlog (u * v) := by
      rw [← hord_g, pow_mod_orderOf, h1]
    exact hpow_inj (Nat.mod_lt _ hN_pos) (hdlog_lt _) h2
  have hdlog_one : dlog 1 = 0 :=
    hpow_inj (hdlog_lt 1) hN_pos (by dsimp only; rw [hdlog_pow, pow_zero])
  -- Define `ψ k : F → ℂ` for `k : ℕ`.
  let ψ (k : ℕ) (x : F) : ℂ :=
    if hx : x = 0 then 0 else ζ ^ (k * dlog (Units.mk0 x hx))
  have hζ_mod : ∀ n : ℕ, ζ ^ (n % N) = ζ ^ n := fun n => by
    conv_rhs => rw [← Nat.div_add_mod n N]
    rw [pow_add, pow_mul, hζ_pow_N, one_pow, one_mul]
  have hψ_mul : ∀ k (x y : F), x ≠ 0 → y ≠ 0 → ψ k (x * y) = ψ k x * ψ k y := by
    intro k x y hx hy
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, hx, hy, hxy, ↓reduceDIte]
    have hunits : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by
      ext; rfl
    rw [hunits, ← hdlog_add, ← pow_add, ← mul_add, ← hζ_mod (k * (_ % N)), ← hζ_mod (k * _)]
    congr 1
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have hψ_one : ∀ k, ψ k 1 = 1 := fun k => by
    simp only [ψ, one_ne_zero, ↓reduceDIte]
    have : Units.mk0 (1 : F) one_ne_zero = 1 := by ext; rfl
    rw [this, hdlog_one, mul_zero, pow_zero]
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp [ζ]
    rw [show 2 * (Real.pi : ℂ) * Complex.I / (N : ℂ) =
        ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hψ_conj : ∀ k (x : F), x ≠ 0 → starRingEnd ℂ (ψ k x) = ψ k x⁻¹ := by
    intro k x hx
    have hinv : x⁻¹ ≠ 0 := inv_ne_zero hx
    have hprod : ψ k x * ψ k x⁻¹ = 1 := by
      rw [← hψ_mul k x x⁻¹ hx hinv, mul_inv_cancel₀ hx, hψ_one]
    have hnorm : ‖ψ k x‖ = 1 := by
      simp only [ψ, hx, ↓reduceDIte, norm_pow, hζ_norm, one_pow]
    have hmc : ψ k x * starRingEnd ℂ (ψ k x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    have hne : ψ k x ≠ 0 := fun h => by rw [h, zero_mul] at hprod; exact zero_ne_one hprod
    exact mul_left_cancel₀ hne (hmc.trans hprod.symm)
  -- Characterize `u ∈ H ↔ d ∣ dlog u`.
  have hmem_H : ∀ u : Fˣ, u ∈ H ↔ d ∣ dlog u := by
    intro u
    have hgd : g ^ d ∈ H := by
      have hset_eq : (H : Set Fˣ) = {x : Fˣ | x ^ m = 1} := by
        have hsub : (Finset.univ.filter fun x : Fˣ => x ∈ H) ⊆
            (Finset.univ.filter fun x : Fˣ => x ^ m = 1) := by
          intro x hx
          rw [Finset.mem_filter] at hx ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have h1 : (⟨x, hx.2⟩ : H) ^ m = 1 := pow_card_eq_one
          exact congrArg Subtype.val h1
        have hcard_le : (Finset.univ.filter fun x : Fˣ => x ^ m = 1).card ≤ m := by
          have himg : (Finset.univ.filter fun x : Fˣ => x ^ m = 1) ⊆
              (Finset.range m).image (fun j => g ^ (d * j)) := by
            intro x hx
            rw [Finset.mem_filter] at hx
            have hpow1 : g ^ (dlog x * m) = 1 := by
              rw [pow_mul, hdlog_pow, hx.2]
            have hdvdN : N ∣ dlog x * m := by
              rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one hpow1
            have hdvd : d ∣ dlog x := by
              rw [← hdm] at hdvdN
              exact (Nat.mul_dvd_mul_iff_right hm_pos).mp hdvdN
            obtain ⟨j, hj⟩ := hdvd
            have hjlt : j < m := by
              have hlt := hdlog_lt x
              rw [hj, ← hdm] at hlt
              exact Nat.lt_of_mul_lt_mul_left hlt
            exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjlt, by rw [← hj, hdlog_pow]⟩
          calc (Finset.univ.filter fun x : Fˣ => x ^ m = 1).card
              ≤ ((Finset.range m).image (fun j => g ^ (d * j))).card := Finset.card_le_card himg
            _ ≤ (Finset.range m).card := Finset.card_image_le
            _ = m := Finset.card_range m
        have hcard_H : (Finset.univ.filter fun x : Fˣ => x ∈ H).card = m := by
          dsimp [m]; rw [← Fintype.card_subtype]
        have hfeq := Finset.eq_of_subset_of_card_le hsub (by omega)
        ext x
        have := Finset.ext_iff.mp hfeq x
        simpa [Finset.mem_filter] using this
      have hpow_m : (g ^ d) ^ m = 1 := by rw [← pow_mul, hdm, ← hord_g, pow_orderOf_eq_one]
      have : g ^ d ∈ (H : Set Fˣ) := by rw [hset_eq]; exact hpow_m
      exact this
    constructor
    · intro hu
      have h1 : (⟨u, hu⟩ : H) ^ m = 1 := pow_card_eq_one
      have h2 : u ^ m = 1 := congrArg Subtype.val h1
      have hpow1 : g ^ (dlog u * m) = 1 := by rw [pow_mul, hdlog_pow, h2]
      have hdvdN : N ∣ dlog u * m := by rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one hpow1
      rw [← hdm] at hdvdN
      exact (Nat.mul_dvd_mul_iff_right hm_pos).mp hdvdN
    · rintro ⟨j, hj⟩
      rw [← hdlog_pow u, hj, pow_mul]
      exact Subgroup.pow_mem H hgd j
  -- Helper: `χ(g) = -1` and `dlog g = 1`.
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have hcard3 : 3 ≤ Fintype.card F := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  have hchi_g : quadraticChar F (g : F) = -1 := by
    have hne1 : quadraticChar F (g : F) ≠ 1 := by
      intro h1
      have heul := quadraticChar_eq_pow_of_char_ne_two hF g.ne_zero
      rw [h1] at heul
      have hpow_eq : (g : F) ^ (Fintype.card F / 2) = 1 := by
        by_contra hne
        simp only [hne, ↓reduceIte] at heul
        norm_num at heul
      have hg_half : g ^ (Fintype.card F / 2) = 1 := by
        ext; simpa using hpow_eq
      have hdvd : N ∣ Fintype.card F / 2 := by
        rw [← hord_g]; exact orderOf_dvd_of_pow_eq_one hg_half
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    rcases quadraticChar_dichotomy g.ne_zero with h | h
    · exact absurd h hne1
    · exact h
  have hdlog_g : dlog (Units.mk0 (g : F) g.ne_zero) = 1 := by
    have hu : Units.mk0 (g : F) g.ne_zero = g := by ext; rfl
    rw [hu]
    exact hpow_inj (hdlog_lt g) (show (1 : ℕ) < N by omega) (by dsimp only; rw [hdlog_pow, pow_one])
  -- Every character `ψ (t * m)` (`t < d`) satisfies `‖jacobiSum (ψ (t * m))‖² ≤ q`!
  have hjac_le : ∀ t ∈ Finset.range d, ‖jacobiSum (ψ (t * m))‖ ^ 2 ≤ (Fintype.card F : ℝ) := by
    intro t ht
    have htlt : t < d := Finset.mem_range.mp ht
    have htm_lt : t * m < N := by
      rw [← hdm]; exact Nat.mul_lt_mul_of_pos_right htlt hm_pos
    have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
    by_cases ht0 : t = 0
    · subst ht0
      have hval : jacobiSum (ψ (0 * m)) = (-1 : ℂ) := by
        have h1 : ∀ x ∈ Finset.univ.erase (0 : F), ψ (0 * m) x = 1 := fun x hx => by
          simp only [ψ, (Finset.mem_erase.mp hx).1, ↓reduceDIte, zero_mul, pow_zero]
        have h2 : jacobiSum (ψ (0 * m)) = ((jacobiSum (fun _ : F => (1 : ℤ)) : ℤ) : ℂ) := by
          unfold jacobiSum
          push_cast
          exact Finset.sum_congr rfl fun x hx => by rw [h1 x hx, one_mul]
        rw [h2, jacobiSum_one hF]; simp
      rw [hval, norm_neg, norm_one]; linarith
    · have htm_pos : 0 < t * m := Nat.mul_pos (by omega) hm_pos
      by_cases hquad : 2 * (t * m) = N
      · have hζhalf : ζ ^ (t * m) = -1 := by
          have hsq : (ζ ^ (t * m)) ^ 2 = 1 := by
            rw [← pow_mul, show t * m * 2 = N by omega, hζ_pow_N]
          have hne1 : ζ ^ (t * m) ≠ 1 := hζ_prim (t * m) htm_pos htm_lt
          have hfac : (ζ ^ (t * m) - 1) * (ζ ^ (t * m) + 1) = 0 := by linear_combination hsq
          rcases mul_eq_zero.mp hfac with h | h
          · exact absurd (sub_eq_zero.mp h) hne1
          · exact eq_neg_of_add_eq_zero_left h
        have hψ_eq_chi : ∀ x ∈ Finset.univ.erase (0 : F),
            ψ (t * m) x = (quadraticChar F x : ℂ) := by
          intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          simp only [ψ, hx0, ↓reduceDIte, pow_mul, hζhalf]
          have hx_eq : x = ((g : F) ^ dlog (Units.mk0 x hx0)) := by
            have := congrArg Units.val (hdlog_pow (Units.mk0 x hx0))
            simpa using this.symm
          conv_rhs => rw [hx_eq, map_pow, hchi_g]
          push_cast; rfl
        have hval : jacobiSum (ψ (t * m)) = ((-quadraticChar F (-1 : F) : ℤ) : ℂ) := by
          rw [← jacobiSum_quad_eq hF]
          unfold jacobiSum
          push_cast
          exact Finset.sum_congr rfl fun x hx => by rw [hψ_eq_chi x hx]
        rw [hval]
        rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h | h <;>
          rw [h] <;> simp [norm_one] <;> linarith
      · have horth1 : ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u = 0 := by
          have hgne : ψ (t * m) (g : F) ≠ 1 := by
            simp only [ψ, g.ne_zero, ↓reduceDIte, hdlog_g, mul_one]
            exact hζ_prim (t * m) htm_pos htm_lt
          have hshift : ψ (t * m) (g : F) * ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u =
              ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u := by
            rw [Finset.mul_sum]
            refine Finset.sum_nbij' (fun u => (g : F) * u) (fun u => (g : F)⁻¹ * u) ?_ ?_ ?_ ?_ ?_
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero g.ne_zero hu.1, Finset.mem_univ _⟩
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero (inv_ne_zero g.ne_zero) hu.1, Finset.mem_univ _⟩
            · intro u _; exact inv_mul_cancel_left₀ g.ne_zero u
            · intro u _; exact mul_inv_cancel_left₀ g.ne_zero u
            · intro u hu; exact (hψ_mul (t * m) (g : F) u g.ne_zero (Finset.mem_erase.mp hu).1).symm
          have hfac : (ψ (t * m) (g : F) - 1) * ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u = 0 := by
            linear_combination hshift
          exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hgne)
        have horth2 : ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u * (quadraticChar F u : ℂ) = 0 := by
          have hgne : ψ (t * m) (g : F) * (quadraticChar F (g : F) : ℂ) ≠ 1 := by
            rw [hchi_g]
            simp only [ψ, g.ne_zero, ↓reduceDIte, hdlog_g, mul_one, Int.cast_neg, Int.cast_one,
              mul_neg_one]
            intro hneg1
            have hζsq : ζ ^ (2 * (t * m)) = 1 := by
              rw [mul_comm, pow_mul, show ζ ^ (t * m) = -1 by linear_combination -hneg1]; norm_num
            rcases lt_or_gt_of_ne hquad with hlt | hgt
            · exact hζ_prim (2 * (t * m)) (by omega) hlt hζsq
            · have hsub : 0 < 2 * (t * m) - N ∧ 2 * (t * m) - N < N := by omega
              have hsub1 : ζ ^ (2 * (t * m) - N) = 1 := by
                have h1 : ζ ^ (2 * (t * m) - N) * ζ ^ N = 1 := by
                  rw [← pow_add, Nat.sub_add_cancel (by omega), hζsq]
                rwa [hζ_pow_N, mul_one] at h1
              exact hζ_prim (2 * (t * m) - N) hsub.1 hsub.2 hsub1
          have hshift : (ψ (t * m) (g : F) * (quadraticChar F (g : F) : ℂ)) *
                ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u * (quadraticChar F u : ℂ) =
              ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u * (quadraticChar F u : ℂ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_nbij' (fun u => (g : F) * u) (fun u => (g : F)⁻¹ * u) ?_ ?_ ?_ ?_ ?_
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero g.ne_zero hu.1, Finset.mem_univ _⟩
            · intro u hu; rw [Finset.mem_erase] at hu ⊢; exact ⟨mul_ne_zero (inv_ne_zero g.ne_zero) hu.1, Finset.mem_univ _⟩
            · intro u _; exact inv_mul_cancel_left₀ g.ne_zero u
            · intro u _; exact mul_inv_cancel_left₀ g.ne_zero u
            · intro u hu
              rw [hψ_mul (t * m) (g : F) u g.ne_zero (Finset.mem_erase.mp hu).1, map_mul]
              push_cast; ring
          have hfac : (ψ (t * m) (g : F) * (quadraticChar F (g : F) : ℂ) - 1) *
              ∑ u ∈ Finset.univ.erase (0 : F), ψ (t * m) u * (quadraticChar F u : ℂ) = 0 := by
            linear_combination hshift
          exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hgne)
        exact le_of_eq (jacobiSum_norm_sq_eq_card hF (ψ (t * m))
          (hψ_mul (t * m)) (hψ_one (t * m)) (hψ_conj (t * m)) horth1 horth2)
  -- Fourier indicator of the coset `aH` on `Fˣ`:
  have hcoset_ind : ∀ x : Fˣ,
      ∑ t ∈ Finset.range d, ψ (t * m) (a : F)⁻¹ * ψ (t * m) (x : F) =
        if x * a⁻¹ ∈ H then (d : ℂ) else 0 := by
    intro x
    set u := x * a⁻¹
    have hterm : ∀ t : ℕ, ψ (t * m) (a : F)⁻¹ * ψ (t * m) (x : F) = (ζ ^ (m * dlog u)) ^ t := fun t => by
      have ha0 : (a : F)⁻¹ ≠ 0 := inv_ne_zero a.ne_zero
      rw [← hψ_mul (t * m) (a : F)⁻¹ (x : F) ha0 x.ne_zero]
      have hu_eq : Units.mk0 ((a : F)⁻¹ * (x : F)) (mul_ne_zero ha0 x.ne_zero) = u := by
        ext; simp [u, mul_comm]
      simp only [ψ, mul_ne_zero ha0 x.ne_zero, ↓reduceDIte, hu_eq]
      rw [← pow_mul]; congr 1; ring
    simp_rw [hterm]
    by_cases huH : u ∈ H
    · simp only [huH, ↓reduceIte]
      obtain ⟨j, hj⟩ := (hmem_H u).mp huH
      have h1 : ζ ^ (m * dlog u) = 1 := by
        rw [hj, show m * (d * j) = N * j by rw [← hdm]; ring, pow_mul, hζ_pow_N, one_pow]
      simp only [h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · simp only [huH, ↓reduceIte]
      have hne1 : ζ ^ (m * dlog u) ≠ 1 := by
        intro h1
        have hrem : (m * dlog u) % N = 0 := by
          by_contra hnz
          have hlt : (m * dlog u) % N < N := Nat.mod_lt _ hN_pos
          have hpos : 0 < (m * dlog u) % N := Nat.pos_of_ne_zero hnz
          exact hζ_prim _ hpos hlt (by rw [hζ_mod, h1])
        have hdvdN : N ∣ m * dlog u := Nat.dvd_of_mod_eq_zero hrem
        rw [← hdm] at hdvdN
        have hdvd : d ∣ dlog u := (Nat.mul_dvd_mul_iff_left hm_pos).mp (by rwa [mul_comm m d])
        exact huH ((hmem_H u).mpr hdvd)
      have hgeom := geom_sum_mul (ζ ^ (m * dlog u)) d
      have hpow_d : (ζ ^ (m * dlog u)) ^ d = 1 := by
        rw [← pow_mul, show m * dlog u * d = N * dlog u by rw [← hdm]; ring,
          pow_mul, hζ_pow_N, one_pow]
      rw [hpow_d, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne1)
  -- Multiply by `L(lam)` and sum over `lam ∈ Fˣ` vs `t < d`!
  have hfourier : (d : ℂ) * ((∑ u : H, legendreTrace ((a * u.1 : Fˣ) : F) : ℤ) : ℂ) =
      ∑ t ∈ Finset.range d,
        ψ (t * m) (a : F)⁻¹ * ((quadraticChar F (-1 : F) : ℂ) * (jacobiSum (ψ (t * m))) ^ 2) := by
    have hmell : ∀ t : ℕ,
        (quadraticChar F (-1 : F) : ℂ) * (jacobiSum (ψ (t * m))) ^ 2 =
          ∑ lam ∈ Finset.univ.erase (0 : F), ψ (t * m) lam * (legendreTrace lam : ℂ) := fun t =>
      (mellin_jacobi_identity (ψ (t * m)) (hψ_mul (t * m))).symm
    have hrhs : ∑ t ∈ Finset.range d,
          ψ (t * m) (a : F)⁻¹ * ((quadraticChar F (-1 : F) : ℂ) * (jacobiSum (ψ (t * m))) ^ 2) =
        ∑ lam ∈ Finset.univ.erase (0 : F),
          (∑ t ∈ Finset.range d, ψ (t * m) (a : F)⁻¹ * ψ (t * m) lam) * (legendreTrace lam : ℂ) := by
      simp_rw [hmell, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun t _ => by ring
    rw [hrhs]
    have hunits_sum : ∑ lam ∈ Finset.univ.erase (0 : F),
          (∑ t ∈ Finset.range d, ψ (t * m) (a : F)⁻¹ * ψ (t * m) lam) * (legendreTrace lam : ℂ) =
        ∑ x : Fˣ, (∑ t ∈ Finset.range d, ψ (t * m) (a : F)⁻¹ * ψ (t * m) (x : F)) *
          (legendreTrace (x : F) : ℂ) := by
      refine (Finset.sum_nbij' (fun x : Fˣ => (x : F))
        (fun lam => if h : lam = 0 then 1 else Units.mk0 lam h) ?_ ?_ ?_ ?_ ?_).symm
      · intro x _; exact Finset.mem_erase.mpr ⟨x.ne_zero, Finset.mem_univ _⟩
      · intro _ _; exact Finset.mem_univ _
      · intro x _; simp [x.ne_zero]
      · intro lam hlam; simp [(Finset.mem_erase.mp hlam).1]
      · intro _ _; rfl
    rw [hunits_sum]
    simp_rw [hcoset_ind]
    have hite : ∀ x : Fˣ,
        (if x * a⁻¹ ∈ H then (d : ℂ) else 0) * (legendreTrace (x : F) : ℂ) =
          if x * a⁻¹ ∈ H then (d : ℂ) * (legendreTrace (x : F) : ℂ) else 0 := fun x => by
      split_ifs <;> ring
    simp_rw [hite, ← Finset.sum_filter, ← Finset.mul_sum]
    have hbij : ∑ x ∈ Finset.univ.filter (fun x : Fˣ => x * a⁻¹ ∈ H), (legendreTrace (x : F) : ℂ) =
        ∑ u : H, (legendreTrace ((a * u.1 : Fˣ) : F) : ℂ) := by
      refine (Finset.sum_nbij' (fun u : H => a * u.1)
        (fun x => if h : x * a⁻¹ ∈ H then ⟨x * a⁻¹, h⟩ else 1) ?_ ?_ ?_ ?_ ?_).symm
      · intro u _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [mul_comm a u.1, mul_assoc, mul_inv_cancel, mul_one]
        exact u.2
      · intro _ _; exact Finset.mem_univ _
      · intro u _
        have hmem : a * u.1 * a⁻¹ ∈ H := by
          rw [mul_comm a u.1, mul_assoc, mul_inv_cancel, mul_one]; exact u.2
        simp only [hmem, ↓reduceDIte]
        ext
        simp [mul_comm a u.1, mul_assoc]
      · intro x hx
        have hmem : x * a⁻¹ ∈ H := (Finset.mem_filter.mp hx).2
        simp only [hmem, ↓reduceDIte]
        rw [mul_comm a (x * a⁻¹), mul_assoc, inv_mul_cancel, mul_one]
      · intro _ _; rfl
    rw [hbij]
    simp [Int.cast_sum]
  -- Norm bound:
  have hnorm_d : ‖(d : ℂ) * ((∑ u : H, legendreTrace ((a * u.1 : Fˣ) : F) : ℤ) : ℂ)‖ ≤
      (d : ℝ) * (Fintype.card F : ℝ) := by
    rw [hfourier]
    calc ‖∑ t ∈ Finset.range d,
            ψ (t * m) (a : F)⁻¹ * ((quadraticChar F (-1 : F) : ℂ) * (jacobiSum (ψ (t * m))) ^ 2)‖
        ≤ ∑ t ∈ Finset.range d,
            ‖ψ (t * m) (a : F)⁻¹ * ((quadraticChar F (-1 : F) : ℂ) * (jacobiSum (ψ (t * m))) ^ 2)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _t ∈ Finset.range d, (Fintype.card F : ℝ) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [norm_mul, norm_mul, norm_pow]
          have hψ1 : ‖ψ (t * m) (a : F)⁻¹‖ = 1 := by
            simp only [ψ, inv_ne_zero a.ne_zero, ↓reduceDIte, norm_pow, hζ_norm, one_pow]
          have hchi1 : ‖(quadraticChar F (-1 : F) : ℂ)‖ = 1 := by
            rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h | h <;>
              rw [h] <;> simp
          rw [hψ1, hchi1, one_mul, one_mul]
          exact hjac_le t ht
      _ = (d : ℝ) * (Fintype.card F : ℝ) := by simp
  rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast] at hnorm_d
  have hd_posR : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have habsR : |(∑ u : H, legendreTrace ((a * u.1 : Fˣ) : F) : ℝ)| ≤ (Fintype.card F : ℝ) := by
    have := le_of_mul_le_mul_left hnorm_d hd_posR
    simpa [Int.cast_abs] using this
  exact_mod_cast habsR

end ProximityGap.PaleyMellinJacobi

#print axioms ProximityGap.PaleyMellinJacobi.mellin_jacobi_identity
#print axioms ProximityGap.PaleyMellinJacobi.legendreTrace_zero
#print axioms ProximityGap.PaleyMellinJacobi.legendreTrace_one
#print axioms ProximityGap.PaleyMellinJacobi.sum_legendreTrace_eq_zero
#print axioms ProximityGap.PaleyMellinJacobi.sum_legendreTrace_qr
#print axioms ProximityGap.PaleyMellinJacobi.sum_legendreTrace_nqr
#print axioms ProximityGap.PaleyMellinJacobi.sum_sq_legendreTrace
#print axioms ProximityGap.PaleyMellinJacobi.sum_sq_legendreTrace_punctured
#print axioms ProximityGap.PaleyMellinJacobi.jacobiSum_norm_sq_eq_card
#print axioms ProximityGap.PaleyMellinJacobi.abs_sum_coset_legendreTrace_le
