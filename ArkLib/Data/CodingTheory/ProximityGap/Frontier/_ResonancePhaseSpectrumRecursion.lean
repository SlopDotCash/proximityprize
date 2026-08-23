/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion

/-!
# Fourier-side recursion for the resonance phase-sum (#444)

This is the spectral form of `phaseSum_succ`.  For any multiplicative additive character
`ψ : ZMod m → ℂ`, the Fourier coefficient of the depth-`r` phase-sum satisfies

`phaseSpectrum ψ u (r+1) = kernelSpectrum ψ u * phaseSpectrum ψ u r`.

Iterating this identity reduces all higher spectral rungs to the one-step kernel spectrum.

Honest scope: this is an exact algebraic identity only. It does not bound the one-step spectrum;
that spectrum is the open door-(iv) Gauss-period/BGK object.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators
open Finset

variable {m : ℕ} [NeZero m]

/-- The `ψ`-Fourier coefficient of the depth-`r` phase-sum. -/
noncomputable def phaseSpectrum (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ) : ℂ :=
  ∑ c : ZMod m, phaseSum u r c * ψ c

/-- The one-step nonzero kernel spectrum attached to `u`. -/
noncomputable def kernelSpectrum (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) : ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0), u a * ψ a

/-- **Spectral one-step recursion.**  If `ψ` is multiplicative for addition, then the
Fourier coefficient of `P_{r+1}` is the one-step spectrum times the Fourier coefficient of
`P_r`. This is the Fourier-side form of the exact convolution recursion. -/
theorem phaseSpectrum_succ (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) :
    phaseSpectrum ψ u (r + 1) = kernelSpectrum ψ u * phaseSpectrum ψ u r := by
  classical
  unfold phaseSpectrum kernelSpectrum
  simp_rw [phaseSum_succ]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro a ha
  calc
    (∑ c : ZMod m, u a * phaseSum u r (c - a) * ψ c)
        = u a * (∑ c : ZMod m, phaseSum u r (c - a) * ψ c) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = u a * (∑ d : ZMod m, phaseSum u r d * ψ (d + a)) := by
          congr 1
          exact Fintype.sum_equiv (Equiv.subRight a) _ _ (by
            intro d
            simp [sub_eq_add_neg, add_assoc])
    _ = u a * (∑ d : ZMod m, phaseSum u r d * (ψ d * ψ a)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [hmul]
    _ = u a * ((∑ d : ZMod m, phaseSum u r d * ψ d) * ψ a) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro d _
          ring
    _ = u a * ψ a * ∑ d : ZMod m, phaseSum u r d * ψ d := by
          ring

/-- Depth zero has only the empty tuple, so its spectrum is `ψ 0`. -/
theorem phaseSpectrum_zero (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) :
    phaseSpectrum ψ u 0 = ψ 0 := by
  classical
  unfold phaseSpectrum phaseSum
  rw [Finset.sum_eq_single (0 : ZMod m)]
  · simp
  · intro c _ hc
    have h0c : ¬ (0 : ZMod m) = c := by
      simpa [eq_comm] using hc
    simp [h0c]
  · simp

/-- Iterating the spectral recursion: with `ψ 0 = 1`, every rung is a power of the
one-step kernel spectrum. -/
theorem phaseSpectrum_eq_kernelSpectrum_pow (ψ : ZMod m → ℂ) (u : ZMod m → ℂ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) (hzero : ψ 0 = 1) :
    ∀ r : ℕ, phaseSpectrum ψ u r = (kernelSpectrum ψ u) ^ r := by
  intro r
  induction r with
  | zero =>
      rw [phaseSpectrum_zero, hzero, pow_zero]
  | succ r ih =>
      rw [phaseSpectrum_succ ψ u r hmul, ih, pow_succ]
      ring

/-- If the one-step kernel spectrum vanishes at a frequency, then every positive depth
spectrum vanishes at the same frequency.  This is only an exact algebraic annihilation
criterion; it does not prove that any prize-relevant kernel spectrum vanishes. -/
theorem phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero (ψ : ZMod m → ℂ)
    (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y)
    (hk : kernelSpectrum ψ u = 0) :
    phaseSpectrum ψ u (r + 1) = 0 := by
  rw [phaseSpectrum_succ ψ u r hmul, hk, zero_mul]

/-- Contrapositive packaging of the annihilation criterion: any nonzero positive-depth
spectrum certifies a nonzero one-step kernel spectrum.  The open door-(iv) content is still
to bound this one-step kernel at the adversarial frequency, not merely to prove nonvanishing. -/
theorem kernelSpectrum_ne_zero_of_phaseSpectrum_succ_ne_zero (ψ : ZMod m → ℂ)
    (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y)
    (hspec : phaseSpectrum ψ u (r + 1) ≠ 0) :
    kernelSpectrum ψ u ≠ 0 := by
  intro hk
  exact hspec (phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero ψ u r hmul hk)

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_succ
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_zero
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_eq_kernelSpectrum_pow
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_succ_eq_zero_of_kernelSpectrum_eq_zero
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.kernelSpectrum_ne_zero_of_phaseSpectrum_succ_ne_zero
