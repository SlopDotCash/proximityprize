import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Abelian-cover test functions for a lower bound on the largest period

These lemmas verify the fiber norm comparison, the constant-mode correction and
the arithmetic of the radius-five test function in the 2026-11-21 disproof log.
The weighted Cayley spectral identity is proved for every cyclic modulus.
The realization of the counted lattice layers at the production subgroup is in the paper proof.
-/

namespace ProximityGap.Frontier.AbelianCoverPeriodFloor

open Finset

variable {I Y : Type*} [Fintype I] [Fintype Y] [DecidableEq Y]

/-- The Euclidean norm of the values above a single vertex. -/
noncomputable def fiberNorm (label : I → Y) (f : I → ℝ) (y : Y) : ℝ :=
  Real.sqrt (∑ i : I with label i = y, (f i) ^ 2)

theorem fiberNorm_sq_sum (label : I → Y) (f : I → ℝ) :
    ∑ y, (fiberNorm label f y) ^ 2 = ∑ i, (f i) ^ 2 := by
  unfold fiberNorm
  simp_rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_fiberwise _ _ _

theorem fiberNorm_sum_le (label : I → Y) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ y, fiberNorm label f y ≤ ∑ i, f i := by
  rw [← Finset.sum_fiberwise univ label f]
  apply Finset.sum_le_sum
  intro y _
  apply Real.sqrt_le_iff.mpr
  exact ⟨Finset.sum_nonneg (fun i _ => hf i), sum_sq_le_sq_sum_of_nonneg (fun i _ => hf i)⟩

/-- Lifting a directed step does not increase its adjacency quadratic form under
the fiberwise Euclidean norm. Summing this inequality allows multiple steps. -/
theorem step_correlation_le (label : I → Y) (f : I → ℝ) (e : I ≃ I) (s : Y ≃ Y)
    (hs : ∀ i, label (e i) = s (label i)) :
    ∑ i, f i * f (e i) ≤ ∑ y, fiberNorm label f y * fiberNorm label f (s y) := by
  classical
  rw [← Finset.sum_fiberwise univ label (fun i => f i * f (e i))]
  apply Finset.sum_le_sum
  intro y _
  have htransport : (∑ i : I with label i = y, f (e i) ^ 2) =
      ∑ i : I with label i = s y, f i ^ 2 := by
    refine sum_bij' (fun i _ => e i) (fun j _ => e.symm j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      rw [hs, hi]
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      apply s.injective
      rw [← hs, e.apply_symm_apply, hj]
    · simp
    · simp
    · simp
  simpa only [fiberNorm, htransport] using
    Real.sum_mul_le_sqrt_mul_sqrt (univ.filter fun i => label i = y) f (fun i => f (e i))

/-- Clearing denominators in the mean-zero Rayleigh argument. Here z is the
constant part's squared norm, p its ambient cardinality, and t a proposed ceiling. -/
theorem constant_mode_obstruction {p n D E L z t : ℝ} (hp : 0 < p)
    (ht : t ≤ n) (hz : p * z ≤ L ^ 2)
    (hcert : t * (p * D - L ^ 2) < p * E - n * L ^ 2) :
    t * (D - z) < E - n * z := by
  have hz' := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hz)
  apply (mul_lt_mul_iff_right₀ hp).mp
  nlinarith

private def degree : ℕ := 2 ^ 30
private def modulus : ℕ := 365375409332725729550921208179070755120141565953

private def layerSize (k : ℕ) : ℕ :=
  2 ^ k * ((degree / 2).descFactorial k / k.factorial)

theorem layerSize_eq_choose (k : ℕ) :
    layerSize k = 2 ^ k * (degree / 2).choose k := by
  exact congrArg (fun c => 2 ^ k * c) (Nat.choose_eq_descFactorial_div_factorial _ _).symm

private def weight (k : ℕ) : ℕ :=
  [100, 319, 917, 2287, 4541, 5335][k]! * 32768 ^ (5-k)

private def layerNorm : ℕ := ((List.range 6).map fun k => layerSize k * weight k ^ 2).sum
private def layerMass : ℕ := ((List.range 6).map fun k => layerSize k * weight k).sum
private def layerEnergy : ℕ :=
  2 * ((List.range 5).map fun k =>
    layerSize k * (degree - 2 * k) * weight k * weight (k+1)).sum

/-- Exact arithmetic for the first prize prime, expressed with natural
addition so that the numerator cannot be affected by truncated subtraction. -/
theorem production_certificate :
    layerMass ^ 2 < modulus * layerNorm ∧
      104498 * (modulus * layerNorm) + degree * layerMass ^ 2 <
      modulus * layerEnergy + 104498 * layerMass ^ 2 := by
  decide +kernel

/-- A pointwise bound on the mass carried by each frequency turns an excess of
the weighted first moment into a lower bound on the number above a threshold. -/
theorem frequency_count_budget {B : Type*} [Fintype B] [DecidableEq B]
    (period mass : B → ℝ) (t n cap : ℝ) (ht : t ≤ n)
    (hperiod : ∀ b, period b ≤ n) (hpos : ∀ b, 0 ≤ mass b)
    (hcap : ∀ b, mass b ≤ cap) :
    ∑ b, period b * mass b ≤ t * (∑ b, mass b) +
        ((univ.filter fun b => t < period b).card : ℝ) * ((n - t) * cap) := by
  classical
  have hpoint (b : B) :
      period b * mass b ≤ t * mass b + if t < period b then (n - t) * cap else 0 := by
    split_ifs with hb
    · have h₁ := mul_le_mul_of_nonneg_right (hperiod b) (hpos b)
      have h₂ := mul_le_mul_of_nonneg_left (hcap b) (sub_nonneg.mpr ht)
      linarith
    · simpa using mul_le_mul_of_nonneg_right (not_lt.mp hb) (hpos b)
  calc
    _ ≤ ∑ b, (t * mass b + if t < period b then (n - t) * cap else 0) :=
      sum_le_sum fun b _ => hpoint b
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_ite, sum_const, sum_const_zero,
      add_zero, nsmul_eq_mul]

private def countWeight (k : ℕ) : ℕ := [32768^3, 2*32768^2, 3*32768, 2][k]!
private def countNorm : ℕ := ((List.range 4).map fun k => layerSize k * countWeight k ^ 2).sum
private def countMass : ℕ := ((List.range 4).map fun k => layerSize k * countWeight k).sum
private def countEnergy : ℕ := 2 * ((List.range 3).map fun k =>
  layerSize k * (degree - 2*k) * countWeight k * countWeight (k+1)).sum

/-- Excludes at most 125802243 nonzero cosets above t=65536, even after adding
the principal frequency to their count. -/
theorem coset_count_certificate :
    modulus * (65536 * countNorm) +
      (1 + 125802243 * degree) * ((degree - 65536) * countMass ^ 2) <
    modulus * countEnergy := by
  decide +kernel

#print axioms fiberNorm_sq_sum
#print axioms fiberNorm_sum_le
#print axioms step_correlation_le
#print axioms constant_mode_obstruction
#print axioms layerSize_eq_choose
#print axioms production_certificate
#print axioms frequency_count_budget
#print axioms coset_count_certificate

open Complex
open scoped ZMod ComplexConjugate

variable {p : ℕ} [NeZero p]

/-- Squared modulus of the unnormalized Fourier coefficient. -/
noncomputable def fourierMass (F : ZMod p → ℝ) (b : ZMod p) : ℝ :=
  Complex.normSq (ZMod.dft (fun x => (F x : ℂ)) b)

theorem shifted_wiener_identity (F : ZMod p → ℝ) (s : ZMod p) :
    (p : ℂ) * (∑ x, (F x : ℂ) * (F (x+s) : ℂ)) =
    ∑ b, ZMod.stdAddChar (s*b) * (fourierMass F b : ℂ) := by
  let Fc : ZMod p → ℂ := fun x => F x
  let A := ZMod.dft Fc
  have hconj (b : ZMod p) :
      ∑ x, (F x : ℂ) * ZMod.stdAddChar (x*b) = conj (A b) := by
    unfold A
    rw [ZMod.dft_apply, map_sum]
    apply sum_congr rfl
    intro x _
    simp only [Fc, smul_eq_mul, map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, neg_neg,
      mul_comm]
  have hinv (u : ZMod p) :
      (p : ℂ) * (F u : ℂ) = ∑ b, ZMod.stdAddChar (b*u) * A b := by
    have hx := congrFun (ZMod.dft.symm_apply_apply Fc) u
    rw [ZMod.invDFT_apply] at hx
    change (p : ℂ)⁻¹ * (∑ b, ZMod.stdAddChar (b*u) * A b) = (F u : ℂ) at hx
    rw [← hx, ← mul_assoc, mul_inv_cancel₀ (NeZero.ne (p : ℂ)), one_mul]
  calc
    _ = ∑ x, (F x : ℂ) * ((p : ℂ) * (F (x+s) : ℂ)) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ = ∑ x, ∑ b, ZMod.stdAddChar (s*b) * A b * ((F x : ℂ) * ZMod.stdAddChar (x*b)) := by
      simp_rw [hinv, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro b _
      rw [mul_comm b (x+s), add_mul, AddChar.map_add_eq_mul]
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [← mul_sum, hconj, mul_assoc, Complex.mul_conj]
      rfl


theorem shifted_wiener_real (F : ZMod p → ℝ) (s : ZMod p) :
    (p : ℝ) * (∑ x, F x * F (x+s)) =
    ∑ b, (ZMod.stdAddChar (s*b)).re * fourierMass F b := by
  have h := congrArg Complex.re (shifted_wiener_identity F s)
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.re_sum,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using h

theorem mass_parseval (F : ZMod p → ℝ) :
    (p : ℝ) * (∑ x, (F x)^2) = ∑ b, fourierMass F b := by
  simpa [pow_two] using shifted_wiener_real F 0

theorem cayley_weighted_moment (F : ZMod p → ℝ) (H : Finset (ZMod p)) :
    (p : ℝ) * (∑ s ∈ H, ∑ x, F x * F (x+s)) =
      ∑ b, (∑ s ∈ H, (ZMod.stdAddChar (s*b)).re) * fourierMass F b := by
  rw [mul_sum]
  simp_rw [shifted_wiener_real]
  rw [sum_comm]
  simp_rw [sum_mul]

theorem mass_le_sq_sum (F : ZMod p → ℝ) (hF : ∀ x, 0 ≤ F x) (b : ZMod p) :
    fourierMass F b ≤ (∑ x, F x) ^ 2 := by
  rw [fourierMass, Complex.normSq_eq_norm_sq]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [ZMod.dft_apply]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro x _
  simp [smul_eq_mul, AddChar.norm_apply, Real.norm_eq_abs, abs_of_nonneg (hF x)]

#print axioms shifted_wiener_identity
#print axioms shifted_wiener_real
#print axioms mass_parseval
#print axioms cayley_weighted_moment
#print axioms mass_le_sq_sum

end ProximityGap.Frontier.AbelianCoverPeriodFloor
