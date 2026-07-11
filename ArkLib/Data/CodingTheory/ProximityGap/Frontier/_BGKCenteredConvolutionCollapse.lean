/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R348PeriodSquareRecursion

/-!
# Centered convolution collapse for the repaired BGK depth-seven gate

The repaired depth-seven target is the DC-subtracted quantity

`q * E₇(H) - |H|¹⁴`,

not the raw energy.  This file gives it two exact physical-space normal forms.

First, if `f_r(d)` counts ordered `r`-tuples from `H` with sum `d`, then

`sum_d (q f_r(d) - |H|^r)^2 = q * (q E_r(H) - |H|^(2r))`.

Thus the corrected moment is precisely the variance of the `r`-fold convolution about its
uniform density, with all divisions cleared.

Second, write `C_r(delta) = sum_d f_r(d) f_r(d+delta)`.  The one-step recursion centers exactly:

`q E_(r+1) - |H|^(2r+2)
   = sum_(s,t in H) (q C_r(s-t) - |H|^(2r))`.

When `H` is a finite multiplicative subgroup, `f_r` and hence `C_r` are invariant under dilation
by `H`.  Reindexing `t = s*u` therefore collapses the two-dimensional average to

`|H| * sum_(u in H) (q C_r(1-u) - |H|^(2r))`.

At `r = 6` this is an exact new face of the depth-seven residual: the needed cancellation is a
signed average along the single translate `1-H`.  Positive packet-count envelopes discard this
sign and cannot see the collapse.  No bound on the signed average is claimed here.

Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset

namespace ArkLib.ProximityGap.Frontier.BGKCenteredConvolutionCollapse

open ArkLib.ProximityGap.CharPMomentRecursion
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.R348PeriodSquareRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The denominator-cleared deviation of the `r`-fold representation count from uniformity. -/
noncomputable def centeredFreq (H : Finset F) (r : ℕ) (d : F) : ℝ :=
  (Fintype.card F : ℝ) * (freq H r d : ℝ) - (H.card : ℝ) ^ r

/-- The squared `L²` mass of the denominator-cleared convolution deviation. -/
noncomputable def centeredFreqEnergy (H : Finset F) (r : ℕ) : ℝ :=
  ∑ d : F, centeredFreq H r d ^ 2

/-- The denominator-cleared centered autocorrelation at lag `delta`. -/
noncomputable def centeredAutocorr (H : Finset F) (r : ℕ) (delta : F) : ℝ :=
  (Fintype.card F : ℝ) * (autocorr H r delta : ℝ) - (H.card : ℝ) ^ (2 * r)

/-- **Exact convolution-variance identity.**  The DC-subtracted moment is exactly the squared
`L²` deviation of the `r`-fold representation function from uniformity. -/
theorem centeredFreqEnergy_eq_dcMoment (H : Finset F) (r : ℕ) :
    centeredFreqEnergy H r =
      (Fintype.card F : ℝ) *
        ((Fintype.card F : ℝ) * (rEnergy H r : ℝ) - (H.card : ℝ) ^ (2 * r)) := by
  let q : ℝ := Fintype.card F
  let N : ℝ := (H.card : ℝ) ^ r
  have hfreq : (∑ d : F, (freq H r d : ℝ)) = N := by
    dsimp only [N]
    exact_mod_cast sum_freq H r
  have henergy : (∑ d : F, (freq H r d : ℝ) ^ 2) = (rEnergy H r : ℝ) := by
    exact_mod_cast (rEnergy_eq_sum_freq_sq H r).symm
  have hones : (∑ _d : F, (1 : ℝ)) = q := by simp [q]
  have hexp : N ^ 2 = (H.card : ℝ) ^ (2 * r) := by
    dsimp only [N]
    rw [pow_two, ← pow_add, two_mul]
  unfold centeredFreqEnergy centeredFreq
  change (∑ d : F, (q * (freq H r d : ℝ) - N) ^ 2) = _
  calc
    (∑ d : F, (q * (freq H r d : ℝ) - N) ^ 2) =
        q ^ 2 * (∑ d : F, (freq H r d : ℝ) ^ 2) -
          2 * q * N * (∑ d : F, (freq H r d : ℝ)) +
            (∑ _d : F, (1 : ℝ)) * N ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      ring
    _ = q * (q * (rEnergy H r : ℝ) - (H.card : ℝ) ^ (2 * r)) := by
      rw [hfreq, henergy, hones, hexp]
      ring

/-- The full autocorrelation mass is the square of the total `r`-fold representation mass. -/
theorem sum_autocorr_eq_totalMass_sq (H : Finset F) (r : ℕ) :
    ∑ delta : F, autocorr H r delta = H.card ^ (2 * r) := by
  unfold autocorr
  rw [Finset.sum_comm]
  calc
    (∑ e : F, ∑ delta : F, freq H r e * freq H r (e + delta)) =
        ∑ e : F, freq H r e * ∑ delta : F, freq H r (e + delta) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Finset.mul_sum]
    _ = ∑ e : F, freq H r e * H.card ^ r := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      congr 1
      calc
        (∑ delta : F, freq H r (e + delta)) = ∑ d : F, freq H r d := by
          exact Fintype.sum_equiv (Equiv.addLeft e)
            (fun delta => freq H r (e + delta)) (fun d => freq H r d) (fun _ => rfl)
        _ = H.card ^ r := sum_freq H r
    _ = (∑ e : F, freq H r e) * H.card ^ r := by rw [Finset.sum_mul]
    _ = H.card ^ (2 * r) := by
      rw [sum_freq, ← pow_add, two_mul]

/-- **Zero-global-mean law.**  The centered autocorrelation is a signed discrepancy function:
its sum over the whole additive field is exactly zero. -/
theorem sum_centeredAutocorr_eq_zero (H : Finset F) (r : ℕ) :
    ∑ delta : F, centeredAutocorr H r delta = 0 := by
  have hsum : (∑ delta : F, (autocorr H r delta : ℝ)) =
      (H.card : ℝ) ^ (2 * r) := by
    exact_mod_cast sum_autocorr_eq_totalMass_sq H r
  unfold centeredAutocorr
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  simp

/-- **Centered one-step recursion.**  The DC-subtracted `(r+1)`-energy is the sum of the signed
centered depth-`r` autocorrelations over the difference multiset `H-H`. -/
theorem dcMoment_succ_eq_sum_centeredAutocorr (H : Finset F) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy H (r + 1) : ℝ) -
        (H.card : ℝ) ^ (2 * (r + 1)) =
      ∑ s ∈ H, ∑ t ∈ H, centeredAutocorr H r (s - t) := by
  let q : ℝ := Fintype.card F
  let n : ℝ := H.card
  have hrec : (rEnergy H (r + 1) : ℝ) =
      ∑ s ∈ H, ∑ t ∈ H, (autocorr H r (s - t) : ℝ) := by
    exact_mod_cast rEnergy_succ_double_sum H r
  have hcard : ((H.card : ℝ) ^ 2) =
      ∑ _s ∈ H, ∑ _t ∈ H, (1 : ℝ) := by simp [pow_two]
  have hexp : n ^ (2 * (r + 1)) = n ^ 2 * n ^ (2 * r) := by
    rw [show 2 * (r + 1) = 2 + 2 * r by omega, pow_add]
  unfold centeredAutocorr
  change q * (rEnergy H (r + 1) : ℝ) - n ^ (2 * (r + 1)) = _
  rw [hrec, hexp, hcard]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_mul]
  simp [q, n, mul_comm]

/-- Left multiplication by a subgroup element preserves the `r`-fold representation count. -/
theorem freq_mul_left (H : Finset F) (hH : IsMulSubgroup H)
    {u : F} (hu : u ∈ H) (r : ℕ) (d : F) :
    freq H r (u * d) = freq H r d := by
  classical
  obtain ⟨ui, hui, huui⟩ := hH.exists_inv u hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_mul] at huui
    exact zero_ne_one huui
  symm
  unfold freq
  refine Finset.sum_bij'
    (fun v _ => fun i => u * v i)
    (fun v _ => fun i => ui * v i) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [Fintype.mem_piFinset] at hv ⊢
    intro i
    exact hH.mul_mem u hu (v i) (hv i)
  · intro v hv
    rw [Fintype.mem_piFinset] at hv ⊢
    intro i
    exact hH.mul_mem ui hui (v i) (hv i)
  · intro v hv
    funext i
    change ui * (u * v i) = v i
    rw [← mul_assoc, mul_comm ui u, huui, one_mul]
  · intro v hv
    funext i
    change u * (ui * v i) = v i
    rw [← mul_assoc, huui, one_mul]
  · intro v hv
    have hsum : (∑ i, u * v i) = u * ∑ i, v i := by rw [Finset.mul_sum]
    rw [hsum]
    by_cases h : ∑ i, v i = d
    · rw [if_pos h, if_pos (congrArg (u * ·) h)]
    · rw [if_neg h, if_neg]
      intro heq
      exact h (mul_left_cancel₀ hu0 heq)

/-- The representation-count autocorrelation is invariant under simultaneous dilation of its
lag by a multiplicative subgroup element. -/
theorem autocorr_mul_left (H : Finset F) (hH : IsMulSubgroup H)
    {u : F} (hu : u ∈ H) (r : ℕ) (delta : F) :
    autocorr H r (u * delta) = autocorr H r delta := by
  classical
  obtain ⟨ui, hui, huui⟩ := hH.exists_inv u hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_mul] at huui
    exact zero_ne_one huui
  unfold autocorr
  have hre :
      (∑ e : F, freq H r e * freq H r (e + u * delta)) =
        ∑ e : F, freq H r (u * e) * freq H r (u * e + u * delta) := by
    exact (Fintype.sum_equiv (Equiv.mulLeft₀ u hu0)
      (fun e => freq H r (u * e) * freq H r (u * e + u * delta))
      (fun e => freq H r e * freq H r (e + u * delta))
      (fun e => rfl)).symm
  rw [hre]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [freq_mul_left H hH hu r e]
  have hadd : u * e + u * delta = u * (e + delta) := by ring
  rw [hadd, freq_mul_left H hH hu r (e + delta)]

/-- The centered autocorrelation inherits multiplicative dilation invariance. -/
theorem centeredAutocorr_mul_left (H : Finset F) (hH : IsMulSubgroup H)
    {u : F} (hu : u ∈ H) (r : ℕ) (delta : F) :
    centeredAutocorr H r (u * delta) = centeredAutocorr H r delta := by
  unfold centeredAutocorr
  rw [autocorr_mul_left H hH hu r delta]

/-- Abstract multiplicative compression: a dilation-invariant function on differences needs only
be sampled on the single translate `1-H`. -/
theorem sum_differences_collapse (H : Finset F) (hH : IsMulSubgroup H)
    (D : F → ℝ) (hD : ∀ u ∈ H, ∀ x, D (u * x) = D x) :
    (∑ s ∈ H, ∑ t ∈ H, D (s - t)) =
      (H.card : ℝ) * ∑ u ∈ H, D (1 - u) := by
  calc
    (∑ s ∈ H, ∑ t ∈ H, D (s - t)) =
        ∑ s ∈ H, ∑ u ∈ H, D (s - s * u) := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      exact (sum_reindex_mulLeft hH hs (fun t => D (s - t))).symm
    _ = ∑ _s ∈ H, ∑ u ∈ H, D (1 - u) := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      refine Finset.sum_congr rfl (fun u hu => ?_)
      have hfactor : s - s * u = s * (1 - u) := by ring
      rw [hfactor, hD s hs]
    _ = (H.card : ℝ) * ∑ u ∈ H, D (1 - u) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- **Multiplicative centered collapse.**  The two-dimensional difference average in the centered
moment recursion is exactly a one-dimensional signed average along `1-H`. -/
theorem dcMoment_succ_eq_card_mul_translateAverage
    (H : Finset F) (hH : IsMulSubgroup H) (r : ℕ) :
    (Fintype.card F : ℝ) * (rEnergy H (r + 1) : ℝ) -
        (H.card : ℝ) ^ (2 * (r + 1)) =
      (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H r (1 - u) := by
  rw [dcMoment_succ_eq_sum_centeredAutocorr]
  exact sum_differences_collapse H hH (centeredAutocorr H r)
    (fun u hu delta => centeredAutocorr_mul_left H hH hu r delta)

/-- Depth-seven specialization: the repaired numerator is a depth-six signed translate average. -/
theorem dcMoment_seven_eq_card_mul_depthSixTranslateAverage
    (H : Finset F) (hH : IsMulSubgroup H) :
    (Fintype.card F : ℝ) * (rEnergy H 7 : ℝ) - (H.card : ℝ) ^ 14 =
      (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) := by
  simpa using dcMoment_succ_eq_card_mul_translateAverage H hH 6

/-- **Fourier-side audit of the collapse.**  With a primitive additive character, the collapsed
translate sum is exactly the nonzero fourteenth moment.  This shows that the one-dimensional form
preserves all DC-subtracted moment content; it is a structural rerouting, not a moment-method
bypass. -/
theorem card_mul_depthSixTranslateAverage_eq_nonzero_fourteenthMoment
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive)
    (H : Finset F) (hH : IsMulSubgroup H) :
    (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) =
      ∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi H b‖ ^ 14 := by
  calc
    (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) =
        (Fintype.card F : ℝ) * (rEnergy H 7 : ℝ) - (H.card : ℝ) ^ 14 :=
      (dcMoment_seven_eq_card_mul_depthSixTranslateAverage H hH).symm
    _ = ∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi H b‖ ^ 14 := by
      simpa using (sum_nonzero_moment hpsi H 7).symm

/-- Although its individual terms are signed, the entire collapsed translate average is
nonnegative: after multiplication by `|H|` it is a sum of fourteenth powers. -/
theorem depthSixTranslateAverage_nonneg
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive)
    (H : Finset F) (hH : IsMulSubgroup H) :
    0 ≤ ∑ u ∈ H, centeredAutocorr H 6 (1 - u) := by
  have hprod :
      0 ≤ (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) := by
    rw [card_mul_depthSixTranslateAverage_eq_nonzero_fourteenthMoment hpsi H hH]
    exact Finset.sum_nonneg (fun b _ => by positivity)
  have hcardPos : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hH.one_mem⟩
  exact (mul_nonneg_iff_of_pos_left hcardPos).mp hprod

/-- The one-dimensional form of the repaired coefficient-`2^18` BGK residual.  Keeping the
factor `|H|` clears the normalization in the exact collapse theorem. -/
def DepthSixTranslateAverageResidual (H : Finset F) : Prop :=
  (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) ≤
    (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (H.card : ℝ) ^ 7)

/-- **Exact residual equivalence.**  For a multiplicative subgroup, coefficient-`2^18`
depth-seven off-zero flatness is neither stronger nor weaker than the signed translate-average
bound: the two propositions differ only by the centered convolution identity. -/
theorem depthSevenOffZeroFlatness_iff_depthSixTranslateAverage
    (H : Finset F) (hH : IsMulSubgroup H) :
    ((Fintype.card F : ℝ) * (rEnergy H 7 : ℝ) - (H.card : ℝ) ^ 14 ≤
        (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (H.card : ℝ) ^ 7)) ↔
      DepthSixTranslateAverageResidual H := by
  unfold DepthSixTranslateAverageResidual
  rw [dcMoment_seven_eq_card_mul_depthSixTranslateAverage H hH]

/-- At the production parameters, the normalized one-dimensional target has the explicit budget
`2^357`.  This is the coefficient scale a per-prime estimate along `1-H` must meet. -/
theorem production_depthSixTranslateAverage_le
    {H : Finset F} (hcard : H.card = 2 ^ 30)
    (hqu : Fintype.card F ≤ 2 ^ 159)
    (hres : DepthSixTranslateAverageResidual H) :
    ∑ u ∈ H, centeredAutocorr H 6 (1 - u) ≤ (2 : ℝ) ^ 357 := by
  have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by
    exact_mod_cast hqu
  have htotal :
      (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) ≤
        (2 : ℝ) ^ 387 := by
    calc
      (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) ≤
          (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (H.card : ℝ) ^ 7) := hres
      _ ≤ (2 : ℝ) ^ 159 * ((2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7) := by
        rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
        exact mul_le_mul_of_nonneg_right hqR (by positivity)
      _ = (2 : ℝ) ^ 387 := by norm_num [← pow_mul, ← pow_add]
  have hscaled :
      (2 : ℝ) ^ 30 * (∑ u ∈ H, centeredAutocorr H 6 (1 - u)) ≤
        (2 : ℝ) ^ 30 * (2 : ℝ) ^ 357 := by
    calc
      (2 : ℝ) ^ 30 * (∑ u ∈ H, centeredAutocorr H 6 (1 - u)) =
          (H.card : ℝ) * ∑ u ∈ H, centeredAutocorr H 6 (1 - u) := by
            rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ 387 := htotal
      _ = (2 : ℝ) ^ 30 * (2 : ℝ) ^ 357 := by norm_num [← pow_add]
  exact le_of_mul_le_mul_left hscaled (by positivity)

#print axioms centeredFreqEnergy_eq_dcMoment
#print axioms sum_autocorr_eq_totalMass_sq
#print axioms sum_centeredAutocorr_eq_zero
#print axioms dcMoment_succ_eq_sum_centeredAutocorr
#print axioms freq_mul_left
#print axioms autocorr_mul_left
#print axioms sum_differences_collapse
#print axioms dcMoment_succ_eq_card_mul_translateAverage
#print axioms dcMoment_seven_eq_card_mul_depthSixTranslateAverage
#print axioms card_mul_depthSixTranslateAverage_eq_nonzero_fourteenthMoment
#print axioms depthSixTranslateAverage_nonneg
#print axioms depthSevenOffZeroFlatness_iff_depthSixTranslateAverage
#print axioms production_depthSixTranslateAverage_le

end ArkLib.ProximityGap.Frontier.BGKCenteredConvolutionCollapse
