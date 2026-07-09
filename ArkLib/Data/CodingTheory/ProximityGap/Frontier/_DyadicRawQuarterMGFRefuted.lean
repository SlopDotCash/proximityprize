/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Raw quarter-MGF normalization refutation and exact Haar defect

The numerically tested dyadic statistic is the dimensionless squared score

```text
  X_i = t_i² / n,
  Σ_i exp(X_i / 4) ≤ 2 |s|.
```

Several concrete R207--R210 Gauss-period consumers instead insert the raw
modulus `t_i = ‖η_i‖` into `exp(t_i/4)`.  This file proves an abstract
Parseval-scale refutation of that raw residual.  The only application-specific
input is the already-landed identity

```text
  Σ_{b≠0} ‖η_G(b)‖² = q|G| - |G|².
```

If `|G| ≥ 128` and `2|G| ≤ q`, the raw exponential sum is forced above
`2(q-1)`.  Thus the raw residual is false at prize scale; the corrected
squared-and-normalized residual remains open.

The file also records the exact normalized Haar defect.  For a dyadic pair
`a,b`, the Cauchy step discards precisely `(a-b)²/(2n)`.  When the children
align (`a=b`) this defect is zero and the parent eighth-MGF weight equals the
child quarter-MGF weight exactly.  Consequently a Haar/martingale rewrite by
itself gives no strict contraction on the coherent spikes.
-/

open Finset Real

namespace ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted

/-- The raw-modulus residual accidentally used by the concrete R207--R210
Gauss-period bridge. -/
def RawQuarterMGFBound {ι : Type*} (s : Finset ι) (t : ι → ℝ) : Prop :=
  (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * t i)) ≤ 2 * (s.card : ℝ)

/-- The corrected, dimensionless residual tested by the dyadic probes. -/
def NormalizedSquaredQuarterMGFBound {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) (n : ℝ) : Prop :=
  (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * (t i ^ 2 / n))) ≤
    2 * (s.card : ℝ)

/-- The second Taylor term already lower-bounds a raw quarter exponential. -/
theorem sq_div_32_le_exp_quarter {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 32 ≤ Real.exp ((1 / 4 : ℝ) * x) := by
  have h := Real.pow_div_factorial_le_exp (x := x / 4) (by positivity) 2
  norm_num at h ⊢
  convert h using 1 <;> ring

/-- A raw quarter exponential sum dominates one thirty-second of the second
moment. -/
theorem raw_quarter_sum_secondMoment_lower {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (∑ i ∈ s, t i ^ 2) / 32 ≤
      ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * t i) := by
  calc
    (∑ i ∈ s, t i ^ 2) / 32
        = ∑ i ∈ s, t i ^ 2 / 32 := by
          simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * t i) := by
      exact Finset.sum_le_sum fun i hi => sq_div_32_le_exp_quarter (ht i hi)

/-- Any family whose second moment exceeds `64 |s|` refutes the raw quarter
MGF budget. -/
theorem not_rawQuarterMGFBound_of_secondMoment {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i)
    (hsecond : 64 * (s.card : ℝ) < ∑ i ∈ s, t i ^ 2) :
    ¬ RawQuarterMGFBound s t := by
  intro hraw
  have hlower := raw_quarter_sum_secondMoment_lower s t ht
  unfold RawQuarterMGFBound at hraw
  linarith

/-- **Parseval-scale refutation.**  If a nonnegative family has `q-1`
entries and exact second moment `qn-n²`, then the large-thin conditions
`128 ≤ n` and `2n ≤ q` make the raw quarter-MGF budget impossible. -/
theorem not_rawQuarterMGFBound_of_parseval_scale {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) (q n : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i)
    (hq : 0 < q) (hn : 128 ≤ n) (hthin : 2 * n ≤ q)
    (hcard : (s.card : ℝ) = q - 1)
    (hsecond : ∑ i ∈ s, t i ^ 2 = q * n - n ^ 2) :
    ¬ RawQuarterMGFBound s t := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hgap : q / 2 ≤ q - n := by linarith
  have hscale : 64 * q ≤ q * n - n ^ 2 := by
    calc
      64 * q = 128 * (q / 2) := by ring
      _ ≤ n * (q / 2) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ ≤ n * (q - n) := mul_le_mul_of_nonneg_left hgap hn0
      _ = q * n - n ^ 2 := by ring
  apply not_rawQuarterMGFBound_of_secondMoment s t ht
  rw [hcard, hsecond]
  linarith

/-- Exact normalized Haar/parallelogram identity.  The loss in the Cauchy
parent bound is exactly the normalized square of the Haar difference. -/
theorem normalized_haar_defect (a b n : ℝ) (hn : n ≠ 0) :
    (a + b) ^ 2 / (2 * n) =
      a ^ 2 / n + b ^ 2 / n - (a - b) ^ 2 / (2 * n) := by
  field_simp [hn]
  ring

/-- Correct pointwise tower translation for the dimensionless scores.  The
parent eighth-MGF weight is bounded by the arithmetic mean of the two child
quarter-MGF weights. -/
theorem normalized_parent_eighth_le_child_quarter_average
    (a b n : ℝ) (hn : 0 < n) :
    Real.exp ((1 / 8 : ℝ) * ((a + b) ^ 2 / (2 * n))) ≤
      (Real.exp ((1 / 4 : ℝ) * (a ^ 2 / n)) +
        Real.exp ((1 / 4 : ℝ) * (b ^ 2 / n))) / 2 := by
  have hparent : (a + b) ^ 2 / (2 * n) ≤ a ^ 2 / n + b ^ 2 / n := by
    rw [normalized_haar_defect a b n hn.ne']
    have hdefect : 0 ≤ (a - b) ^ 2 / (2 * n) := by positivity
    linarith
  have hexp :
      Real.exp ((1 / 8 : ℝ) * ((a + b) ^ 2 / (2 * n))) ≤
        Real.exp ((1 / 8 : ℝ) * (a ^ 2 / n + b ^ 2 / n)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hparent (by norm_num))
  let u := Real.exp ((1 / 8 : ℝ) * (a ^ 2 / n))
  let v := Real.exp ((1 / 8 : ℝ) * (b ^ 2 / n))
  have hamgm : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by
    nlinarith [sq_nonneg (u - v)]
  have hu : u ^ 2 = Real.exp ((1 / 4 : ℝ) * (a ^ 2 / n)) := by
    simp only [u, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hv : v ^ 2 = Real.exp ((1 / 4 : ℝ) * (b ^ 2 / n)) := by
    simp only [v, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp ((1 / 8 : ℝ) * ((a + b) ^ 2 / (2 * n)))
        ≤ Real.exp ((1 / 8 : ℝ) * (a ^ 2 / n + b ^ 2 / n)) := hexp
    _ = u * v := by
      simp only [u, v, mul_add, Real.exp_add]
    _ ≤ (u ^ 2 + v ^ 2) / 2 := hamgm
    _ = (Real.exp ((1 / 4 : ℝ) * (a ^ 2 / n)) +
          Real.exp ((1 / 4 : ℝ) * (b ^ 2 / n))) / 2 := by rw [hu, hv]

/-- At a coherent spike (`a=b`), the parent eighth-MGF weight and child
quarter-MGF weight coincide.  Hence the Haar step has no strict contraction
without an additional theorem controlling aligned child pairs. -/
theorem aligned_haar_mgf_no_gain (a n : ℝ) (hn : n ≠ 0) :
    Real.exp ((1 / 8 : ℝ) * ((a + a) ^ 2 / (2 * n))) =
      Real.exp ((1 / 4 : ℝ) * (a ^ 2 / n)) := by
  congr 1
  field_simp [hn]
  ring

end ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.sq_div_32_le_exp_quarter
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.raw_quarter_sum_secondMoment_lower
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.not_rawQuarterMGFBound_of_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.not_rawQuarterMGFBound_of_parseval_scale
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.normalized_haar_defect
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.normalized_parent_eighth_le_child_quarter_average
#print axioms ArkLib.ProximityGap.Frontier.DyadicRawQuarterMGFRefuted.aligned_haar_mgf_no_gain
