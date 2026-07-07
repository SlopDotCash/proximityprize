/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S11 MGF rate monotonicity)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

set_option linter.style.longLine false

/-!
# S11 MGF rate monotonicity — lower-rate concentration is automatic

Issue lalalune/ArkLib#444 (Ethereum Proximity Prize, the char-`p` concentration wall).

The S11 layer-cake brick reduced the moment/slack/prize chain to the one-variable residual
`MGFBound s t A c`, namely

  `Σ_{b∈s} exp (c · t_b) ≤ A · |s|`.

For the true normalized spectrum `t_b = |η_b|²/n` we have `t_b ≥ 0`. Therefore an exponential-moment
bound at a rate `c` immediately implies the same bound at any lower positive rate `c' ≤ c`:
`exp(c' t_b) ≤ exp(c t_b)` pointwise. This file records that tiny but load-bearing rate-transfer
lemma and composes it with the existing `momentEnvelope_of_mgf` / `prize_sq_of_mgf` consumers.

Honest scope: this does **not** prove the MGF residual. It only removes a nuisance from the S11 route:
once a uniform MGF/survival estimate is available at some working rate, all lower rates are free, with
constant degraded only by the explicit `1/c'` in the prize chain. No CORE closure, no capacity claim.
-/

open Finset
open Real
open ArkLib.ProximityGap.Frontier.WFS1
open ArkLib.ProximityGap.Frontier.WFS11

namespace ArkLib.ProximityGap.Frontier.WFS11

/-- **MGF rate monotonicity.** For a nonnegative spectrum, an MGF bound at rate `c` implies the same
bound at every lower rate `c' ≤ c`. This is the discrete exponential-tail rate-transfer step: the
residual may be checked at one rate and consumed at any smaller positive rate. -/
theorem MGFBound.of_rate_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c c' : ℝ}
    (ht : ∀ b ∈ s, 0 ≤ t b) (hcc' : c' ≤ c) (hMGF : MGFBound s t A c) :
    MGFBound s t A c' := by
  unfold MGFBound at hMGF ⊢
  refine le_trans ?_ hMGF
  apply Finset.sum_le_sum
  intro b hb
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcc' (ht b hb))

/-- **Lower-rate moment envelope from a higher-rate MGF.** If `MGFBound` is known at rate `c`, then
for every `0 < c' ≤ c` the S11 layer-cake moment envelope holds at the lower rate `c'`. -/
theorem momentEnvelope_of_mgf_rate_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c c' : ℝ}
    (hc' : 0 < c') (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hcc' : c' ≤ c) (hMGF : MGFBound s t A c) :
    MomentEnvelope (fun r => (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)) A c' := by
  exact momentEnvelope_of_mgf s t hc' ht hP (MGFBound.of_rate_le s t ht hcc' hMGF)

/-- **Higher-rate MGF ⟹ lower-rate prize chain.** A one-variable MGF bound at rate `c` can be
consumed by the S11 prize theorem at any lower positive rate `c' ≤ min(c,1)`, yielding the explicit
constant `sqrt(2e/c')`. This is just rate monotonicity composed with `prize_sq_of_mgf`. -/
theorem prize_sq_of_mgf_rate_le_general {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {Mmax A n Q c c' : ℝ} {r : ℕ}
    (hMmax : 0 ≤ Mmax) (hA : 1 ≤ A) (hn : 0 ≤ n) (hQ : 0 < Q) (hc' : 0 < c')
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hcc' : c' ≤ c) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hMGF : MGFBound s t A c)
    (hmoment : Mmax ^ (2 * r) ≤ Q * (n ^ r * ((∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (A / c') * n * (r : ℝ) := by
  exact prize_sq_of_mgf_general s t hMmax hA hn hQ hc' ht hP hr hrQ
    (MGFBound.of_rate_le s t ht hcc' hMGF) hmoment

theorem prize_sq_of_mgf_rate_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) {Mmax n Q c c' : ℝ} {r : ℕ}
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q) (hc' : 0 < c') (_hc'1 : c' ≤ 1)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hcc' : c' ≤ c) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hMGF : MGFBound s t 1 c)
    (hmoment : Mmax ^ (2 * r) ≤ Q * (n ^ r * ((∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (1 / c') * n * (r : ℝ) := by
  simpa using prize_sq_of_mgf_rate_le_general (A := 1) s t hMmax (by norm_num) hn hQ hc'
    ht hP hcc' hr hrQ hMGF hmoment

#print axioms MGFBound.of_rate_le
#print axioms momentEnvelope_of_mgf_rate_le
#print axioms prize_sq_of_mgf_rate_le_general
#print axioms prize_sq_of_mgf_rate_le

end ArkLib.ProximityGap.Frontier.WFS11
