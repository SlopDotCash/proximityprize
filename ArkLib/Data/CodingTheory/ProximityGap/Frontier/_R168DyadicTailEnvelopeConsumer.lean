/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R168 dyadic tail-envelope consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf

/-!
# R168 (#466): a concrete consumer for the dyadic tail-envelope route

R66/R67 identified the most promising replacement for the false moment-ratio
monotonicity route: prove an exponential order-statistic bound for the dyadic
Gauss-period coset spectrum.  The empirical target is

```text
  N(T) ≤ M exp(-T/4).
```

The existing S11 lane already carries the analytic bridge
`MGFBound ⟹ MomentEnvelope ⟹ prize`.  This file pins a concrete, conservative
MGF residual for the dyadic route:

```text
  (1 / |s|) * Σ exp((1/8) * t_b) ≤ 2.
```

Why these constants: a continuous tail with rate `1/4` implies an exponential
moment at rate `1/8` with constant `≈ 2`.  This file does not prove that
survival-to-MGF step for the actual dyadic periods; it makes the exact
Lean-facing target and downstream constants explicit.

The additional theorem `dyadicTailMGF_of_survival_count_ceiling` specializes
S11's discrete layer-cake/count-ceiling bridge to these constants: a finite
threshold staircase whose count-weighted sum is at most `2 |s|` lands the R168
MGF residual.

Status: concentration consumer only.  Residual = prove the dyadic MGF bound.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

open ArkLib.ProximityGap.Frontier.WFS1
open ArkLib.ProximityGap.Frontier.WFS11

/-- **Concrete dyadic tail-route residual.**  For a normalized dyadic period
spectrum `t`, the conservative R66/R67 target is the empirical MGF bound at
rate `1/8` with constant `2`. -/
def DyadicTailMGFBound {ι : Type*} (s : Finset ι) (t : ι → ℝ) : Prop :=
  MGFBound s t 2 (1 / 8)

/-- **Closed-form grid tail residual from R170.**  On a finite threshold grid
`Θ`, the R170 target says every grid survival count is bounded by the
closed-form envelope `(3/4) |s| exp(-θ/4)`.  The intended grid is
`Θ = {0.5, 1.0, 1.5, ...}` or its `T ≥ 1` tail together with a separate
base term. -/
def DyadicClosedFormGridTail {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (Θ : Finset ℝ) : Prop :=
  ∀ θ ∈ Θ,
    ((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤
      (3 / 4 : ℝ) * (s.card : ℝ) * Real.exp (-(θ / 4))

/-- **Finite-grid count certificate for the R168 residual.**  If a threshold
staircase dominates the exponential weights `exp((1/8) t_b)`, every survival
count at the grid thresholds is bounded by an explicit ceiling `B`, and the
weighted ceiling sum is at most `2 |s|`, then the concrete dyadic MGF residual
holds.  This is the Lean-facing form of the R66/R67 tail-envelope proof target. -/
theorem dyadicTailMGF_of_survival_count_ceiling {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ B : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 8 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hcount : ∀ θ ∈ Θ, ((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s t := by
  exact mgfBound_of_survival_count_ceiling s t Θ δ B hδ hstair hcount hweighted

/-- **Closed-form grid tail consumer.**  If the R170 closed-form tail bound
holds on the staircase grid and the closed-form weighted envelope itself has
total mass at most `2 |s|`, then the concrete R168 MGF residual follows.

This separates the remaining proof into two pieces:
1. a dyadic survival-count theorem (`DyadicClosedFormGridTail`);
2. a pure numerical weighted-sum inequality for the chosen grid. -/
theorem dyadicTailMGF_of_closedFormGridTail {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp ((1 / 8 : ℝ) * t b) ≤
      ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hTail : DyadicClosedFormGridTail s t Θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * ((3 / 4 : ℝ) * (s.card : ℝ) * Real.exp (-(θ / 4))))
        ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s t := by
  refine dyadicTailMGF_of_survival_count_ceiling s t Θ δ
    (fun θ => (3 / 4 : ℝ) * (s.card : ℝ) * Real.exp (-(θ / 4))) hδ hstair ?_ hweighted
  intro θ hθ
  exact hTail θ hθ

/-- **Bin-budget compensation consumer.**  A bin certificate is enough to land
the R168 MGF residual: assign every spectrum point `b ∈ s` to a bin, give each
bin an exponential ceiling `E k` for `exp((1/8) t_b)`, and prove that the
resulting pointwise bin-budget sum is at most `2 |s|`.

This is the Lean-facing version of the R176 compensation strategy: extra
high-tail bins are allowed if the low bins are large enough that the total
exponential budget stays below `2`. -/
theorem dyadicTailMGF_of_bin_budget {ι κ : Type*}
    (s : Finset ι) (t : ι → ℝ) (binOf : ι → κ) (E : κ → ℝ)
    (hceil : ∀ b ∈ s, Real.exp ((1 / 8 : ℝ) * t b) ≤ E (binOf b))
    (hbudget : (∑ b ∈ s, E (binOf b)) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s t := by
  unfold DyadicTailMGFBound MGFBound
  exact (Finset.sum_le_sum hceil).trans hbudget

/-- **Tower-step product-budget consumer.**  Abstract form of the R181
dyadic-tower inequality.  If each parent normalized magnitude `parent i` is at
most the sum of two child normalized magnitudes `left i + right i`, and the
paired child product budget

`Σ_i exp(left_i/8) * exp(right_i/8) ≤ 2 |s|`

holds, then the parent spectrum satisfies the concrete R168 MGF residual.

In the intended application, `parent_i = |a_i+b_i|²/σ²_parent`, while
`left_i,right_i` are the two child squared magnitudes normalized by
`σ²_child`; the inequality comes from `|a+b|² ≤ 2(|a|²+|b|²)` plus
`σ²_parent = 2σ²_child`. -/
theorem dyadicTailMGF_of_tower_product_budget {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hbudget :
      (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i)) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  unfold DyadicTailMGFBound MGFBound
  calc
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * parent i))
        ≤ ∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * (left i + right i)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hparent i hi) (by norm_num))
    _ = ∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_add, Real.exp_add]
    _ ≤ 2 * (s.card : ℝ) := hbudget

/-- **AM-GM reduction for the tower product budget.**  The paired product
budget in `dyadicTailMGF_of_tower_product_budget` follows from two one-sided
higher-rate MGF bounds at rate `1/4`, each with constant `2`.  Pointwise,
`uv ≤ (u^2+v^2)/2`, with
`u = exp(left/8)` and `v = exp(right/8)`. -/
theorem dyadicTailMGF_of_tower_amgm_mgf {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hLeft : (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ))
    (hRight : (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i)) ≤ 2 * (s.card : ℝ)) :
    DyadicTailMGFBound s parent := by
  have hprod :
      (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i)) ≤ 2 * (s.card : ℝ) := by
    have hpoint : ∀ i ∈ s,
        Real.exp ((1 / 8 : ℝ) * left i) * Real.exp ((1 / 8 : ℝ) * right i)
          ≤ (Real.exp ((1 / 4 : ℝ) * left i) +
              Real.exp ((1 / 4 : ℝ) * right i)) / 2 := by
      intro i _
      set u := Real.exp ((1 / 8 : ℝ) * left i)
      set v := Real.exp ((1 / 8 : ℝ) * right i)
      have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
      have hamgm : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith
      have hu : u ^ 2 = Real.exp ((1 / 4 : ℝ) * left i) := by
        subst u
        rw [pow_two]
        rw [← Real.exp_add]
        ring_nf
      have hv : v ^ 2 = Real.exp ((1 / 4 : ℝ) * right i) := by
        subst v
        rw [pow_two]
        rw [← Real.exp_add]
        ring_nf
      simpa [hu, hv] using hamgm
    calc
      (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
          Real.exp ((1 / 8 : ℝ) * right i))
          ≤ ∑ i ∈ s, (Real.exp ((1 / 4 : ℝ) * left i) +
              Real.exp ((1 / 4 : ℝ) * right i)) / 2 := Finset.sum_le_sum hpoint
      _ = ((∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) +
            (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * right i))) / 2 := by
          simp [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          rw [Finset.sum_add_distrib]
      _ ≤ (2 * (s.card : ℝ) + 2 * (s.card : ℝ)) / 2 := by
          exact div_le_div_of_nonneg_right (add_le_add hLeft hRight) (by norm_num)
      _ = 2 * (s.card : ℝ) := by ring
  exact dyadicTailMGF_of_tower_product_budget s parent left right hparent hprod

/-- The R168 residual directly implies the S11 moment envelope with constants
`A = 2`, `c = 1/8`. -/
theorem momentEnvelope_of_dyadicTailMGF {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hTail : DyadicTailMGFBound s t) :
    MomentEnvelope (fun r => (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)) 2 (1 / 8) := by
  exact momentEnvelope_of_mgf s t (by norm_num) ht hP hTail

/-- The R168 residual gives a concrete S1 slack constant `16`. -/
theorem slack_of_dyadicTailMGF {ι : Type*} (s : Finset ι) (t : ι → ℝ) {n : ℝ}
    (hn : 0 ≤ n) (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hTail : DyadicTailMGFBound s t) :
    CharPEnergyTransferWithSlack
      (fun r => n ^ r * ((∑ b ∈ s, (t b) ^ r) / (s.card : ℝ))) n 16 := by
  have h := slack_of_mgf_general (A := 2) (n := n) (c := (1 / 8 : ℝ))
    s t (by norm_num) hn (by norm_num) ht hP hTail
  norm_num at h
  exact h

/-- Concrete prize-square consumer for the dyadic tail route.  If the normalized
dyadic period spectrum satisfies the R168 MGF residual, then the S11 prize
bound lands with constant multiplier `32 * exp 1` in the squared form. -/
theorem prize_sq_of_dyadicTailMGF {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hTail : DyadicTailMGFBound s t)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  have h := prize_sq_of_mgf_general (A := 2) (c := (1 / 8 : ℝ))
    s t hMmax (by norm_num) hn hQ (by norm_num) ht hP hr hrQ hTail hmoment
  exact h

end ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.momentEnvelope_of_dyadicTailMGF
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.dyadicTailMGF_of_survival_count_ceiling
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.dyadicTailMGF_of_closedFormGridTail
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.dyadicTailMGF_of_bin_budget
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.dyadicTailMGF_of_tower_product_budget
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.dyadicTailMGF_of_tower_amgm_mgf
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.slack_of_dyadicTailMGF
#print axioms ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.prize_sq_of_dyadicTailMGF
