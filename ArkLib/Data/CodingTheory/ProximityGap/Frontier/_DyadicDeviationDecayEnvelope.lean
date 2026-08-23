/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The dyadic deviation-decay envelope: why the floor needs `δᵢ = O(1/i)`, not a constant gap (#407)

## What this file adds over `_DyadicCocycleLargeDeviation.lean`

That file telescopes a **constant** geometric-mean budget `G` and bounds the top level by
`M N0 · G^L`.  Its prose suggests a measured geometric mean `≈ 1.50 = √2 · 1.06` recovers the
floor via "`1.06^L` supplying the polylog".  **That reading is quantitatively wrong**, and this
file makes the correction precise:

* a *constant* per-level excess over `√2` — i.e. `M(i+1)² ≥ (2+δ)·M(i)²` with `δ > 0` fixed —
  forces `M(2^μ)/√(2^μ) ≥ (1+δ/2)^{μ/2}`, which is a **power** `n^{c(δ)}`
  (`c(δ) = ½ log₂(1+δ/2) > 0`), NOT a polylog.  So a constant gap **misses** the floor
  `M(2^μ) ≍ √(2^μ · log(q/2^μ)) = √n · polylog`.  (`constant_excess_power_blowup`.)
* the floor is recovered **iff** the per-level deviation **decays** as `δᵢ = O(1/i)`.  Under the
  decaying hypothesis `DyadicDeviationDecay M C` (`M(i+1)² ≤ (2 + C/(i+1))·M(i)²`), the exact
  squared telescope plus `1+x ≤ eˣ` gives the explicit envelope
  `M(μ)² ≤ M(0)² · 2^μ · exp((C/2)·Hᵤ)`, `Hᵤ = Σ_{i<μ} 1/(i+1)` the harmonic sum.  Since
  `Hᵤ ≤ 1 + log μ`, the excess over `2^μ` is `exp(O(C log μ)) = μ^{O(C)}` — a genuine
  **polylog**, matching the floor.  (`sq_level_le_pow_mul_exp_harmonic`.)

So the single open analytic input is sharpened from "geometric mean `≤ √2·(1+o(1))`" to the
**quantitative decay rate** `δᵢ = O(1/i)`: the recursion constant must shrink like the reciprocal
level.  This is the exact form of the BGK / incomplete-character-sum sup-norm wall for the dyadic
subgroup `μ_{2^i}` — a recognized open problem — and `DyadicDeviationDecay` is the named,
never-instantiated hypothesis carrying it.  Everything else here is proven, no `sorry`/`axiom`.

`M i` is the intended envelope `max_{b≠0} |Σ_{x∈μ_{2^i}} e_p(b x)|`; we only use `0 ≤ M i` and the
recursion, so the results are about any nonnegative sequence obeying the dyadic descent.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- BGK: Bourgain–Glibichuk–Konyagin, character sums over subgroups (the open sup-norm wall).
-/

namespace ProximityGap.Frontier.DyadicDeviationDecay

open Finset

/--
**The decaying per-level deviation hypothesis (the named open core).**

`M(i+1)² ≤ (2 + C/(i+1)) · M(i)²` for every level `i`.  The `2` is the Parseval/random scale
(the disjoint-coset `L²` orthogonality of the FFT butterfly); the `C/(i+1)` is the worst-case
alignment excess, conjectured (and probed) to decay like the reciprocal level.  Proving this for
the dyadic Gaussian-period envelope is the BGK incomplete-character-sum sup-norm bound — open. -/
def DyadicDeviationDecay (M : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ i : ℕ, M (i + 1) ^ 2 ≤ (2 + C / (i + 1)) * M i ^ 2

/-- **Exact squared telescope.**  The decaying recursion (with nonnegative levels) telescopes the
squared top level into the product of per-level factors. -/
theorem sq_level_le_prod {M : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hM : ∀ i, 0 ≤ M i)
    (hdec : DyadicDeviationDecay M C) (μ : ℕ) :
    M μ ^ 2 ≤ M 0 ^ 2 * ∏ i ∈ range μ, (2 + C / (i + 1)) := by
  induction μ with
  | zero => simp
  | succ μ ih =>
      have hfac_nonneg : (0:ℝ) ≤ 2 + C / (μ + 1) := by
        have : (0:ℝ) ≤ C / (μ + 1) := div_nonneg hC (by positivity)
        linarith
      calc M (μ + 1) ^ 2 ≤ (2 + C / (μ + 1)) * M μ ^ 2 := hdec μ
        _ ≤ (2 + C / (μ + 1)) * (M 0 ^ 2 * ∏ i ∈ range μ, (2 + C / (i + 1))) :=
              mul_le_mul_of_nonneg_left ih hfac_nonneg
        _ = M 0 ^ 2 * ∏ i ∈ range (μ + 1), (2 + C / (i + 1)) := by
              rw [prod_range_succ]; ring

/-- Factor each per-level term as `2 · (1 + C/(2(i+1)))`, separating the random scale `2^μ`. -/
theorem prod_factor (C : ℝ) (μ : ℕ) :
    ∏ i ∈ range μ, (2 + C / (i + 1)) = 2 ^ μ * ∏ i ∈ range μ, (1 + C / (2 * (i + 1))) := by
  rw [show (2:ℝ) ^ μ = ∏ _i ∈ range μ, (2:ℝ) by rw [prod_const, card_range]]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  have : ((i:ℝ) + 1) ≠ 0 := by positivity
  field_simp

/--
**The explicit polylog envelope (headline).**  Under the decaying deviation, the squared envelope
is at most the random scale `2^μ` times `exp((C/2)·Hᵤ)`, where `Hᵤ = Σ_{i<μ} 1/(i+1)` is the
harmonic sum.  Because `Hᵤ ≤ 1 + log μ`, the excess factor is `μ^{O(C)}` — a **polylog**, so
`M(2^μ) ≤ M(0)·√(2^μ)·μ^{O(C)} = √n · polylog(n)`, exactly the floor shape. -/
theorem sq_level_le_pow_mul_exp_harmonic {M : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hM : ∀ i, 0 ≤ M i)
    (hdec : DyadicDeviationDecay M C) (μ : ℕ) :
    M μ ^ 2 ≤ M 0 ^ 2 * 2 ^ μ * Real.exp (C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1))) := by
  have htel := sq_level_le_prod hC hM hdec μ
  rw [prod_factor] at htel
  -- bound ∏ (1 + C/(2(i+1))) ≤ exp(Σ C/(2(i+1))) = exp((C/2) Σ 1/(i+1)) via 1+x ≤ eˣ
  have hprod_le : ∏ i ∈ range μ, (1 + C / (2 * ((i:ℝ) + 1)))
      ≤ Real.exp (C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1))) := by
    have hstep : ∀ i ∈ range μ, (1 + C / (2 * ((i:ℝ) + 1)))
        ≤ Real.exp (C / (2 * ((i:ℝ) + 1))) := by
      intro i _
      have h := Real.add_one_le_exp (C / (2 * ((i:ℝ) + 1)))
      linarith [h]
    have hpos : ∀ i ∈ range μ, (0:ℝ) ≤ 1 + C / (2 * ((i:ℝ) + 1)) := by
      intro i _; have : (0:ℝ) ≤ C / (2 * ((i:ℝ) + 1)) := div_nonneg hC (by positivity); linarith
    have hsum : ∑ i ∈ range μ, C / (2 * ((i:ℝ) + 1))
        = C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      show C / (2 * ((i:ℝ) + 1)) = C / 2 * (1 / ((i:ℝ) + 1))
      rw [mul_one_div, div_div]
    calc ∏ i ∈ range μ, (1 + C / (2 * ((i:ℝ) + 1)))
        ≤ ∏ i ∈ range μ, Real.exp (C / (2 * ((i:ℝ) + 1))) :=
          prod_le_prod hpos hstep
      _ = Real.exp (∑ i ∈ range μ, C / (2 * ((i:ℝ) + 1))) :=
          (Real.exp_sum (range μ) (fun i => C / (2 * ((i:ℝ) + 1)))).symm
      _ = Real.exp (C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1))) := by rw [hsum]
  have h2pos : (0:ℝ) ≤ M 0 ^ 2 * 2 ^ μ := by positivity
  calc M μ ^ 2 ≤ M 0 ^ 2 * (2 ^ μ * ∏ i ∈ range μ, (1 + C / (2 * ((i:ℝ) + 1)))) := htel
    _ = (M 0 ^ 2 * 2 ^ μ) * ∏ i ∈ range μ, (1 + C / (2 * ((i:ℝ) + 1))) := by ring
    _ ≤ (M 0 ^ 2 * 2 ^ μ) * Real.exp (C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hprod_le h2pos
    _ = M 0 ^ 2 * 2 ^ μ * Real.exp (C / 2 * ∑ i ∈ range μ, (1 / ((i:ℝ) + 1))) := by ring

/-!
## The corrective separation: a constant per-level excess gives a POWER, not a polylog

The point of `DyadicDeviationDecay` (with its `1/(i+1)` decay) is that the deviation must vanish
with the level.  Here we prove the contrapositive structural fact: if instead the per-level ratio
exceeds the random scale by a *constant* `δ > 0` at every level (a lower bound — i.e. the alignment
genuinely sustains), then the normalized envelope `M(μ)² / 2^μ` grows like `(1 + δ/2)^μ`, a
positive power of `n = 2^μ`, and so **exceeds every polylog** — the floor is missed.
-/

/-- **Constant-excess lower telescope.**  A sustained constant excess `δ` at every level forces an
exponential lower bound on the squared envelope. -/
theorem constant_excess_sq_ge {M : ℕ → ℝ} {δ : ℝ}
    (hexc : ∀ i, (2 + δ) * M i ^ 2 ≤ M (i + 1) ^ 2) (hδ : 0 ≤ δ) (μ : ℕ) :
    M 0 ^ 2 * (2 + δ) ^ μ ≤ M μ ^ 2 := by
  induction μ with
  | zero => simp
  | succ μ ih =>
      have hfac : (0:ℝ) ≤ 2 + δ := by linarith
      calc M 0 ^ 2 * (2 + δ) ^ (μ + 1)
          = (2 + δ) * (M 0 ^ 2 * (2 + δ) ^ μ) := by ring
        _ ≤ (2 + δ) * M μ ^ 2 := mul_le_mul_of_nonneg_left ih hfac
        _ ≤ M (μ + 1) ^ 2 := hexc μ

/--
**Constant excess ⟹ power-law blowup of the normalized envelope.**  With a sustained constant
excess `δ > 0` and a nonzero start, `M(μ)² / 2^μ ≥ M(0)² · (1 + δ/2)^μ`.  The right side is a
fixed base `> 1` raised to `μ`, i.e. a positive power of `n = 2^μ` — it dominates every polynomial
in `μ`, so no constant-gap law can produce the `√(n · polylog)` floor.  This is precisely why the
open input must be the *decaying* `DyadicDeviationDecay`, not a constant geometric-mean budget. -/
theorem constant_excess_power_blowup {M : ℕ → ℝ} {δ : ℝ}
    (hexc : ∀ i, (2 + δ) * M i ^ 2 ≤ M (i + 1) ^ 2) (hδ : 0 ≤ δ) (μ : ℕ) :
    M 0 ^ 2 * (1 + δ / 2) ^ μ ≤ M μ ^ 2 / 2 ^ μ := by
  have h := constant_excess_sq_ge hexc hδ μ
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ μ)]
  have hrw : M 0 ^ 2 * (1 + δ / 2) ^ μ * 2 ^ μ = M 0 ^ 2 * (2 + δ) ^ μ := by
    rw [mul_assoc, ← mul_pow, show ((1:ℝ) + δ / 2) * 2 = 2 + δ from by ring]
  rw [hrw]; exact h

/-- The blowup base genuinely exceeds `1` when `δ > 0`, so `(1+δ/2)^μ → ∞` (a real power-law,
unbounded by any polylog).  Recorded to make the separation from the polylog envelope explicit. -/
theorem blowup_base_gt_one {δ : ℝ} (hδ : 0 < δ) : 1 < 1 + δ / 2 := by linarith

/-!
## The character-sum realization: the exact FFT butterfly identity

This connects the abstract envelope sequence `M` above to the real object
`period ψ H b = Σ_{x∈H} ψ(b·x)` (`ψ` an additive character, `H = μ_{2^k}`).  The dyadic
butterfly identity below is the EXACT recursion whose squared form gives `M(i+1)² ≤ (2+δ)·M(i)²`;
it is fully proven here, and it makes precise that the *only* open quantity is the cross term
`2 Re(period Hk1 b · conj(period Hk1 (b·ζ)))` (the alignment excess `δ`).
-/

section Butterfly

variable {F : Type*} [Field F] [DecidableEq F]

/-- The subgroup character sum (Gaussian period) at frequency `b`: `∑_{x∈H} ψ(b·x)`. -/
noncomputable def period (ψ : F → ℂ) (H : Finset F) (b : F) : ℂ := ∑ x ∈ H, ψ (b * x)

/-- **The dyadic FFT butterfly identity (exact, proven).**  If the level-`k` subgroup `Hk` splits
as the disjoint union of the level-`(k−1)` subgroup `Hk1` and its `ζ`-coset (`ζ ≠ 0`), then the
period at `b` is the sum of two level-`(k−1)` periods, at `b` and at `b·ζ`.  Squaring and taking
`max_{b≠0}` gives `M(k)² = ... ≤ (2 + δ)·M(k−1)²` with `δ` the cross-correlation term — exactly
the `DyadicDeviationDecay` input. -/
theorem period_butterfly (ψ : F → ℂ) (Hk1 Hk : Finset F) (ζ b : F) (hζ : ζ ≠ 0)
    (hsplit : Hk = Hk1 ∪ Hk1.image (fun x => ζ * x))
    (hdisj : Disjoint Hk1 (Hk1.image (fun x => ζ * x))) :
    period ψ Hk b = period ψ Hk1 b + period ψ Hk1 (b * ζ) := by
  unfold period
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image (by intro a _ c _ h; exact mul_left_cancel₀ hζ h)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

/-- **Triangle consequence.**  The butterfly gives the trivial per-level doubling `|period Hk b| ≤
|period Hk1 b| + |period Hk1 (b·ζ)|`; the genuine content (and the open input) is that the two
children do not *align* — the cross term must be `≤ δ·M(k−1)²` with `δ → 0`, not the trivial `2`. -/
theorem abs_period_butterfly_le (ψ : F → ℂ) (Hk1 Hk : Finset F) (ζ b : F) (hζ : ζ ≠ 0)
    (hsplit : Hk = Hk1 ∪ Hk1.image (fun x => ζ * x))
    (hdisj : Disjoint Hk1 (Hk1.image (fun x => ζ * x))) :
    ‖period ψ Hk b‖ ≤ ‖period ψ Hk1 b‖ + ‖period ψ Hk1 (b * ζ)‖ := by
  rw [period_butterfly ψ Hk1 Hk ζ b hζ hsplit hdisj]
  exact norm_add_le _ _

end Butterfly

end ProximityGap.Frontier.DyadicDeviationDecay

#print axioms ProximityGap.Frontier.DyadicDeviationDecay.sq_level_le_prod
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.prod_factor
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.sq_level_le_pow_mul_exp_harmonic
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.constant_excess_sq_ge
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.constant_excess_power_blowup
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.period_butterfly
#print axioms ProximityGap.Frontier.DyadicDeviationDecay.abs_period_butterfly_le
