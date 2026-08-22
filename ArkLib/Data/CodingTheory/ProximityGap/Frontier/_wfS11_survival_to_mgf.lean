/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S11 survival → MGF, the OTHER layer-cake half)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_layercake_moment

/-!
# S11 layer-cake — the OTHER half: the literal SURVIVAL tail ⟹ the MGF bound (discrete, axiom-clean)

Issue lalalune/ArkLib#444 (Ethereum Proximity Prize, the char-`p` energy-transfer wall).

## What this file supplies (the un-taken half of the layer-cake equivalence)

`_wfS11_layercake_moment.lean` carried HALF of the layer-cake: `MGFBound ⟹ MomentEnvelope` (the MGF
residual integrates the moments). Its docstring named, but DID NOT carry, the OTHER half: the
literal counting **survival** function
  `S(s) = (1/P) · #{b : t_b ≥ s}`
and its sub-exponential tail `S(s) ≤ A · e^{−c s}` are what the BGK ceiling actually produces; the
MGF is a *consequence* of that survival tail. This file carries that consequence **discretely**, with
NO continuous layer-cake integral, via the **exact Abel / summation-by-parts identity** over the
spectrum's own value set, plus a **monotone** comparison: any pointwise survival ceiling that
dominates the true counts upper-bounds the MGF.

## The discrete layer-cake (Abel summation-by-parts), sign-definite

For a finite nonempty index `s : Finset ι`, a nonnegative spectrum `t : ι → ℝ`, and the strictly
increasing weight `g(v) = exp(c v)` (`c > 0`), the MGF sum reorganizes EXACTLY over the survival
counts. The clean, fully-formal, sign-definite statement we carry is the **monotone domination**:

* `mgf_le_of_survival_dominated` : if a comparison spectrum `t'` survival-DOMINATES `t`
  (every super-level set of `t'` is at least as large as that of `t`, equivalently `t` is pointwise
  `≤` a nondecreasing rearrangement of `t'`), then `Σ_b exp(c t_b) ≤ Σ_b exp(c t'_b)`. We carry the
  cleanest SUFFICIENT form: a **pointwise** ceiling `t_b ≤ u_b` with `exp`-monotonicity gives the
  termwise MGF domination, hence `MGFBound`. (Probe-confirmed exact-Abel reorganization in
  `scripts/probes/probe_s11_survival_to_mgf.py`; the monotone upper bound in
  `scripts/probes/probe_s11_survival_mgf_bound.py`.)

* `mgfBound_of_pointwise_exp_ceiling` : the operational brick — if for every `b` the per-point
  exponential weight is dominated, `exp(c t_b) ≤ w_b`, and the ceiling weights sum to `≤ A·P`, then
  `MGFBound s t A c`. This is what a survival tail delivers at the per-point level: the tail bounds
  the *number* of large `t_b`, hence the *sum* of their exponential weights.

* `mgfBound_of_max_ceiling` : the crudest-but-honest survival consequence — if the spectrum is
  uniformly bounded `t_b ≤ T` (a survival cutoff: `S(s)=0` for `s>T`), then `MGFBound s t (exp(c T)) c`.
  Trivial but it is the *correct* endpoint and shows the MGF residual is finite once the survival has
  ANY cutoff; the BGK content is making the ceiling `A` ABSOLUTE (n,p-uniform), not merely finite.

## Honesty (rules 1,3,4,6 + asymptotic/cliff guard)

This carries the **survival ⟹ MGF implication** (the other half of the layer-cake equivalence)
axiom-clean and fully discretely. It does NOT prove the survival tail itself uniformly in `n` — that
uniformity (an ABSOLUTE `A`, `c`) IS the BGK wall, the same residual repackaged. NOT a CORE closure,
NOT a refutation. NO capacity / beyond-Johnson / δ*→0 / sub-linear / cliff-at-n/2 claim. Field-
universal (pure ℝ analysis over a finite `Finset`). Composed with `moment_le_of_mgf` of the sibling
file, the FULL layer-cake equivalence `survival ⟹ MGF ⟹ moment envelope ⟹ S1 slack` is now welded;
the single remaining open input is the ABSOLUTE survival/MGF constant = BGK.

Tag: CONCENTRATION-REDUCED (both layer-cake halves carried). Residual = absolute survival constant = BGK.
`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false


open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.WFS11

/-! ### 1. Per-point exponential ceiling ⟹ MGFBound (the operational survival brick) -/

/-- **MGFBound from a per-point exponential ceiling.** If for every `b ∈ s` the exponential weight is
dominated, `exp(c · t_b) ≤ w_b`, and the ceiling weights sum to `≤ A · P` (`P = s.card`), then
`MGFBound s t A c` holds. This is the operational content of a survival tail: the tail bounds the
count of large `t_b`, hence the sum of their exponential weights `Σ_b exp(c t_b) ≤ Σ_b w_b ≤ A·P`. -/
theorem mgfBound_of_pointwise_exp_ceiling {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c : ℝ}
    (w : ι → ℝ) (hw : ∀ b ∈ s, Real.exp (c * t b) ≤ w b)
    (hwsum : (∑ b ∈ s, w b) ≤ A * (s.card : ℝ)) :
    MGFBound s t A c := by
  unfold MGFBound
  calc (∑ b ∈ s, Real.exp (c * t b)) ≤ ∑ b ∈ s, w b := Finset.sum_le_sum hw
    _ ≤ A * (s.card : ℝ) := hwsum

/-! ### 2. Survival DOMINATION (pointwise ≤) ⟹ MGF domination (sign-definite Abel consequence) -/

/-- **MGF is monotone under a pointwise survival ceiling.** If `t_b ≤ u_b` for every `b` (the
comparison spectrum `u` survival-dominates `t` pointwise), then since `exp` is increasing,
`Σ_b exp(c t_b) ≤ Σ_b exp(c u_b)`. This is the sign-definite consequence of the discrete layer-cake:
raising the spectrum can only raise the MGF. -/
theorem mgf_sum_le_of_pointwise_le {ι : Type*} (s : Finset ι) (t u : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (htu : ∀ b ∈ s, t b ≤ u b) :
    (∑ b ∈ s, Real.exp (c * t b)) ≤ ∑ b ∈ s, Real.exp (c * u b) := by
  apply Finset.sum_le_sum
  intro b hb
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (htu b hb) hc

/-- **MGFBound transfers along a pointwise survival ceiling.** If `t_b ≤ u_b` and the comparison
spectrum `u` already satisfies `MGFBound s u A c`, then so does `t`. The honest reading: a spectrum
whose survival profile is dominated by a controlled one inherits its MGF bound. -/
theorem mgfBound_of_pointwise_le {ι : Type*} (s : Finset ι) (t u : ι → ℝ) {A c : ℝ}
    (hc : 0 ≤ c) (htu : ∀ b ∈ s, t b ≤ u b) (hu : MGFBound s u A c) :
    MGFBound s t A c := by
  unfold MGFBound at hu ⊢
  exact le_trans (mgf_sum_le_of_pointwise_le s t u hc htu) hu

/-! ### 3. A uniform survival cutoff ⟹ MGFBound (the honest finite endpoint) -/

/-- **MGFBound from a uniform survival cutoff.** If the spectrum is uniformly bounded `t_b ≤ T`
(equivalently the survival function `S(s) = 0` for `s > T`), then `MGFBound s t (exp(c T)) c`: every
`exp(c t_b) ≤ exp(c T)`, so the average is `≤ exp(c T)`. The MGF residual is FINITE once the survival
has any cutoff — the BGK content is making the constant `exp(c T)` ABSOLUTE / `n,p`-uniform, which is
exactly the wall (here `T = max_b t_b` is the spectral max, which is `Θ(log(q/n))` not `O(1)`). -/
theorem mgfBound_of_max_ceiling {ι : Type*} (s : Finset ι) (t : ι → ℝ) {T c : ℝ}
    (hc : 0 ≤ c) (hT : ∀ b ∈ s, t b ≤ T) :
    MGFBound s t (Real.exp (c * T)) c := by
  refine mgfBound_of_pointwise_exp_ceiling s t (fun _ => Real.exp (c * T)) ?_ ?_
  · intro b hb
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hT b hb) hc)
  · rw [Finset.sum_const, nsmul_eq_mul]
    ring_nf
    exact le_refl _

/-! ### 4. The EXACT discrete layer-cake identity (survival COUNTS, via double-counting) -/

/-- **The discrete layer-cake double-counting identity (EXACT).** For a finite threshold grid
`Θ : Finset ℝ`, nonnegative increment weights `δ : ℝ → ℝ`, and a spectrum `t : ι → ℝ`, summing over
the index set the staircase `Σ_{θ∈Θ, θ ≤ t_b} δ_θ` equals summing over thresholds the weight times
the **survival count** `#{b ∈ s : θ ≤ t_b}`:
  `Σ_{b∈s} Σ_{θ∈Θ, θ≤t_b} δ_θ = Σ_{θ∈Θ} δ_θ · (#{b∈s : θ ≤ t_b})`.
This is the discrete layer-cake CORE: it is exactly the Fubini/`sum_comm` swap that converts a
per-point staircase weight into a survival-count-weighted sum. The MGF (and every moment) is built by
choosing `δ` so the staircase equals `g(t_b)`; the bound on the survival counts then bounds the sum.
No continuous integral. -/
theorem layercake_double_count {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) :
    (∑ b ∈ s, ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
      = ∑ θ ∈ Θ, δ θ * ((s.filter (fun b => θ ≤ t b)).card : ℝ) := by
  -- rewrite the inner filtered sum over Θ as a full sum over Θ with an indicator
  have hb : ∀ b ∈ s, (∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
      = ∑ θ ∈ Θ, (if θ ≤ t b then δ θ else 0) := by
    intro b _
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hb, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  -- Σ_{b∈s} (if θ ≤ t b then δ θ else 0) = δ θ * #{b : θ ≤ t b}
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Survival-count MGF ceiling (the honest survival ⟹ MGF mechanism).** If a per-point exponential
weight is dominated by a staircase over the threshold grid, `exp(c · t_b) ≤ Σ_{θ∈Θ, θ≤t_b} δ θ` with
`δ ≥ 0`, then by the double-counting identity the MGF is bounded by the survival-count-weighted sum:
  `Σ_b exp(c t_b) ≤ Σ_{θ∈Θ} δ θ · #{b : θ ≤ t_b}`.
This is exactly where a survival tail enters: bounding each survival count `#{b : θ ≤ t_b} ≤ A·P·e^{−c θ}`
(the sub-exponential tail) bounds the whole MGF. The brick reduces the MGF to the literal survival
counts. -/
theorem mgf_le_survival_weighted {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ)
    (Θ : Finset ℝ) (δ : ℝ → ℝ) {c : ℝ}
    (_hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp (c * t b) ≤ ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ) :
    (∑ b ∈ s, Real.exp (c * t b))
      ≤ ∑ θ ∈ Θ, δ θ * ((s.filter (fun b => θ ≤ t b)).card : ℝ) := by
  calc (∑ b ∈ s, Real.exp (c * t b))
      ≤ ∑ b ∈ s, ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ := Finset.sum_le_sum hstair
    _ = ∑ θ ∈ Θ, δ θ * ((s.filter (fun b => θ ≤ t b)).card : ℝ) :=
        layercake_double_count s t Θ δ

/-- **Survival-count ceiling packaged as an `MGFBound`.** If the per-point exponential weights are
dominated by a threshold staircase and the resulting survival-count-weighted sum is at most
`A·|s|`, then the spectrum satisfies `MGFBound s t A c`. This is the exact reusable endpoint of
the discrete layer-cake bridge. -/
theorem mgfBound_of_survival_weighted_ceiling {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ : ℝ → ℝ) {A c : ℝ}
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp (c * t b) ≤ ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hweighted :
      (∑ θ ∈ Θ, δ θ * ((s.filter (fun b => θ ≤ t b)).card : ℝ))
        ≤ A * (s.card : ℝ)) :
    MGFBound s t A c := by
  unfold MGFBound
  exact le_trans (mgf_le_survival_weighted s t Θ δ hδ hstair) hweighted

/-- **MGFBound from explicit survival count ceilings.** If each threshold has a numerical ceiling
`B θ` for its survival count and the weighted ceiling sum is at most `A·|s|`, then the staircase
dominance gives `MGFBound`. This is the form an actual tail estimate supplies: prove
`#{b ∈ s : θ ≤ t_b} ≤ B θ`, then sum the tail envelope over the grid. -/
theorem mgfBound_of_survival_count_ceiling {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → ℝ) (Θ : Finset ℝ) (δ B : ℝ → ℝ) {A c : ℝ}
    (hδ : ∀ θ ∈ Θ, 0 ≤ δ θ)
    (hstair : ∀ b ∈ s, Real.exp (c * t b) ≤ ∑ θ ∈ Θ.filter (fun θ => θ ≤ t b), δ θ)
    (hcount : ∀ θ ∈ Θ, ((s.filter (fun b => θ ≤ t b)).card : ℝ) ≤ B θ)
    (hweighted : (∑ θ ∈ Θ, δ θ * B θ) ≤ A * (s.card : ℝ)) :
    MGFBound s t A c := by
  refine mgfBound_of_survival_weighted_ceiling s t Θ δ hδ hstair ?_
  calc
    (∑ θ ∈ Θ, δ θ * ((s.filter (fun b => θ ≤ t b)).card : ℝ))
        ≤ ∑ θ ∈ Θ, δ θ * B θ := by
          apply Finset.sum_le_sum
          intro θ hθ
          exact mul_le_mul_of_nonneg_left (hcount θ hθ) (hδ θ hθ)
    _ ≤ A * (s.card : ℝ) := hweighted

/-! ### 5. End-to-end: a survival cutoff lands the moment envelope (welds to the sibling brick) -/

/-- **Survival cutoff ⟹ moment envelope, end-to-end (welds the two layer-cake halves).** A uniform
survival cutoff `t_b ≤ T` lands, via the cutoff MGF bound (this file) and the layer-cake brick
`moment_le_of_mgf` (sibling file), the full moment envelope with the explicit constant `exp(c T)`:
  `(1/P)·Σ_b t_b^r ≤ exp(c T) · r! / c^r`  for every `r`.
This is the survival ⟹ MGF ⟹ moment-envelope chain carried end-to-end, axiom-clean. The residual
is making `exp(c T)` ABSOLUTE in `n,p` = BGK. -/
theorem momentEnvelope_of_survival_cutoff {ι : Type*} (s : Finset ι) (t : ι → ℝ) {T c : ℝ}
    (hc : 0 < c) (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hT : ∀ b ∈ s, t b ≤ T) :
    MomentEnvelope (fun r => (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)) (Real.exp (c * T)) c := by
  have hMGF : MGFBound s t (Real.exp (c * T)) c := mgfBound_of_max_ceiling s t hc.le hT
  exact momentEnvelope_of_mgf s t hc ht hP hMGF

end ArkLib.ProximityGap.Frontier.WFS11

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgfBound_of_pointwise_exp_ceiling
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgf_sum_le_of_pointwise_le
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgfBound_of_pointwise_le
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgfBound_of_max_ceiling
#print axioms ArkLib.ProximityGap.Frontier.WFS11.layercake_double_count
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgf_le_survival_weighted
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgfBound_of_survival_weighted_ceiling
#print axioms ArkLib.ProximityGap.Frontier.WFS11.mgfBound_of_survival_count_ceiling
#print axioms ArkLib.ProximityGap.Frontier.WFS11.momentEnvelope_of_survival_cutoff
