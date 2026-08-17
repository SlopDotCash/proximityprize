/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DiBenedettoFiniteNSavingBelow

/-!
# di Benedetto near-Sidon saving: the supremum `1/24` IS the limit (#444 , constant-factor lane)

`DiBenedettoFiniteNSavingBelow.lean` proved the realised dyadic saving is STRICTLY below `1/24` at
every finite `n` (`realisedSaving_lt_nearSidon`), and its docstring asserts , **as prose, never as a
theorem** , that `1/24` is "the SUPREMUM, attained only in the `n → ∞` limit (`t_k(n) → k`)". This
file lands that limit.

The realised log-exponents converge to the integer order:

  `realisedExp energyTwo   n = logb n (3n²−3n)        → 2`,
  `realisedExp energyThree n = logb n (15n³−45n²+40n) → 3`   (as `n → ∞`),

because `logb n (E n) = log (E n) / log n`, and for `E n = c·n^k·(1 + o(1))` the difference
`log (E n) − k·log n = log (E n / n^k) → log c` is a CONVERGENT (hence bounded) sequence, while
`log n → ∞`; a convergent-over-divergent ratio tends to `0`, so `log (E n)/log n → k`.

The saving is the AFFINE (continuous) functional `diBenedettoSaving t₂ t₃ = (10 − 2t₃ − t₂/2)/72`, so

  `diBenedettoSaving (t₂(n)) (t₃(n)) → diBenedettoSaving 2 3 = 1/24`.

Combined with the finite-`n` strict shortfall (`realisedSaving_lt_nearSidon`: `< 1/24` everywhere) and
monotone approach, `1/24` is EXACTLY the supremum of the realised saving and it is ATTAINED in the
limit, never at any finite scale. This completes the boundary picture of the di Benedetto / energy /
sum-product family: its best constant-factor power-saving is `1/24` as a strict supremum-and-limit, a
fixed `12×` short of the prize cancellation exponent `1/2` (`energy_method_below_prize`).

## Probe (`/tmp/probe_dib_saving_limit.py`, `n = 2²..2⁵⁹`, exact char-0 closed forms)
- `t₂(n) → 2`, `t₃(n) → 3` monotonically from above (`t₂: 2.585@n=4 → 2.027@2⁵⁸`, `t₃: 4.32 → 3.067`).
- `saving(n) ↑ 1/24` monotone from BELOW; `saving(2,3) = 1/24` exactly. 0 fails / 58.
- decay rate: `(1/24 − saving)·ln n → 0.08285` CONSTANT ⟹ the shortfall is `Θ(1/log n)` (slow). The
  Lean theorem here lands the LIMIT (`→ 1/24`); the explicit `Θ(1/log n)` constant is recorded as the
  probe verdict, not formalised (a future quantitative brick).

## HONESTY (rules 1, 3, 6 + ASYMPTOTIC GUARD)
NOT a CORE closure. This is the LIMIT companion of the proven finite-`n` strict ceiling: it shows the
energy method's own best saving `1/24` is exactly the supremum AND the limit of the realised dyadic
saving. A NEGATIVE / boundary result , it pins the asymptotic value of a route that is `12×` short of
the prize, and makes NO capacity / beyond-Johnson / growth-law claim. Pure `ℝ`/`logb` real-analysis
limit on the proven exact-value energies; FIELD-UNIVERSAL (the saving formula is thickness-blind ,
prize-relevance only through the dyadic energy VALUES, supplied by the envelope file). Touches NEITHER
`δ*` NOR the cliff-at-`n/2` incidence object. EXTEND-proven on `realisedExp` + `diBenedettoSaving`. The
char-`p` transfer at `p = n⁴` remains a SEPARATE open input (these are the exact char-0 cyclotomic
energies). ONE sweep, ONE commit. CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Filter Topology Real

namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- **General convergence of a realised log-exponent.** If, as `n → ∞`, the difference
`log (E n) − k·log n` tends to a finite limit `L` (i.e. `E n` is asymptotically `c·n^k` with
`L = log c`), then the realised exponent `logb n (E n) = log (E n)/log n` tends to `k`.

Mechanism: `log (E n)/log n = k + (log (E n) − k·log n)/log n`, the second term being a CONVERGENT
numerator over `log n → ∞`, hence `→ 0`. -/
theorem realisedExp_tendsto_of_logDiff_tendsto {E : ℝ → ℝ} {k L : ℝ}
    (hdiff : Tendsto (fun n => Real.log (E n) - k * Real.log n) atTop (nhds L)) :
    Tendsto (fun n => realisedExp E n) atTop (nhds k) := by
  -- log n → atTop, so 1/log n → 0 and (log (E n) − k log n)/log n → L·0 = 0.
  have hlogTop : Tendsto (fun n : ℝ => Real.log n) atTop atTop := Real.tendsto_log_atTop
  -- the correction term tends to 0: (convergent)·(1/(→∞))
  have hcorr : Tendsto (fun n => (Real.log (E n) - k * Real.log n) / Real.log n) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℝ => (Real.log n)⁻¹) atTop (nhds 0) := hlogTop.inv_tendsto_atTop
    have : Tendsto (fun n => (Real.log (E n) - k * Real.log n) * (Real.log n)⁻¹) atTop
        (nhds (L * 0)) := hdiff.mul hinv
    simpa [div_eq_mul_inv, mul_zero] using this
  -- logb n (E n) = log (E n)/log n = k + correction  (eventually, where log n ≠ 0)
  have hev : (fun n => realisedExp E n)
      =ᶠ[atTop] (fun n => k + (Real.log (E n) - k * Real.log n) / Real.log n) := by
    -- for n ≥ 2, log n > 0 ≠ 0, so the algebra holds
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
    have hlogpos : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
    have hne : Real.log n ≠ 0 := ne_of_gt hlogpos
    unfold realisedExp Real.logb
    field_simp
    ring
  -- assemble: k + (→0) → k + 0 = k
  have : Tendsto (fun n => k + (Real.log (E n) - k * Real.log n) / Real.log n) atTop (nhds (k + 0)) :=
    tendsto_const_nhds.add hcorr
  rw [add_zero] at this
  exact this.congr' hev.symm

/-- **The `log`-difference of `E₂` against `n²` converges** (to `log 3`).
`log (E₂ n) − 2·log n = log (3n²−3n) − log (n²) = log ((3n²−3n)/n²) = log (3 − 3/n) → log 3`. -/
theorem energyTwo_logDiff_tendsto :
    Tendsto (fun n => Real.log (energyTwo n) - 2 * Real.log n) atTop (nhds (Real.log 3)) := by
  -- on n ≥ 2: E₂ n = 3n²−3n > 0, n² > 0, and log(E₂ n) − 2 log n = log(3 − 3/n)
  have hev : (fun n => Real.log (energyTwo n) - 2 * Real.log n)
      =ᶠ[atTop] (fun n => Real.log (3 - 3 / n)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hE : energyTwo n = (3 - 3 / n) * n ^ 2 := by
      unfold energyTwo; field_simp
    have hfac_pos : (0 : ℝ) < 3 - 3 / n := by
      have : 3 / n ≤ 3 / 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
      linarith
    rw [hE, Real.log_mul (ne_of_gt hfac_pos) (by positivity), Real.log_pow]
    push_cast; ring
  -- log(3 − 3/n) → log(3 − 0) = log 3, since 3/n → 0 and log is continuous at 3
  have h3n : Tendsto (fun n : ℝ => 3 - 3 / n) atTop (nhds (3 - 0)) := by
    have : Tendsto (fun n : ℝ => (3 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact tendsto_const_nhds.sub this
  rw [sub_zero] at h3n
  have hcont : Tendsto (fun n : ℝ => Real.log (3 - 3 / n)) atTop (nhds (Real.log 3)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp h3n
  exact hcont.congr' hev.symm

/-- **The `log`-difference of `E₃` against `n³` converges** (to `log 15`).
`log (E₃ n) − 3·log n = log ((15n³−45n²+40n)/n³) = log (15 − 45/n + 40/n²) → log 15`. -/
theorem energyThree_logDiff_tendsto :
    Tendsto (fun n => Real.log (energyThree n) - 3 * Real.log n) atTop (nhds (Real.log 15)) := by
  have hev : (fun n => Real.log (energyThree n) - 3 * Real.log n)
      =ᶠ[atTop] (fun n => Real.log (15 - 45 / n + 40 / n ^ 2)) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hE : energyThree n = (15 - 45 / n + 40 / n ^ 2) * n ^ 3 := by
      unfold energyThree; field_simp
    have hfac_pos : (0 : ℝ) < 15 - 45 / n + 40 / n ^ 2 := by
      have h1 : 45 / n ≤ 45 / 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
      have h2 : (0 : ℝ) ≤ 40 / n ^ 2 := by positivity
      linarith
    rw [hE, Real.log_mul (ne_of_gt hfac_pos) (by positivity), Real.log_pow]
    push_cast; ring
  have hpoly : Tendsto (fun n : ℝ => 15 - 45 / n + 40 / n ^ 2) atTop (nhds (15 - 0 + 0)) := by
    have ha : Tendsto (fun n : ℝ => (45 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hb : Tendsto (fun n : ℝ => (40 : ℝ) / n ^ 2) atTop (nhds 0) := by
      have hsq : Tendsto (fun n : ℝ => n ^ 2) atTop atTop :=
        Filter.tendsto_pow_atTop (by norm_num)
      exact tendsto_const_nhds.div_atTop hsq
    exact (tendsto_const_nhds.sub ha).add hb
  simp only [sub_zero, add_zero] at hpoly
  have hcont : Tendsto (fun n : ℝ => Real.log (15 - 45 / n + 40 / n ^ 2)) atTop (nhds (Real.log 15)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hpoly
  exact hcont.congr' hev.symm

/-- **The realised depth-2 exponent converges to `2`.** `t₂(n) = logb n (E₂ n) → 2`. -/
theorem realisedExp_two_tendsto :
    Tendsto (fun n => realisedExp energyTwo n) atTop (nhds 2) :=
  realisedExp_tendsto_of_logDiff_tendsto energyTwo_logDiff_tendsto

/-- **The realised depth-3 exponent converges to `3`.** `t₃(n) = logb n (E₃ n) → 3`. -/
theorem realisedExp_three_tendsto :
    Tendsto (fun n => realisedExp energyThree n) atTop (nhds 3) :=
  realisedExp_tendsto_of_logDiff_tendsto energyThree_logDiff_tendsto

/-- **HEADLINE , the realised di Benedetto saving converges to the near-Sidon `1/24`.**
`diBenedettoSaving (t₂(n)) (t₃(n)) → diBenedettoSaving 2 3 = 1/24` as `n → ∞`. With the proven
finite-`n` strict shortfall (`realisedSaving_lt_nearSidon < 1/24` everywhere), `1/24` is EXACTLY the
supremum of the realised saving and is ATTAINED only in the limit , never at any finite scale. The
energy method's best constant-factor saving is thus pinned at `1/24` (sup = lim), a fixed `12×` short
of the prize cancellation exponent `1/2`. -/
theorem realisedSaving_tendsto_nearSidon :
    Tendsto (fun n => diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n))
      atTop (nhds (1 / 24)) := by
  -- diBenedettoSaving t₂ t₃ = (10 − 2 t₃ − t₂/2)/72 is jointly continuous (affine) in (t₂, t₃).
  have hsave : Tendsto (fun n => diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n))
      atTop (nhds (diBenedettoSaving 2 3)) := by
    unfold diBenedettoSaving
    have h2 := realisedExp_two_tendsto
    have h3 := realisedExp_three_tendsto
    -- (10 − 2·t₃(n) − t₂(n)/2)/72 → (10 − 2·3 − 2/2)/72
    exact ((tendsto_const_nhds.sub (h3.const_mul 2)).sub (h2.div_const 2)).div_const 72
  rwa [diBenedettoSaving_nearSidon] at hsave

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedExp_tendsto_of_logDiff_tendsto
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyTwo_logDiff_tendsto
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyThree_logDiff_tendsto
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedExp_two_tendsto
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedExp_three_tendsto
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedSaving_tendsto_nearSidon
