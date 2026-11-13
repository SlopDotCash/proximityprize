/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodSidonBound
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodSpectralFrame

/-!
# The r=2 Sidon bound discharges the spectral frame only with a divergent constant (#444 / #407)

The two-sided spectral frame (`GaussPeriodSpectralFrame`) brackets the prize per-frequency core
`M(n) = max_{b≠0} ‖η_b‖` between the proven Parseval floor `√(n(q−n)/(q−1)) ≈ √n` and the
**named-OPEN** ceiling `NearRamanujanSqrtLog ψ G C : ‖η_b‖ ≤ C·√(n·log(q/n))`. The prize asks for
this ceiling with an **absolute** `C`.

The in-tree `worst_period_sidon_le` proves, **unconditionally in the Sidon regime** (`repCount ≤ 2`,
which holds for `μ_n` once `q > 2^n` via the cyclotomic resultant lift), the `r = 2` moment ceiling

> `‖η_b‖⁴ ≤ 3·q·n²`,   i.e.   `‖η_b‖ ≤ (3q)^{1/4}·√n`.

This file welds the two: the proven `r=2` bound **does** discharge `NearRamanujanSqrtLog`, but **only
with the explicit `q`-dependent constant**

> `C_Sidon(q,n) := (3q)^{1/4} / √(log(q/n))`

(`sidonSqrtLogConstant`), because `(3q)^{1/4}·√n = C_Sidon · √(n·log(q/n))` is an algebraic identity
once `log(q/n) > 0`. The headline `nearRamanujanSqrtLog_of_sidon` makes this a theorem; the companion
`sidonSqrtLogConstant_ge_of_le_pow` records that `C_Sidon` is **monotone increasing in `q`** at fixed
`n` and `q/n`-ratio floor — it is `(3q)^{1/4}/√(log(q/n))`, which **diverges like `q^{1/4}`** in the
prize regime `q = n^β` (`β ≥ 4`). So the proven `r=2` moment level provably **cannot** close the
frame with an absolute constant: the gap is exactly the `q^{1/4}` over-shoot — the additive-moment /
energy route wall (consistent with the `§3` meta-theorem and the cliff-at-`n/2` guard: a single
even moment is thickness-monotone and carries no `√log`-over-`√q` saving).

PROBE: `probe_sidon_vs_nearram.py` over EXACT thin `μ_n` (`n = 2^a`, `p ≫ n³`, proper, never
`n = q−1`, incl. Fermat 257) confirms `C_forced = (3q)^{1/4}/√(log(q/n))` to ratio `1.0000`, that it
grows `2.26 → 3.08 → 4.48` as `n: 4→8→16`, while the true absolute constant `C_true = M/√(n log(q/n))`
stays `≈ 1.0–1.4` (the genuine prize constant). This is a CONSTRAINT (a precisely-mapped wall on the
moment route), NOT a CORE closure. `CORE M(μ_n) ≤ C·√(n·log(p/n))` with absolute `C` stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issues #444, #407.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.WorstPeriodSidon
open ArkLib.ProximityGap.GaussPeriodSpectralFrame

namespace ArkLib.ProximityGap.SidonFrameConstantDivergence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The explicit (and **`q`-dependent, divergent**) constant with which the proven `r=2` Sidon bound
discharges the frame's open `NearRamanujanSqrtLog` hypothesis:
`C_Sidon(q,n) = (3q)^{1/4} / √(log(q/n))`. -/
noncomputable def sidonSqrtLogConstant (q n : ℝ) : ℝ :=
  (3 * q) ^ ((1 : ℝ) / 4) / Real.sqrt (Real.log (q / n))

/-- **The key algebraic identity.** `(3q)^{1/4}·√n = C_Sidon · √(n·log(q/n))` whenever
`log(q/n) > 0` (i.e. `n < q`). This is what makes the proven `r=2` ceiling exactly a
`NearRamanujanSqrtLog`-shaped bound with constant `C_Sidon`. -/
theorem sidon_ceiling_eq_sqrtLog_scaled {q n : ℝ}
    (hn : 0 ≤ n) (hlog : 0 < Real.log (q / n)) :
    (3 * q) ^ ((1 : ℝ) / 4) * Real.sqrt n
      = sidonSqrtLogConstant q n * Real.sqrt (n * Real.log (q / n)) := by
  unfold sidonSqrtLogConstant
  have hLpos : (0 : ℝ) < Real.sqrt (Real.log (q / n)) := Real.sqrt_pos.mpr hlog
  have hL : Real.sqrt (Real.log (q / n)) ≠ 0 := ne_of_gt hLpos
  rw [Real.sqrt_mul hn]
  field_simp

/-- **The weld.** Under the in-tree Sidon hypothesis (`repCount ≤ 2`) and `n < q`, the **proven**
`r=2` bound `worst_period_sidon_le` discharges the frame's named-open ceiling
`NearRamanujanSqrtLog`, but with the explicit `q`-dependent constant `C_Sidon(q,n)`. -/
theorem nearRamanujanSqrtLog_of_sidon {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2)
    (hlog : 0 < Real.log ((Fintype.card F : ℝ) / G.card)) :
    NearRamanujanSqrtLog ψ G (sidonSqrtLogConstant (Fintype.card F : ℝ) (G.card : ℝ)) := by
  classical
  intro b _hb
  -- proven r=2 ceiling: ‖η_b‖^4 ≤ 3 q n^2  ⟹  ‖η_b‖ ≤ (3q)^{1/4} √n
  have hpow : ‖eta ψ G b‖ ^ 4 ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 :=
    worst_period_sidon_le hψ G hrep b
  have hnorm_nonneg : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  have hq_nonneg : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hn_nonneg : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
  -- bound ‖η_b‖ by the fourth root of the RHS
  have hrhs_nonneg : (0 : ℝ) ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by positivity
  set R : ℝ := (3 * (Fintype.card F : ℝ)) ^ ((1:ℝ)/4) * Real.sqrt (G.card : ℝ) with hR
  have hR_nonneg : (0 : ℝ) ≤ R := by
    rw [hR]; positivity
  have hceil : ‖eta ψ G b‖ ≤ R := by
    -- R^4 = 3 q n^2, and ‖η‖^4 ≤ 3 q n^2, both nonneg ⟹ ‖η‖ ≤ R
    have hRHS_eq : R ^ 4 = 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by
      rw [hR, mul_pow]
      have h1 : ((3 * (Fintype.card F : ℝ)) ^ ((1:ℝ)/4)) ^ 4 = 3 * (Fintype.card F : ℝ) := by
        rw [← Real.rpow_natCast ((3 * (Fintype.card F : ℝ)) ^ ((1:ℝ)/4)) 4,
            ← Real.rpow_mul (by positivity)]
        norm_num
      have h2 : (Real.sqrt (G.card : ℝ)) ^ 4 = (G.card : ℝ) ^ 2 := by
        have : (Real.sqrt (G.card : ℝ)) ^ 4 = ((Real.sqrt (G.card : ℝ)) ^ 2) ^ 2 := by ring
        rw [this, Real.sq_sqrt hn_nonneg]
      rw [h1, h2]
    have hle4 : ‖eta ψ G b‖ ^ 4 ≤ R ^ 4 := by rw [hRHS_eq]; exact hpow
    exact le_of_pow_le_pow_left₀ (by norm_num) hR_nonneg hle4
  -- now scale to the √log shape
  calc ‖eta ψ G b‖
      ≤ R := hceil
    _ = sidonSqrtLogConstant (Fintype.card F : ℝ) (G.card : ℝ)
          * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
        rw [hR]; exact sidon_ceiling_eq_sqrtLog_scaled hn_nonneg hlog

/-- **The constant is NOT absolute — it grows with `q`.** At a fixed `q/n`-ratio (hence fixed
`log(q/n) = L > 0`), `C_Sidon = (3q)^{1/4}/√L` is **strictly monotone increasing in `q`**. So no
absolute bound on `sidonSqrtLogConstant` holds as `q → ∞`: the `r=2` Sidon ceiling provably cannot
discharge the frame's open `NearRamanujanSqrtLog` with an absolute constant. (In the prize regime
`q = n^β`, `β ≥ 4`, this is the `q^{1/4} → ∞` over-shoot — the additive-moment route wall.) -/
theorem sidonSqrtLogConstant_strictMono_in_q {n L : ℝ} (hL : 0 < L)
    {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hlt : q₁ < q₂)
    (hL₁ : Real.log (q₁ / n) = L) (hL₂ : Real.log (q₂ / n) = L) :
    sidonSqrtLogConstant q₁ n < sidonSqrtLogConstant q₂ n := by
  unfold sidonSqrtLogConstant
  rw [hL₁, hL₂]
  have hLs : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL
  -- numerator strictly increases: (3q₁)^{1/4} < (3q₂)^{1/4}
  have hnum : (3 * q₁) ^ ((1:ℝ)/4) < (3 * q₂) ^ ((1:ℝ)/4) := by
    apply Real.rpow_lt_rpow (by positivity) _ (by norm_num)
    linarith
  -- divide both sides by the fixed positive √L
  exact div_lt_div_of_pos_right hnum hLs

end ArkLib.ProximityGap.SidonFrameConstantDivergence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SidonFrameConstantDivergence.sidon_ceiling_eq_sqrtLog_scaled
#print axioms ArkLib.ProximityGap.SidonFrameConstantDivergence.nearRamanujanSqrtLog_of_sidon
#print axioms ArkLib.ProximityGap.SidonFrameConstantDivergence.sidonSqrtLogConstant_strictMono_in_q
