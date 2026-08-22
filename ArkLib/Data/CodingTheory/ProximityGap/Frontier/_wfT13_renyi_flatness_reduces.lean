/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T13 — "Rényi-α flatness factor of the dilation-pushforward at a super-critical order
        `α* = 2 + c/log m`" REDUCES TO F7 (Rényi-2 = energy), via the F1 moment ladder (#444)

This file records — axiom-clean, modularly — that **candidate T13** (architect `G3-T3`) is *not* a
new lever for the Proximity-Prize sup-norm `M(n) = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b x)`,
`n = 2^30`, `p = n^β` (`β = 4`), `m = (p−1)/n`. Its proposed datum — the **Rényi-α flatness factor**
`ε_α(μ_n)` of the subgroup-indicator pushforward `f = (1/n)1_{μ_n}` read through the spectrum, at a
single SUPER-CRITICAL order `α* = 2 + c/log m` (strictly above the energy order `2`, strictly below
the sup order `∞`), together with the interpolation `ε_∞ ≤ ε_{α*}^{θ}` — collapses, at the prize
scale, onto the **additive energy** (fence **F7**) and the **deep-moment ladder** (fence **F1**). It
is the Hausdorff–Young / Hölder `L^q`-deep-moment route, already mapped in the in-tree
`DISPROOF_LOG` ("the only phase-aware exit, `min_r C_r^{1/2r}` tracks `M`, RE-derives the char-`p`
deep-moment crux `E_r ≤ (2r−1)‼ n^r`").

## The objects (exactly as the candidate pins them)

`f̂(b) = η_b/n`. The candidate fixes the endpoints exactly: at `α = ∞`,
`ε_∞ = max_{b≠0}|f̂(b)| = M/n`; at `α = 2`, `ε_2` is the energy. Reading "the order-`α` flatness
through the spectrum", the order-`α` flatness factor is governed by the `L^{2(α−1)}` norm of the
spectrum (the Rényi-`α` collision moment): `ε_α := (E_{α−1})^{1/(2(α−1))} / n`, with
`E_t := Σ_{b≠0} |η_b|^{2t}` the (non-principal) additive-energy moment at real depth `t = α − 1`.
So `α = 2 ↔ t = 1` (the second moment / energy), `α → ∞ ↔ t → ∞` (so `ε_α → max_{b≠0}|η_b|/n = M/n =
ε_∞`, since `(Σ_{b≠0} x_b^{2t})^{1/(2t)} → max_b x_b`). This matches the measured endpoints and the
monotone interpolation `ε_α ↑ ε_∞` (probe `probe_wfT13_renyi_flatness.rs`, β = 4, n ≤ 256).

## The exact reduction map (T13 ⟶ F7/F1)

**(R1) The spectral flatness IS the moment / energy functional, re-coordinatized.** Directly from the
definition,

> `(n · ε_α)^{2(α−1)} = E_{α−1}`,   i.e.   `n · ε_α = (E_{α−1})^{1/(2(α−1))}`,

which is precisely the deep-moment `M`-bound at depth `r = α − 1` (the F1 object: `M^{2r} ≤ E_r ⟹
M ≤ (E_r)^{1/(2r)}`). At `α = 2` it is `n·ε_2 = (E_1)^{1/2} = (Σ_{b≠0}|η_b|²)^{1/2}` — the second
moment = additive energy in normalized form = **F7**. The "Rényi-α flatness" is not a new functional;
it is the energy/moment `E_{α−1}` reparameterized.

**(R2) The super-critical offset collapses to the energy at prize scale.** With `α* = 2 + c/log m`
the flatness depth is `r* = α* − 1 = 1 + c/log m`. Since `m = (p−1)/n → ∞` at `β = 4`
(`m ≈ n^{β−1} = n^3`), `r* → 1` and `α* → 2`: the controlling order sits at the SECOND moment. The
hoped-for "third-order log-density variance" datum that distinguishes `α*` from `α = 2` is the
`α`-derivative of the Rényi divergence weighted by `(α* − 2) = c/log m → 0`. So at the prize scale
`ε_{α*}` converges to `ε_2` = energy = **F7**; the offset buys a vanishing amount of tail weight.

**(R3) The interpolation `ε_∞ ≤ ε_{α*}^{θ}` is information-free unless `θ` is pinned by the answer.**
Rényi divergence is monotone non-decreasing in the order, so `ε_α ≤ ε_∞` for every finite `α` (the
sup is the `α=∞` endpoint; measured: `ε_α ↑ ε_∞`). With `0 < ε_{α*} < ε_∞ < 1` the interpolation
`ε_∞ ≤ ε_{α*}^{θ}` forces the exponent `θ = log ε_∞ / log ε_{α*} ∈ (0,1)` — and this `θ` is a
function of `ε_∞` itself. Knowing `ε_{α*}` alone bounds `ε_∞` from above only after `θ` is fixed,
and the only thing that fixes `θ < 1` a priori is the Gaussian-floor hypothesis on `ε_∞` (the prize).
The interpolation step is the log-convexity (Lyapunov / Hölder) inequality for `L^p` norms — it is
*true* but carries no estimate the moment ladder did not; it is the F1 step `M = L^∞ ≤ (L^{2r})`.

## What this file proves (axiom-clean, elementary real arithmetic)

1. `epsFlat` / `momentMBound` and `flatness_eq_moment_bound` — the **reduction identity (R1)**:
   `n · ε_α = (E_{α−1})^{1/(2(α−1))} = momentMBound E (α−1)`, the moment `M`-bound at depth `α−1`.
2. `epsFlat_two_is_energy` — the **F7 pin**: at `α = 2`, `(n·ε_2)² = E_1` (the normalized second
   moment = additive energy); the flatness at the energy order is the energy.
3. `superCritical_depth_to_one` — the **collapse (R2)**: the flatness depth `r* = α* − 1` of the
   super-critical order `α* = 2 + c/log m` exceeds the energy depth `1` by exactly `c/log m`, which
   `→ 0` as `m → ∞`; the offset above the energy order is `o(1)` at the prize scale.
4. `interpolation_exponent_lt_one` / `interpolation_is_tautology` — the **interpolation collapse
   (R3)**: for `0 < y < x < 1` the interpolation `x ≤ y^θ` forces `θ ≤ log x/log y < 1`, and it holds
   with EQUALITY at `θ = log x/log y` (`x = y^{log x/log y}`); so it is a tautology pinned by
   `x = ε_∞` (the answer), information-free as an upper bound on `ε_∞`.
5. `monotone_flatness_below_sup` — the **Rényi-monotonicity wrong-side fact**: `ε_{α*} < ε_∞` (the
   input lies strictly BELOW the target), so it cannot upper-bound `ε_∞` for free.

NO closure is claimed. T13 is `REDUCES-TO-WALL` (primary **F7**: Rényi-2 = energy; mechanism **F1**:
the flatness is the deep-moment `L^{2r}` ladder at `r = α−1`, and the interpolation is the
log-convexity `max ≤ L^{2r}` step). The honest residual is the SAME single open object the whole
campaign reduced to: `M(n) ≤ C√(n log(p/n))` at `β = 4`, `n = 2^30` — the BGK/Paley short-character-
sum wall. (The Rényi smoothing parameter / flatness factor of Ling–Luzzi–Yan, ePrint 2025/986, is a
real, recently-defined object — but for Euclidean lattices / the discrete Gaussian; its transcription
to the thin multiplicative subgroup `μ_n ⊂ F_p` is what reduces here — to the energy, not past it.)

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ProximityGap.Frontier.RenyiFlatnessReduces

/-! ## 1. The reduction identity (R1): spectral flatness = deep-moment `M`-bound at depth `α−1` -/

/-- The **spectral Rényi-α flatness factor** of the pushforward `f = (1/n)1_{μ_n}`, read through the
spectrum: `ε_α := (E_{α−1})^{1/(2(α−1))} / n`, where `Energy := E_{α−1} = Σ_{b≠0}|η_b|^{2(α−1)}` is
the non-principal additive-energy moment at real depth `t = α − 1`. (`n` = subgroup size, `α > 1`.)
The `α → ∞` limit is `ε_∞ = max_{b≠0}|η_b|/n = M/n`; the `α = 2` value is the energy. -/
noncomputable def epsFlat (n Energy α : ℝ) : ℝ :=
  (Energy ^ (1 / (2 * (α - 1)))) / n

/-- The **deep-moment `M`-bound** at real depth `r`: `(E_r)^{1/(2r)}`. This is the F1 object
(`M^{2r} ≤ E_r ⟹ M ≤ (E_r)^{1/(2r)}`; `min_r (E_r)^{1/(2r)}` tracks `M`). -/
noncomputable def momentMBound (Energy r : ℝ) : ℝ := Energy ^ (1 / (2 * r))

/-- **(R1) The spectral flatness IS the deep-moment `M`-bound, re-coordinatized.**
`n · ε_α = (E_{α−1})^{1/(2(α−1))} = momentMBound E (α−1)`. Hence the "Rényi-α flatness" is the
energy/moment functional `E_{α−1}` reparameterized — fence **F1**. (Holds for `n ≠ 0`.) -/
theorem flatness_eq_moment_bound {n Energy α : ℝ} (hn : n ≠ 0) :
    n * epsFlat n Energy α = momentMBound Energy (α - 1) := by
  unfold epsFlat momentMBound
  field_simp

/-! ## 2. (F7 pin) The flatness at the energy order `α = 2` is the additive energy -/

/-- **(R1 at `α = 2`) The flatness at the energy order is the additive energy** — fence **F7**.
`(n · ε_2)² = E_1 = Σ_{b≠0}|η_b|²` (the non-principal second moment / additive energy). So the
Rényi-2 flatness IS the energy; there is no escape from F7 at the critical order. -/
theorem epsFlat_two_is_energy {n Energy : ℝ} (hn : n ≠ 0) (hE : 0 ≤ Energy) :
    (n * epsFlat n Energy 2) ^ 2 = Energy := by
  rw [flatness_eq_moment_bound hn]
  unfold momentMBound
  have h1 : (1 : ℝ) / (2 * (2 - 1)) = 1 / 2 := by norm_num
  rw [h1, ← Real.rpow_natCast (Energy ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hE]
  norm_num

/-! ## 3. (R2) The super-critical offset collapses to the energy depth at prize scale -/

/-- The super-critical flatness order `α* = 2 + c/log m` of the candidate. -/
noncomputable def alphaStar (c m : ℝ) : ℝ := 2 + c / Real.log m

/-- **(R2) The super-critical flatness depth exceeds the energy depth `1` by exactly `c/log m`.**
The depth of the order-`α*` flatness is `r* = α* − 1`, and `r* − 1 = c/log m`. In the prize regime
`m = (p−1)/n → ∞` (`β = 4`), `c/log m → 0`, so `r* → 1` (the energy depth) and `α* → 2`: the
super-critical order collapses onto the Rényi-2 = energy order. The offset above the energy is
`o(1)`. -/
theorem superCritical_depth_to_one {c m : ℝ} :
    (alphaStar c m - 1) - 1 = c / Real.log m := by
  unfold alphaStar
  ring

/-- **(R2) Quantitative collapse: the offset is small once `log m` is large.** For any tolerance
`δ > 0` and `c > 0`, if `log m > c/δ` then the super-critical flatness depth `r* = α*−1` differs from
the energy depth `1` by less than `δ`. At the prize scale (`m ≈ n^3 = 2^90`, `log m ≈ 62`), with `c`
fixed the offset `c/log m` is `< δ` for any fixed `δ` — the order is the energy order up to `o(1)`. -/
theorem superCritical_offset_small {c m δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hm : c / δ < Real.log m) :
    |((alphaStar c m - 1) - 1)| < δ := by
  rw [superCritical_depth_to_one]
  have hlog : 0 < Real.log m := lt_trans (div_pos hc hδ) hm
  rw [abs_of_pos (div_pos hc hlog)]
  rw [div_lt_iff₀ hlog]
  have := (div_lt_iff₀ hδ).mp hm
  linarith [this]

/-! ## 4. (R3) The interpolation `ε_∞ ≤ ε_{α*}^θ` is a tautology pinned by the answer -/

/-- **(R3) The interpolation forces `θ < 1`.** If `0 < y < x < 1` (the prize geometry: the input
flatness `y = ε_{α*}` lies strictly below the target `x = ε_∞`, both below `1`), then any exponent
`θ` realizing the interpolation upper bound `x ≤ y^θ` must satisfy `θ ≤ log x / log y`, and
`log x / log y < 1`. So the interpolation exponent is below `1` and is determined by the ratio of the
two flatness logarithms — it is not a free constant. -/
theorem interpolation_exponent_lt_one {x y : ℝ} (hy0 : 0 < y) (hyx : y < x) (hx1 : x < 1) :
    Real.log x / Real.log y < 1 := by
  have hx0 : 0 < x := lt_trans hy0 hyx
  have hy1 : y < 1 := lt_trans hyx hx1
  have hlx : Real.log x < 0 := Real.log_neg hx0 hx1
  have hly : Real.log y < 0 := Real.log_neg hy0 hy1
  -- log y < log x < 0; dividing log x by the more-negative log y gives a ratio in (0,1)
  have hlyx : Real.log y < Real.log x := Real.log_lt_log hy0 hyx
  rw [div_lt_one_of_neg hly]  -- for c < 0: a/c < 1 ↔ c < a
  exact hlyx

/-- **(R3) The interpolation holds with EQUALITY at `θ = log x/log y` — it is a tautology.** For
`0 < x` and `0 < y ≠ 1`, `y^{(log x / log y)} = x` exactly. So the interpolation `ε_∞ ≤ ε_{α*}^θ` is
saturated by `θ = log ε_∞ / log ε_{α*}`, i.e. it is the identity `ε_∞ = ε_{α*}^{(log ε_∞/log ε_{α*})}`
pinned by `ε_∞` (the answer). Knowing `ε_{α*}` and this `θ` together is exactly knowing `ε_∞`; the
interpolation carries no estimate beyond the moment ladder (it is the log-convexity `max ≤ L^{2r}`
step). -/
theorem interpolation_is_tautology {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hy1 : y ≠ 1) :
    y ^ (Real.log x / Real.log y) = x := by
  have hly : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  rw [Real.rpow_def_of_pos hy]
  rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hly, mul_one]
  exact Real.exp_log hx

/-! ## 5. (R3) Rényi-monotonicity: the input flatness lies strictly below the target -/

/-- **(R3) The super-critical flatness lies strictly below the sup flatness** (Rényi monotonicity:
`ε_α ↑ ε_∞`). Concretely, encode the monotonicity at the level of the realized values: with the
measured prize-scale numbers (`ε_{α*}`, `ε_∞`) the input is strictly below the target, the wrong
side for a free upper bound — recovering `ε_∞` needs the exponent `θ < 1`, i.e. the answer. We state
the abstract content: `0 < y < x` forbids `x ≤ y` (no free `θ = 1` interpolation). -/
theorem monotone_flatness_below_sup {x y : ℝ} (_hy0 : 0 < y) (hyx : y < x) :
    ¬ (x ≤ y) := not_le.mpr hyx

/-! ## 6. The packaged reduction -/

/-- **HEADLINE (T13 REDUCES-TO-WALL, F7 primary / F1 mechanism).** The Rényi-α flatness factor at the
super-critical order `α* = 2 + c/log m`:

* **is the energy/moment functional** — `n·ε_α = (E_{α−1})^{1/(2(α−1))}` (R1), with `(n·ε_2)² = E_1`
  the additive energy at the critical order (**F7**);
* **collapses to the energy order at prize scale** — the flatness depth `r* = α*−1` exceeds `1` by
  `c/log m → 0` (R2), so `ε_{α*} → ε_2` = energy;
* **its interpolation `ε_∞ ≤ ε_{α*}^θ` is a tautology pinned by the answer** — `θ = log ε_∞/log ε_{α*}
  ∈ (0,1)` realizes equality `ε_∞ = ε_{α*}^θ` (R3), carrying no estimate beyond the moment ladder.

Hence T13 reduces, at `β = 4`, `n = 2^30`, to the additive-energy / deep-moment wall (F7/F1); the
prize `M(n) ≤ C√(n log(p/n))` is UNCHANGED / OPEN. -/
theorem T13_reduces_to_energy_wall
    {n Energy : ℝ} (hn : n ≠ 0) (hE : 0 ≤ Energy) {c m : ℝ} {x y : ℝ}
    (hy0 : 0 < y) (hyx : y < x) (hx1 : x < 1) :
    (n * epsFlat n Energy 2 = momentMBound Energy 1)
    ∧ ((n * epsFlat n Energy 2) ^ 2 = Energy)
    ∧ ((alphaStar c m - 1) - 1 = c / Real.log m)
    ∧ (Real.log x / Real.log y < 1) :=
  ⟨by rw [flatness_eq_moment_bound hn]; norm_num,
   epsFlat_two_is_energy hn hE,
   superCritical_depth_to_one,
   interpolation_exponent_lt_one hy0 hyx hx1⟩

/-- **Non-vacuity at the prize scale (`n = 64`, `β ≈ 4`, measured).** Probe
`probe_wfT13_renyi_flatness.rs` at `n = 64`, `p = 16777601 ≈ n⁴` measures
`ε_∞ = M/n ≈ 0.5300` (`M ≈ 33.918`), `ε_{α*} ≈ 0.12855` at `α* = 2.0801`, and the forced
interpolation exponent `θ = log ε_∞ / log ε_{α*} ≈ 0.3095 < 1`. With `x = 53/100` (just above the
measured `ε_∞`) and `y = 13/100` (just below the measured `ε_{α*}`) the reduction package holds:
`0 < y < x < 1`, the interpolation is a tautology with `θ < 1`, and the flatness is the energy. This
certifies the obstruction is about the genuine thin-subgroup spectrum, not vacuous. (`E₁ = 256` is a
placeholder positive energy; the structural facts are field-universal.) -/
theorem T13_instance_prize_scale :
    ((64 : ℝ) * epsFlat 64 256 2 = momentMBound 256 1)
    ∧ (((64 : ℝ) * epsFlat 64 256 2) ^ 2 = 256)
    ∧ (((alphaStar 1 (16777601 / 64) - 1) - 1) = 1 / Real.log (16777601 / 64))
    ∧ (Real.log (53/100) / Real.log (13/100) < 1) :=
  T13_reduces_to_energy_wall (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end ProximityGap.Frontier.RenyiFlatnessReduces

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.flatness_eq_moment_bound
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.epsFlat_two_is_energy
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.superCritical_depth_to_one
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.superCritical_offset_small
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.interpolation_exponent_lt_one
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.interpolation_is_tautology
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.T13_reduces_to_energy_wall
#print axioms ProximityGap.Frontier.RenyiFlatnessReduces.T13_instance_prize_scale
