/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WF407_T02Shkredov — the Shkredov / bilinear additive-comb lever is regime-vacuous (FRONTIER lane)

**Thread (407-T02).** The "best lever" against the open `δ*` core is the *non-moment*
additive-combinatorial bound on the `r`-fold cross-surplus of `μ_n` — named as
Shkredov-style subgroup higher-energy (`E⁺(Γ)`, tripling constant `|3Γ| ≫ |Γ|²/log`,
Shkredov 1504.04522) and the Chang–Shparlinski / Kerr–Macourt **bilinear** double-sum
mechanism (Bourgain–Glibichuk–Konyagin 0705.4573), which the *moment* route is PROVEN
(wall W4) unable to supply.

**Verdict (this file + probes `wf407_T02-shkredov_*.py`): WALLED.** Both families collapse
onto the Gauss-period / Paley-eigenvalue wall (W2 √n-loss + W4 moment-depth), because:

1. **Density-gated (Shkredov / Heath–Brown–Konyagin).** Every nontrivial subgroup-energy
   saving needs `|Γ| > p^{1/4}` (`HBK` is vacuous below `q^{1/3}`). The prize subgroup has
   `|μ_n| = n = 2^a`, `p = n·2^128`, so `n > p^{1/4} ⟺ a > 128/3 ≈ 42.67`
   (`shkredov_density_gate`). The prize caps `a ≤ 40` (`PAPERS_NEEDED`/CLAUDE.md: `k ≤ 2^40`),
   so `n < p^{1/4}` ALWAYS (`prize_below_quarter_power`) — the hypothesis is NEVER met.
   Equivalently the density exponent `θ = log_p n = a/(a+128) ≤ 40/168 < 1/4`
   (`density_exponent_lt_quarter`).
2. **r=2/r=3-locked (probe Part 3/L2).** Shkredov bounds `E⁺ = E_2` (and at most `E_3`); the
   cross-surplus `S_r = E_r^{F_p} − E_r^{char0}` is **exactly 0 for `r < r_max = 2·log_n p`**
   and only turns on AT that ceiling — the depth no Shkredov/bilinear bound is stated at and
   the moment method provably (W4) cannot reach.
3. **Collapse (probe Part 5).** `Σ_b ‖η_b‖^{2r} = q·E_r` EXACTLY, so any cross-surplus bound is
   the moment method on the Gauss periods = the Paley Graph Conjecture (`B ≤ 2√n ⟺ Ramanujan`),
   OPEN; and the bilinear mechanism needs a second density-`p^{3/7}` variable `μ_n` lacks
   (`bilinear_factor_below_quarter`).

This file proves the **elementary regime-vacuity arithmetic** (the rigorous kernel of the
verdict): the Shkredov/HBK density hypothesis is unsatisfiable at prize parameters. It does NOT
prove the floor `B`; it certifies that the named lever is out of regime. No fabricated closure.

## References
- Shkredov, *On tripling constant of multiplicative subgroups*, arXiv:1504.04522.
- Bourgain–Glibichuk–Konyagin, *Estimates for the number of sums and products …*, 0705.4573.
- [ABF26] ePrint 2026/680 (the prize); CLAUDE.md regime spec (`k ≤ 2^40`, `q ≈ n·2^128`).
-/

namespace ArkLib.ProximityGap.WF407_T02Shkredov

open Real

/-- The prize prime law `p = n · 2^128` (dominant term of the field-size requirement). -/
noncomputable def primeOf (n : ℝ) : ℝ := n * (2 : ℝ) ^ (128 : ℝ)

/-- **Shkredov / HBK density gate.** Every nontrivial subgroup higher-energy saving (Shkredov
`E⁺`, tripling; HBK energy) requires the subgroup to be a positive power of `p` above the
quarter threshold: `|Γ| > p^{1/4}`. With `p = n·2^128`, this is exactly `log n > 128·log 2 / 3`,
i.e. `a = log₂ n > 128/3 ≈ 42.67`. -/
theorem shkredov_density_gate {n : ℝ} (hn0 : 0 < n) :
    n > primeOf n ^ ((1:ℝ)/4) ↔ Real.log n > (128 * Real.log 2) / 3 := by
  have hp : (0:ℝ) < primeOf n := by unfold primeOf; positivity
  have hlogp : Real.log (primeOf n) = Real.log n + 128 * Real.log 2 := by
    unfold primeOf
    rw [Real.log_mul (ne_of_gt hn0) (by positivity), Real.log_rpow (by norm_num)]
  rw [gt_iff_lt, ← Real.log_lt_log_iff (by positivity) hn0,
      Real.log_rpow hp, hlogp, gt_iff_lt]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The prize subgroup is below the quarter power — the gate is never met.** With `n = 2^a`
and the prize cap `a ≤ 40 < 128/3`, we have `log n = a·log 2 < (128·log 2)/3`, hence
`n ≤ p^{1/4}` (the strict gate `n > p^{1/4}` FAILS). So the Shkredov/HBK density hypothesis is
unsatisfiable at every realizable prize instance. -/
theorem prize_below_quarter_power {a : ℝ} (ha0 : 0 < a) (hcap : a ≤ 40) :
    ¬ ((2:ℝ)^a > primeOf ((2:ℝ)^a) ^ ((1:ℝ)/4)) := by
  have hn0 : (0:ℝ) < (2:ℝ)^a := by positivity
  rw [shkredov_density_gate hn0, not_lt]
  -- log (2^a) = a * log 2 ≤ 40 * log 2 < (128 log 2)/3.
  have hlog : Real.log ((2:ℝ)^a) = a * Real.log 2 := Real.log_rpow (by norm_num) a
  rw [hlog]
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc a * Real.log 2 ≤ 40 * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right hcap (le_of_lt hl2)
    _ ≤ (128 * Real.log 2) / 3 := by nlinarith [hl2]

/-- **Density exponent `θ = log_p n = a/(a+128) < 1/4` at the prize.** The subgroup density
exponent of `μ_n` is `θ = log n / log p = a/(a+128)` (base-2: `a/(a+128)`). For `a ≤ 40`,
`θ ≤ 40/168 = 5/21 < 1/4`. This is the same fact as `prize_below_quarter_power`, phrased as the
density exponent the Shkredov/bilinear literature requires to exceed `1/4`. -/
theorem density_exponent_lt_quarter {a : ℝ} (ha0 : 0 < a) (hcap : a ≤ 40) :
    Real.log ((2:ℝ)^a) / Real.log (primeOf ((2:ℝ)^a)) < (1:ℝ)/4 := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log ((2:ℝ)^a) = a * Real.log 2 := Real.log_rpow (by norm_num) a
  have hlogp : Real.log (primeOf ((2:ℝ)^a)) = (a + 128) * Real.log 2 := by
    unfold primeOf
    rw [Real.log_mul (by positivity) (by positivity), hlogn,
        Real.log_rpow (by norm_num)]
    ring
  rw [hlogn, hlogp]
  -- (a log2)/((a+128) log2) = a/(a+128) < 1/4  ⟺  4a < a+128  ⟺  3a < 128, true since a ≤ 40.
  rw [mul_div_mul_right _ _ (ne_of_gt hl2)]
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Bilinear mechanism is below the quarter power too.** The Chang–Shparlinski / Kerr–Macourt
bilinear gain needs BOTH variables to range over sets of multiplicative density `> p^{3/7}`. Any
factorization of the single thin set `μ_n` into a sumset/product `A·B` gives factors of density
`≤ θ/2 = a/(2(a+128))`. For `a ≤ 40` this is `≤ 40/336 < 1/4 < 3/7`. So even the (weaker) quarter
threshold fails for each bilinear factor; a fortiori the `3/7` bilinear threshold fails. -/
theorem bilinear_factor_below_quarter {a : ℝ} (ha0 : 0 < a) (hcap : a ≤ 40) :
    a / (2 * (a + 128)) < (1:ℝ)/4 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-
**Axiom audit.** The four theorems
(`shkredov_density_gate`, `prize_below_quarter_power`, `density_exponent_lt_quarter`,
`bilinear_factor_below_quarter`) are pure exact real-arithmetic and depend only on
`[propext, Classical.choice, Quot.sound]` — axiom-clean, no `sorry`/`admit`/`native_decide`.

**VERDICT (407-T02): WALLED.** The named "best lever" — Shkredov higher-energy / bilinear — is
out of regime at the prize: the density hypothesis `|μ_n| > p^{1/4}` (Shkredov/HBK) is
*unsatisfiable* for `a ≤ 40` (`prize_below_quarter_power`, `density_exponent_lt_quarter`), and the
bilinear `p^{3/7}` two-variable hypothesis fails even per-factor (`bilinear_factor_below_quarter`).
Combined with the probe findings — the cross-surplus `S_r` is `0` below `r_max = 2 log_n p` and
Shkredov is `r=2/r=3`-locked; `Σ_b‖η_b‖^{2r}=q·E_r` so any cross-surplus bound IS the moment
method on the Gauss periods — the lever collapses onto the Gauss-period / Paley wall
(`B ≤ 2√n ⟺ Ramanujan`, the Paley Graph Conjecture, OPEN). No closure of the floor `B`.
-/

end ArkLib.ProximityGap.WF407_T02Shkredov

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.WF407_T02Shkredov.shkredov_density_gate
#print axioms ArkLib.ProximityGap.WF407_T02Shkredov.prize_below_quarter_power
#print axioms ArkLib.ProximityGap.WF407_T02Shkredov.density_exponent_lt_quarter
#print axioms ArkLib.ProximityGap.WF407_T02Shkredov.bilinear_factor_below_quarter
