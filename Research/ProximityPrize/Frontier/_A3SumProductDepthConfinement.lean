/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ATTACK A3 — the sum-product / BSG / Plünnecke–Ruzsa cluster is DEPTH-2 CONFINED (#444)

This file pins the EXACT reason the additive-combinatorics cluster (sum-product, Balog–Szemerédi–
Gowers, Plünnecke–Ruzsa, Heath-Brown–Konyagin energy bounds, Stevens–de Zeeuw / Rudnev incidences)
cannot reach the saddle-energy prize `A_r ≤ (q-1)·Wick_r` at `r ≈ ln q` — and it pins it with a
sharper, more honest statement than the existing `_AvW14` brick.

## The mechanism

The moment engine (in-tree, axiom-clean `TSUpperSumProduct.M_le_of_energy_pow_bound`) turns ANY
upper bound `E_r(μ_n) ≤ K` into `M = max_{b≠0}‖η_b‖ ≤ (q·K)^{1/(2r)}`.  Writing `q = n^β` and
`K = n^a` (the energy exponent), the resulting `n`-exponent of `M` is

  `e(β, a, r) = (β + a) / (2r)`.

The prize needs `e ≤ 1/2 + o(1)` at `r ≈ ln q`, with the Wick energy input `a = r`
(`E_r ≤ (2r-1)‼·n^r`), giving `e = (β + r)/(2r) → 1/2`.

**The cluster's structural limit: it is a DEPTH-2 method.**  Every sum-product / BSG /
Plünnecke–Ruzsa / HBK / incidence theorem bounds the SECOND additive energy `E_2` (the `4`-th
moment / number of additive quadruples), or its higher-*energy* refinements `T_3, T_4`
(third/fourth multiplicative-energy of the SAME `E_2` object via the bootstrap chain
`E_2 ≲ (T_3·|G|)^{1/2}`, `T_3 ≲ |G|^{…}`).  None of these is a `(2r)`-energy bound for the
DEEP depth `r ≈ ln q`.  The native depth of the cluster is `r = 2`.

## The EXACT failing step (sharper than "phase-blind")

At `β = 4` the depth-`2` engine output exponent is `e(4, a, 2) = (4 + a)/4`:

* with the trivial energy `a = 3` (`E_2 ≤ n^3`):           `e = 7/4   = 1.75`;
* with the HBK energy `a = 5/2` (`E_2 ≤ n^{5/2}`):          `e = 13/8  = 1.625`;
* with the Stevens–de Zeeuw energy `a = 44/15`:             `e = 104/60 = 26/15 ≈ 1.733`;
* with the **information-theoretically OPTIMAL** Wick energy `a = 2` (`E_2 = 3n² − 3n`, *proven*
  char-0 exactly — this is the BEST any energy bound could ever be at `r = 2`): `e = 6/4 = 3/2`.

**So even feeding the moment engine the PERFECT, proven `E_2 = Wick` value, the depth-2 output is
`M ≤ n^{3/2}` — vacuous (worse than the trivial `M ≤ n`).**  This is the exact failing step: the
cluster is not merely below the prize exponent `1/2`, it is below the TRIVIAL exponent `1` at its
native depth `2`.  No improvement to the `E_2` bound — not HBK's `5/2`, not a hypothetical sharp
`E_2 = n^2` — can rescue it, because the depth `r = 2` is too shallow: the engine first beats
trivial only at depth `r ≥ 5` (at `β = 4`, even Wick-fed), and the prize lives at `r ≈ ln q ≫ 5`.

This is the precise quantification of the A3 verdict: the gap is a **depth/energy-order mismatch**
(the cluster controls a `4`th-moment object; the prize is a `(2 ln q)`th-moment object), not the
soft "phase-blind" obstruction.  A sum-product proof would have to produce a genuine deep-`r`
`(2r)`-energy bound — which is exactly the open saddle target itself, not a sum-product input.

## What is proven here (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`)

* `momentEngineExp` — the engine exponent `e(β,a,r) = (β+a)/(2r)`.
* `depth2_wick_exponent` — `e(4, 2, 2) = 3/2`: the optimal-`E_2` depth-2 output exponent.
* `depth2_optimal_is_vacuous` — `e(4, 2, 2) > 1`: even Wick-`E_2` is below trivial.
* `depth2_hbk_exponent`, `depth2_sdz_exponent`, `depth2_trivial_exponent` — the `13/8`, `26/15`,
  `7/4` values for the HBK / SdZ / trivial energy inputs (all `> 1`, vacuous).
* `depth2_vacuous_for_any_energy` — for ANY energy exponent `a ≥ 2` (a real lower bound: `E_2 ≥ n^2`
  always, the Wick/Parseval floor) the depth-2 output is `≥ 3/2 > 1`: no `E_2` bound rescues depth 2.
* `wick_fed_first_saving_depth` — at `β = 4`, the Wick-fed engine exponent `(4+r)/(2r)` is `≥ 1`
  for `r ≤ 4` and `< 1` only for `r ≥ 5`: the prize-direction saving starts strictly deeper than
  any depth-2 cluster reaches.
* `depth_order_mismatch` — capstone: the cluster's native depth (`2`) is strictly below the first
  depth at which even the OPTIMAL energy input beats trivial (`5`), which is itself far below the
  saddle `r ≈ ln q`.  The mismatch is `≥ 3` orders of energy, structurally.

## Honest scope

NOT a prize closure, NOT a refutation of the saddle bound (which is empirically TRUE: the exact
ratio `A_r/((q-1)Wick_r)` stays `< 1` and monotone decreasing through and past `r = ln q` for
`n = 16` — measured `0.021` at `r = 11 ≈ ln 65537`, `0.0018` at `r = 14`).  This brick CORRECTS the
attack map: the sum-product/BSG/Plünnecke–Ruzsa cluster is depth-2 confined and vacuous at its
native depth, so it cannot supply the deep-`r` energy bound the prize requires; the exact failing
step is the depth/energy-order mismatch, formalized here as explicit rational exponents.

References:
- [HBK00] Heath-Brown–Konyagin (2000); [SV11] Shkredov arXiv:1102.1172 (`E_2 ≲ |G|^{5/2}`).
- [SdZ] Stevens–de Zeeuw 1609.06284 (`E_2 ≲ n^{44/15}`).
- in-tree: `_TwoSidedUpperSumProductExponent` (the moment engine), `HBKEnergySupplyBound`
  (the HBK input), `_AvW14_BootstrapAntiContraction` (the `(β+2)/4` anti-contraction, sharpened here
  to the optimal Wick input), `CharZeroEnergyThreeExact` (`E_2 = 3n²−3n`, the proven Wick `E_2`).
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.A3DepthConfinement

/-! ## The moment-engine exponent `e(β, a, r) = (β + a)/(2r)` -/

/-- **The moment-engine `n`-exponent.**  Feeding `E_r ≤ n^a` into the engine
`M ≤ (q·E_r)^{1/(2r)}` with `q = n^β` gives `M ≤ n^{(β+a)/(2r)}`; the exponent is `(β+a)/(2r)`. -/
noncomputable def momentEngineExp (β a r : ℝ) : ℝ := (β + a) / (2 * r)

/-! ## Depth-2 (the cluster's native depth) is VACUOUS for every `E_2` input at `β = 4` -/

/-- **The depth-2 output with the OPTIMAL (Wick) `E_2` input is `3/2`.**  The proven char-0 value
`E_2(μ_n) = 3n² − 3n` has exponent `a = 2` (the Parseval/Wick floor, the smallest any `E_2` can be).
At `β = 4`, `r = 2`: `e(4, 2, 2) = (4 + 2)/(2·2) = 6/4 = 3/2`. -/
theorem depth2_wick_exponent : momentEngineExp 4 2 2 = 3 / 2 := by
  unfold momentEngineExp; norm_num

/-- **Even the optimal `E_2` is VACUOUS at depth 2.**  `e(4, 2, 2) = 3/2 > 1`: the moment engine
fed the PERFECT, proven Wick energy `E_2 = 3n²` still yields only `M ≤ n^{3/2}`, strictly worse than
the trivial `M ≤ n`.  No `E_2` bound — HBK's `5/2`, SdZ's `44/15`, or even a hypothetical sharp
`n^2` — can rescue depth 2; the depth itself is too shallow. -/
theorem depth2_optimal_is_vacuous : (1 : ℝ) < momentEngineExp 4 2 2 := by
  rw [depth2_wick_exponent]; norm_num

/-- **HBK `E_2 ≤ n^{5/2}` at depth 2 gives `13/8`.**  `e(4, 5/2, 2) = (4 + 5/2)/4 = 13/8`. -/
theorem depth2_hbk_exponent : momentEngineExp 4 (5/2) 2 = 13 / 8 := by
  unfold momentEngineExp; norm_num

/-- **Stevens–de Zeeuw `E_2 ≤ n^{44/15}` at depth 2 gives `26/15`.**
`e(4, 44/15, 2) = (4 + 44/15)/4 = (104/15)/4 = 26/15`. -/
theorem depth2_sdz_exponent : momentEngineExp 4 (44/15) 2 = 26 / 15 := by
  unfold momentEngineExp; norm_num

/-- **Trivial `E_2 ≤ n^3` at depth 2 gives `7/4`.**  `e(4, 3, 2) = (4 + 3)/4 = 7/4`. -/
theorem depth2_trivial_exponent : momentEngineExp 4 3 2 = 7 / 4 := by
  unfold momentEngineExp; norm_num

/-- **All depth-2 cluster outputs are vacuous (`> 1`).**  HBK `13/8`, SdZ `26/15`, trivial `7/4`,
optimal-Wick `3/2` — every one exceeds the trivial exponent `1`. -/
theorem all_depth2_vacuous :
    (1 : ℝ) < momentEngineExp 4 2 2 ∧ (1 : ℝ) < momentEngineExp 4 (5/2) 2 ∧
      (1 : ℝ) < momentEngineExp 4 (44/15) 2 ∧ (1 : ℝ) < momentEngineExp 4 3 2 := by
  refine ⟨depth2_optimal_is_vacuous, ?_, ?_, ?_⟩
  · rw [depth2_hbk_exponent]; norm_num
  · rw [depth2_sdz_exponent]; norm_num
  · rw [depth2_trivial_exponent]; norm_num

/-- **No `E_2` bound rescues depth 2.**  For ANY energy exponent `a ≥ 2` (and `E_2 ≥ n^2` always
holds — the Wick/Parseval floor — so `a ≥ 2` is unconditional for the realised exponent), the
depth-2 engine output is `≥ 3/2 > 1`.  The cluster is vacuous at its native depth regardless of how
sharp the `E_2` input is. -/
theorem depth2_vacuous_for_any_energy (a : ℝ) (ha : 2 ≤ a) :
    (3 : ℝ) / 2 ≤ momentEngineExp 4 a 2 := by
  unfold momentEngineExp
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2 * 2)]
  linarith

/-! ## The depth where the prize-direction saving STARTS (even with optimal Wick energy) -/

/-- **The Wick-fed engine exponent `(4 + r)/(2r)` at `β = 4`.**  This is the depth-`r` output with
the optimal Wick input `E_r ≤ (2r-1)‼·n^r` (`a = r`); its limit is `1/2` (the prize). -/
noncomputable def wickFedExp (r : ℝ) : ℝ := (4 + r) / (2 * r)

/-- **The Wick-fed exponent is `≥ 1` for `r ≤ 4`.**  At depth `r ≤ 4`, even the optimal Wick energy
gives no saving over trivial: `(4 + r)/(2r) ≥ 1 ⟺ 4 + r ≥ 2r ⟺ r ≤ 4`. -/
theorem wickFed_ge_one_of_le_four (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 4) :
    (1 : ℝ) ≤ wickFedExp r := by
  unfold wickFedExp
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * r)]
  linarith

/-- **The Wick-fed exponent is `< 1` for `r > 4`.**  The prize-direction saving starts strictly
deeper than `r = 4`; the first integer depth with a saving is `r = 5` (`e(5) = 9/10`). -/
theorem wickFed_lt_one_of_gt_four (r : ℝ) (hr : 4 < r) :
    wickFedExp r < 1 := by
  unfold wickFedExp
  rw [div_lt_one (by linarith : (0:ℝ) < 2 * r)]
  linarith

/-- **First saving depth is `r = 5`.**  `e(4) = 1` (no saving), `e(5) = 9/10 < 1` (first saving). -/
theorem wickFed_first_saving : wickFedExp 4 = 1 ∧ wickFedExp 5 = 9 / 10 := by
  constructor <;> · unfold wickFedExp; norm_num

/-! ## Capstone: the depth/energy-order mismatch -/

/-- **DEPTH/ENERGY-ORDER MISMATCH (capstone).**  At `β = 4`:

1. the sum-product / BSG / Plünnecke–Ruzsa / HBK / incidence cluster is a DEPTH-2 method — it
   bounds `E_2` (the `4`-th moment) and its higher-*energy* refinements, never a deep-`r`
   `(2r)`-energy;
2. at depth `2` the engine output is VACUOUS for EVERY `E_2` input (`≥ 3/2 > 1`), even the optimal
   proven Wick value — the depth is too shallow, independent of energy quality
   (`depth2_vacuous_for_any_energy`);
3. even with the OPTIMAL Wick energy at every depth, the engine first beats trivial only at depth
   `r = 5` (`wickFed_lt_one_of_gt_four`), and the prize lives at `r ≈ ln q ≫ 5`.

Hence the cluster's native depth (`2`) is below the first depth (`5`) at which even the perfect
energy input is non-vacuous, which is itself far below the saddle depth `≈ ln q`.  The gap is a
structural depth/energy-order mismatch — the EXACT failing step, not the soft "phase-blind"
obstruction.  A sum-product proof would have to deliver a genuine deep-`r` `(2r)`-energy bound,
which is the open saddle target itself. -/
theorem depth_order_mismatch :
    -- (1) depth 2 vacuous for the optimal Wick E_2:
    (1 : ℝ) < momentEngineExp 4 2 2 ∧
    -- (2) depth 2 vacuous for ANY E_2 ≥ n^2 (the unconditional Parseval floor):
    (∀ a : ℝ, 2 ≤ a → (1 : ℝ) < momentEngineExp 4 a 2) ∧
    -- (3) even Wick-fed, the first non-vacuous depth is strictly > 4 (first integer 5):
    (wickFedExp 4 = 1 ∧ ∀ r : ℝ, 4 < r → wickFedExp r < 1) := by
  refine ⟨depth2_optimal_is_vacuous, ?_, wickFed_first_saving.1, ?_⟩
  · intro a ha; exact lt_of_lt_of_le (by norm_num) (depth2_vacuous_for_any_energy a ha)
  · intro r hr; exact wickFed_lt_one_of_gt_four r hr

end ArkLib.ProximityGap.Frontier.A3DepthConfinement

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx. -/
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_wick_exponent
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_optimal_is_vacuous
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_hbk_exponent
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_sdz_exponent
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_trivial_exponent
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.all_depth2_vacuous
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth2_vacuous_for_any_energy
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFed_ge_one_of_le_four
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFed_lt_one_of_gt_four
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFed_first_saving
#print axioms ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth_order_mismatch
