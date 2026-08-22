/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FarLineProxyBelowJohnson

/-!
# Exact far-line PROXY tower at `rho = 1/4` (#444; the `n/2-1` Plotkin/antipodal closed form)

This file pins the EXACT values of the **closed-form far-line PROXY**
`farLineProxy n (1/4) = 1/2 + 1/n` on the tower `n = 16, 20, 24, 32`. **READ THE SCOPE NOTE: this
proxy is NOT a measurement of the worst-direction binder; it is the antipodal/Plotkin closed-form
ansatz `s* = n/2 - 1`, and it OVER-predicts the true binder on the 2-power tower.**

## ⚠️ Correction (audit §A0/§D, `docs/kb/deltastar-444-audit-corrections-2026-06-16.md`)

An earlier docstring of this file labelled `farLineProxy 32 = 17/32` (`m* = 7`) as "THE corrected
full-direction measurement" and the value `19/32` (`m* = 5`) as an "engine direction-cap (`b < s`)
ARTIFACT". **That framing is BACKWARDS and is RETRACTED** (audit §A0, "THE BIG ONE", and §D):

* `farLineProxy n (1/4) = 1/2 + 1/n`, with `s* = n/2 - 1`, `m* = n/4 - 1`, is the **antipodal /
  Plotkin PROXY closed form** — an *extrapolated ansatz*, NOT a measurement at `n = 32`.
* the **worst-direction cascade** (exhaustive `orbcount`, GPU `rho4.out` `[4096, 89, 89, 9]`) MEASURES
  `s* = 13`, `m* = s* - k = 5`, `delta* = 19/32 ~ 0.594` at `n = 32` — a **2-adic DIP below** the
  `n/4 - 1` proxy line. This is the value encoded in-tree as
  `CrossingDepthLinearTracking.cStarFull 32 = 5`, proven a dip by
  `CrossingDepthLinearTracking.pow2_values_are_dip_below_line` (`cStarFull 32 < 32/4 - 1 = 7`).
* the "`19/32` is a `b < s` cap artifact, the correct value is `7`" claim was WRONG: `rho4.out`
  binds at an in-search direction `(20,8)`, and full-direction `orbcount` REPRODUCES `0.594`.

So `m* = 7 / delta* = 17/32` is the **PROXY closed form** (`n/2 - 1` Plotkin), correct as an
*identity for `farLineProxy`* but NOT the measured binder; the **measured worst-direction binder at
`n = 32` is `m* = 5`**, a dip below the line. The `n/4 - 1` LINEAR law is exact ONLY on the
off-tower mid-range `{16, 20, 24, 28}` (`cStar_eq_linear_midrange`); on the prize 2-power tower it
OVER-predicts.

## The theorems (extending `FarLineProxyBelowJohnson.farLineProxy`)

At `rho = 1/4` the in-tree closed-form proxy is `farLineProxy n (1/4) = 1/2 + 1/n`. This file pins
its EXACT rational values on the tower `n = 16, 20, 24, 32` (these are theorems ABOUT the
`farLineProxy` ansatz, all true) and records the discrepancy `17/32` (proxy) vs `19/32` (the
measured `n = 32` worst-direction value). The theorem statements are correct as identities for the
proxy; the docstrings now state which is the PROXY (`m* = 7`) and which is the MEASURED binder
(`m* = 5`). This neither closes nor moves the BGK/Paley CORE wall `M(mu_n) <= C sqrt(n log(p/n))`;
it is a correction brick (rule 4) that fixes the backwards "artifact" labelling.
-/

namespace ArkLib.ProximityGap.Frontier.FarLineProxyTowerN32

open ProximityGap.Frontier.FarLineProxyBelowJohnson

/-- The prize line `rho = 1/4`. -/
noncomputable def rho : ℝ := 1 / 4

/-! ### `farLineProxy n (1/4) = 1/2 + 1/n` on the full-direction-VERIFIED tower -/

/-- At `rho = 1/4` the proxy collapses to `1/2 + 1/n` (since `1/(2 rho) - 1 = 2 - 1 = 1`). -/
theorem proxy_quarter (n : ℝ) (hn : n ≠ 0) :
    farLineProxy n rho = 1 / 2 + 1 / n := by
  unfold farLineProxy rho
  field_simp
  ring

/-- `farLineProxy 16 (1/4) = 9/16` (full-direction VERIFIED anchor). -/
theorem proxy_n16 : farLineProxy 16 rho = 9 / 16 := by
  rw [proxy_quarter 16 (by norm_num)]; norm_num

/-- `farLineProxy 20 (1/4) = 11/20` (full-direction VERIFIED anchor). -/
theorem proxy_n20 : farLineProxy 20 rho = 11 / 20 := by
  rw [proxy_quarter 20 (by norm_num)]; norm_num

/-- `farLineProxy 24 (1/4) = 13/24` (full-direction VERIFIED anchor). -/
theorem proxy_n24 : farLineProxy 24 rho = 13 / 24 := by
  rw [proxy_quarter 24 (by norm_num)]; norm_num

/-- **The PROXY `n = 32` value: `farLineProxy 32 (1/4) = 17/32`** (`m* = n/4 - 1 = 7`, the
    antipodal/Plotkin closed form). This is the EXTRAPOLATED `n/2 - 1` ansatz, NOT the measured
    binder: the worst-direction cascade MEASURES `19/32` (`m* = 5`) at `n = 32`
    (`CrossingDepthLinearTracking.cStarFull 32 = 5`). -/
theorem proxy_n32 : farLineProxy 32 rho = 17 / 32 := by
  rw [proxy_quarter 32 (by norm_num)]; norm_num

/-! ### The proxy `17/32` differs from the MEASURED worst-direction value `19/32` -/

/-- The measured `n = 32` worst-direction value `19/32` (`= 0.594`, `m* = 5`, GPU `rho4.out`
    `[4096,89,89,9]`, in-tree `cStarFull 32 = 5`) is NOT the closed-form proxy value `17/32`: the
    Plotkin proxy `m* = n/4 - 1 = 7` OVER-predicts the 2-adic-dip binder `m* = 5`. -/
theorem proxy_ne_measured : farLineProxy 32 rho ≠ 19 / 32 := by
  rw [proxy_n32]; norm_num

/-- The exact discrepancy between the PROXY value `17/32` and the MEASURED worst-direction value
    `19/32` at `n = 32`: `1/16` (the proxy `m* = 7` over-predicts the measured `m* = 5` by 2 rungs). -/
theorem proxy_measured_gap : (19 / 32 : ℝ) - farLineProxy 32 rho = 1 / 16 := by
  rw [proxy_n32]; norm_num

/-! ### The PROXY radius `m* = n/4 - 1` (exact on the mid-range, OVER-predicts on the 2-power tower)

`m*_proxy(n) = n/4 - 1` is the antipodal/Plotkin closed form (`s* = n/2 - 1`). It is exact ONLY on
the off-tower mid-range `{16, 20, 24, 28}` (`CrossingDepthLinearTracking.cStar_eq_linear_midrange`);
on the prize 2-power tower it OVER-predicts the MEASURED worst-direction binder, which DIPS below it
(`CrossingDepthLinearTracking.pow2_values_are_dip_below_line`: `cStarFull 32 = 5 < 7 = 32/4 - 1`). -/

/-- The PROXY (antipodal/Plotkin) radius `m*_proxy(n) = n/4 - 1`, evaluated at the tower points. At
    `n = 32` this proxy value is `7`; the MEASURED worst-direction binder is `m* = 5` (a 2-adic dip,
    `cStarFull 32 = 5`), so `7` here is the proxy ansatz, NOT the measurement. -/
def mStarProxy : ℕ → ℕ
  | 16 => 3
  | 20 => 4
  | 24 => 5
  | 32 => 7
  | _  => 0

/-- `m*_proxy` equals `n/4 - 1` on the tower (the LINEAR Plotkin-proxy ansatz). -/
theorem mStarProxy_linear :
    mStarProxy 16 = 16 / 4 - 1 ∧ mStarProxy 20 = 20 / 4 - 1 ∧
    mStarProxy 24 = 24 / 4 - 1 ∧ mStarProxy 32 = 32 / 4 - 1 := by decide

/-- At `n = 32` the PROXY radius is `m*_proxy = 7` (`= n/4 - 1`), which is STRICTLY ABOVE the
    MEASURED worst-direction binder `m* = 5` (`cStarFull 32 = 5`): the Plotkin proxy over-predicts
    by 2 rungs on the 2-power tower. -/
theorem mStarProxy_n32_over_predicts : mStarProxy 32 = 7 ∧ (5 : ℕ) < mStarProxy 32 := by decide

/-! ### Above Johnson (rho = 1/4): proxy `> 1/2 = Johnson`, the standard Plotkin lock -/

/-- The `n = 32` proxy is ABOVE `1/2` (`= Johnson` at `rho = 1/4`); the prize floor
    (`>= Johnson`) is the SEPARATE, harder MCA object. -/
theorem proxy_n32_above_half : (1 : ℝ) / 2 < farLineProxy 32 rho := by
  rw [proxy_n32]; norm_num

/-- **HEADLINE (corrected: PROXY tower vs MEASURED binder).** The far-line PROXY closed form
    `farLineProxy n (1/4) = 1/2 + 1/n` evaluates to `9/16, 11/20, 13/24` at `n = 16, 20, 24` and to
    `17/32` at `n = 32`. At `n = 32` this proxy value `17/32` (`m*_proxy = 7`) DIFFERS from the
    MEASURED worst-direction binder `19/32` (`m* = 5`, in-tree `cStarFull 32 = 5`) by exactly
    `1/16`: the Plotkin proxy `m*_proxy = n/4 - 1` OVER-predicts the 2-adic-dip binder by 2 rungs.
    (This corrects the earlier backwards labelling that called `17/32` "the measurement" and `19/32`
    "an artifact".) The proxy sits above Johnson `1/2`. -/
theorem proxy_tower_vs_measured :
    -- the proxy closed-form tower
    farLineProxy 16 rho = 9 / 16 ∧ farLineProxy 20 rho = 11 / 20 ∧
    farLineProxy 24 rho = 13 / 24 ∧
    -- proxy value at n = 32 differs from the MEASURED worst-direction value 19/32
    farLineProxy 32 rho = 17 / 32 ∧ farLineProxy 32 rho ≠ 19 / 32 ∧
    -- proxy radius m*_proxy = n/4 - 1, STRICTLY ABOVE the measured binder m* = 5
    mStarProxy 32 = 32 / 4 - 1 ∧ (5 : ℕ) < mStarProxy 32 ∧
    -- above Johnson
    (1 : ℝ) / 2 < farLineProxy 32 rho := by
  refine ⟨proxy_n16, proxy_n20, proxy_n24, proxy_n32, proxy_ne_measured, ?_, ?_,
    proxy_n32_above_half⟩
  · decide
  · decide

end ArkLib.ProximityGap.Frontier.FarLineProxyTowerN32
