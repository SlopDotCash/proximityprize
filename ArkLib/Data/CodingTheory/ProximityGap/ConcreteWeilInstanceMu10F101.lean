/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# Field-dependence of the Garcia–Voloch excess: `μ_10 ⊆ F_101` (#389)

A companion to `ConcreteWeilInstanceMu10` (`μ_10 ⊆ F_31`, excess `120`, `C = 2`) at the **same
order** but a different field, exhibiting that the Garcia–Voloch energy excess is genuinely
*field-dependent*: `μ_10 ⊆ F_101` (the 10th roots of unity, with `6` a primitive 10th root) is
**exactly Sidon-modulo-negation** — additive energy `E = 270 = 3·10² − 3·10`, so `energyExcess = 0`
and the `C = 0` branch fires with no residual:

> **`mu10_F101_gvRepBound`** — `GVRepBound (μ_10 ⊆ F_101) 6`: every nonzero `t` has at most `6`
> additive representations (`(3+0)·10 = 30 ≤ 6² = 36`, `6³ = 216 ≤ 64·10² = 6400`).

So at order 10 the excess drops from `120` (over `F_31`) to `0` (over `F_101`): the larger field is
"more generic", matching the `n²/p → 0` Sidon-modulo-negation prediction (`100/101 ≈ 1` vs `100/31`).
Every hypothesis (including the energy `E = 270`) is discharged by `decide`; axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime101FactMu10 : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- `μ_10 ⊆ F_101`, the 10th roots of unity `{1, 6, 14, 17, 36, 65, 84, 87, 95, 100}`
(`6` is a primitive 10th root). -/
def mu10_F101 : Finset (ZMod 101) := {1, 6, 14, 17, 36, 65, 84, 87, 95, 100}

set_option maxRecDepth 1000000 in
/-- **Residual-free Garcia–Voloch bound for `μ_10 ⊆ F_101`** (exactly Sidon, `C = 0`).  `μ_10` has
`E = 270 = 3·10²−3·10`, `energyExcess = 0`, so the `C = 0` branch yields `GVRepBound (μ_10) 6` —
contrast `μ_10 ⊆ F_31` (excess `120`, `C = 2`). -/
theorem mu10_F101_gvRepBound : GVRepBound mu10_F101 6 :=
  gvRepBound_of_energyExcess_quadratic (G := mu10_F101) (n := 10) (C := 0) (M := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
