/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# The largest concrete Garcia–Voloch instance: `μ_18 ⊆ F_379` (#389)

Extends the concrete residual-free sequence to order 18 — a six-order jump over the prior
in-tree maximum (`μ_12`/`μ_14`).  `μ_18 ⊆ F_379` (the 18th roots of unity) is exactly
Sidon-modulo-negation: additive energy `E = 918 = 3·18² − 3·18`, so `energyExcess = 0` and the
`C = 0` branch of `gvRepBound_of_energyExcess_quadratic` fires:

> **`mu18_F379_gvRepBound`** — `GVRepBound (μ_18 ⊆ F_379) 8`: every nonzero `t` has at most `8`
> additive representations (`(3+0)·18 = 54 ≤ 8² = 64`, `8³ = 512 ≤ 64·18² = 20736`).

The full concrete sequence is now `μ_4: 0, μ_6: 0, μ_8: 32, μ_10: 120 (F_31) / 0 (F_101),
μ_12: 288, μ_14: 168, μ_18: 0` — spanning orders 4 through 18.  Every hypothesis (including the
energy `E = 918`, a sum of `18⁴` indicator terms over `F_379`) is discharged by `decide` (8M
heartbeats, ~26 s); axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime379FactMu18 : Fact (Nat.Prime 379) := ⟨by norm_num⟩

/-- `μ_18 ⊆ F_379`, the 18th roots of unity. -/
def mu18_F379 : Finset (ZMod 379) :=
  {1, 40, 51, 52, 84, 115, 145, 180, 185, 194, 199, 234, 264, 295, 327, 328, 339, 378}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- **Residual-free Garcia–Voloch bound for `μ_18 ⊆ F_379`** (exactly Sidon, `C = 0`).  `μ_18` has
`E = 918 = 3·18²−3·18`, `energyExcess = 0`, so the `C = 0` branch yields `GVRepBound (μ_18) 8`. -/
theorem mu18_F379_gvRepBound : GVRepBound mu18_F379 8 :=
  gvRepBound_of_energyExcess_quadratic (G := mu18_F379) (n := 18) (C := 0) (M := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
