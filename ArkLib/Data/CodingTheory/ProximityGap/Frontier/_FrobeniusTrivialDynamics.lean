/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# FRONTIER — Frobenius-triviality of the Gauss-sum exponent dynamics (#444)

**Fresh-swing angle (c), REFUTED at the structural root.**  The campaign asked whether an
entropy / transfer-operator bound for the "Gauss-sum dynamics `t ↦ p·t`" (the Frobenius orbit on
the exponent group `ℤ/m`) could contract the depth-`r` moment `ρ_r(u)` and so prove Paley at
`β = 4`.  The deterministic sequence is `u_t = G(ψ^t)/√p ∈ S¹`, `t ∈ ℤ/m`, `m = (p−1)/n`, and the
only algebraic relation among the Gauss sums `G(ψ^t)` for varying `t` is the **Frobenius /
Hasse–Davenport** relation, which permutes the exponents by `t ↦ p·t (mod m)`.

**The structural obstruction (this file).**  In this problem `p − 1 = n·m` *by definition of* `m`
(`m = (p−1)/n`, the order of `H^⊥ = {χ : χ|_{μ_n} = 𝟙}`), hence
                           `p = n·m + 1  ⟹  p ≡ 1  (mod m).`
Therefore the Frobenius map `t ↦ p·t` on `ℤ/m` is the **identity**: `(p : ZMod m) = 1`, so
`(p : ZMod m) • t = t` for every `t`.  Every exponent is a fixed point; the Frobenius orbit of each
`t` is the singleton `{t}`; the system has `m` fixed points and **zero topological entropy**.
There is no expanding/contracting transfer operator, no mixing — nothing for a
thermodynamic-formalism / Ruelle–Perron–Frobenius bound to act on.  Angle (c) **cannot** contract
`ρ_r`: it is the identity dynamics.

This is the dynamical face of the already-established **`√p`-vacuity / abelian-monodromy** prong:
the Galois group acts on each individual `G(ψ^t)` only by a phase `ψ^t(c)` (a Stickelberger root of
unity), and the cross-exponent dynamics is trivial because `p ≡ 1 (mod m)`.  No new contraction
exists.

`closesPrize = false`.  Rigorous **no-go** for the entropy/transfer-operator angle, not a step
toward the bound.  Verified numerically (`p mod m = 1` for `n = 16,32,64,128,256` at `β = 4`).

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.FrobTriv

/-- **The defining arithmetic of the dual setup**: with `p = n·m + 1` (which is exactly
`p − 1 = n·m`, the definition of `m = (p−1)/n` for the order-`m` subgroup `H^⊥`), the Frobenius
multiplier `p` reduces to `1` in `ZMod m`.  This is the algebraic fact that trivialises the
Frobenius dynamics `t ↦ p·t`. -/
theorem frobenius_multiplier_eq_one (n m : ℕ) (p : ℕ) (hp : p = n * m + 1) :
    (p : ZMod m) = 1 := by
  subst hp
  push_cast
  simp

/-- **Frobenius acts as the IDENTITY on the exponent group `ZMod m`.**  Since the multiplier
`(p : ZMod m) = 1`, the dynamical map `t ↦ p·t` is `t ↦ t`: every `t ∈ ZMod m` is a fixed point.
Hence the Gauss-sum Frobenius dynamics on exponents has trivial orbits (singletons) and zero
entropy — the entropy/transfer-operator angle (c) has nothing to contract. -/
theorem frobenius_is_identity (n m : ℕ) (p : ℕ) (hp : p = n * m + 1) (t : ZMod m) :
    (p : ZMod m) * t = t := by
  rw [frobenius_multiplier_eq_one n m p hp, one_mul]

/-- **Every exponent is a Frobenius fixed point** (restatement: zero entropy / trivial orbits).
The set of fixed points of `t ↦ p·t` is all of `ZMod m`. -/
theorem all_fixed (n m : ℕ) (p : ℕ) (hp : p = n * m + 1) :
    ∀ t : ZMod m, (p : ZMod m) * t = t :=
  fun t => frobenius_is_identity n m p hp t

end ArkLib.ProximityGap.Frontier.FrobTriv

/-! ## Axiom audit (run via `lake env lean`) -/
#print axioms ArkLib.ProximityGap.Frontier.FrobTriv.frobenius_multiplier_eq_one
#print axioms ArkLib.ProximityGap.Frontier.FrobTriv.frobenius_is_identity
#print axioms ArkLib.ProximityGap.Frontier.FrobTriv.all_fixed
