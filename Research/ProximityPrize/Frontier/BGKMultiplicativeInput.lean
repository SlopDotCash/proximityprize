/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCurve
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# The BGK multiplicative input: `μ_n` has multiplicative doubling `σₘ[μ_n] = 1` (#389)

**Scouting brick for the BGK 2006 power-saving route.** The Bourgain–Glibichuk–Konyagin
character-sum bound for a multiplicative subgroup `H ≤ 𝔽_p^*` is driven by the *sum–product
phenomenon*: a subgroup has **perfect multiplicative structure** (multiplicative doubling
`σₘ[H] = 1`, i.e. `H·H = H`), and sum–product forces this to be incompatible with large
*additive* structure (large additive energy / small sumset). The contradiction yields the
power saving `max_{b≠0}‖η_b‖ ≤ n^{1−c}`.

This file lands the **multiplicative input** — the trivial-but-load-bearing half of the
dichotomy — for the in-tree smooth-domain carrier `μ_n = RepCountCurve.muN F n` (the `n`-th
roots of unity in `F`), via Mathlib's pointwise-`Finset` product (`Mathlib.Algebra.Group.
Pointwise.Finset.Basic`). It is the entry point that connects `μ_n` to the
`Combinatorics.Additive` sum–product API (`DoublingConst`, `ApproximateSubgroup`,
`PluenneckeRuzsa`) — none of which the in-tree `μ_n` work currently touches:

* `muN_mul_self_eq` : `μ_n · μ_n = μ_n` (closed under multiplication; `1 ∈ μ_n`).
* `card_muN_mul_self_eq` : `#(μ_n · μ_n) = #μ_n` (multiplicative doubling = 1, exactly).
* `muN_doubling_eq_one` : `(#(μ_n · μ_n) : ℚ) / #μ_n = 1` — the doubling constant `σₘ[μ_n] = 1`
  written explicitly (the `Combinatorics.Additive` `Finset.mulConst` requires the ambient type
  to be a `Group`, which a field `F` is not under `*`; the in-tree carrier lives in `F`, so we
  state the constant directly).

**Honest scope.** This is the *easy* half of the BGK chain — the multiplicative side is
trivial because `μ_n` is literally a subgroup. The genuinely hard, **multi-month** half is
sum–product: deriving a contradiction from `σₘ[μ_n] = 1` together with a (hypothetical) large
additive energy `E^+(μ_n) ≫ n^{5/2}`. Mathlib has Plünnecke–Ruzsa
(`Mathlib.Combinatorics.Additive.PluenneckeRuzsa`) but **no sum–product theorem over `𝔽_p`**
(no Glibichuk–Konyagin / Bourgain–Katz–Tao estimate), which is the missing input. This brick
makes the multiplicative side machine-checked and Mathlib-interoperable so that, when a
sum–product estimate is formalized, the two halves compose.

Probe corroboration (`/tmp/bgk_probe.py`, prize-shaped `p ≈ n^4`, `n ∈ {8,16,32}`): the
multiplicative doubling `|G·G| = n` exactly (this file), while `E^+(G) ≈ 3n²` is near the
Sidon/Gaussian floor (so `|G+G| ≈ n²/3` is near-maximal) — the sum–product dichotomy holds
numerically; only its *proof* is the open core.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset
open scoped Pointwise

namespace ArkLib.ProximityGap.BGKMultiplicativeInput

open ArkLib.ProximityGap (muN)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `1 ∈ μ_n` (`1^n = 1` for every `n`). -/
theorem one_mem_muN {n : ℕ} : (1 : F) ∈ muN F n := by
  simp only [muN, mem_filter, mem_univ, true_and, one_pow]

/-- **`μ_n` is closed under multiplication**: `μ_n · μ_n = μ_n`. The `n`-th roots of unity form
a multiplicative subgroup, so the pointwise product set is `μ_n` itself. `⊆`: if `aⁿ = 1` and
`bⁿ = 1` then `(ab)ⁿ = aⁿbⁿ = 1`. `⊇`: `x = x · 1` with `1 ∈ μ_n`. -/
theorem muN_mul_self_eq {n : ℕ} :
    (muN F n) * (muN F n) = muN F n := by
  apply Finset.Subset.antisymm
  · -- μ_n · μ_n ⊆ μ_n
    intro x hx
    rw [Finset.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp only [muN, mem_filter, mem_univ, true_and] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  · -- μ_n ⊆ μ_n · μ_n  (x = x * 1)
    intro x hx
    rw [Finset.mem_mul]
    exact ⟨x, hx, 1, one_mem_muN, mul_one x⟩

/-- **Multiplicative doubling of `μ_n` is exactly 1** (`#(μ_n · μ_n) = #μ_n`). The BGK
multiplicative input: perfect multiplicative structure. -/
theorem card_muN_mul_self_eq {n : ℕ} :
    ((muN F n) * (muN F n)).card = (muN F n).card := by
  rw [muN_mul_self_eq]

/-- **The multiplicative doubling constant `σₘ[μ_n] = 1`**, stated explicitly as
`#(μ_n · μ_n) / #μ_n = 1` over `ℚ` (`μ_n` is always nonempty, since `1 ∈ μ_n`). This is the
subgroup-doubling fact — perfect multiplicative structure — that is the entry point to the
sum–product / BGK power-saving route. (`Finset.mulConst` itself needs the ambient type to be a
`Group`; a field `F` is not a multiplicative group, so we state the constant directly on the
in-tree `F`-carrier.) -/
theorem muN_doubling_eq_one {n : ℕ} :
    (((muN F n) * (muN F n)).card : ℚ) / (muN F n).card = 1 := by
  have hne : (muN F n).Nonempty := ⟨1, one_mem_muN⟩
  have hpos : 0 < (muN F n).card := Finset.card_pos.mpr hne
  rw [card_muN_mul_self_eq, div_self]
  exact_mod_cast hpos.ne'

#print axioms ArkLib.ProximityGap.BGKMultiplicativeInput.muN_mul_self_eq
#print axioms ArkLib.ProximityGap.BGKMultiplicativeInput.card_muN_mul_self_eq
#print axioms ArkLib.ProximityGap.BGKMultiplicativeInput.muN_doubling_eq_one

end ArkLib.ProximityGap.BGKMultiplicativeInput
