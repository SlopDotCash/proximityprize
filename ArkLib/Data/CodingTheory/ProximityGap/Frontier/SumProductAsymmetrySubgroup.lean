/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrSubgroupExact
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyCubeBound

/-!
# The sum-product ASYMMETRY of the thin subgroup: `E_×(H) = |H|³` (max) vs `E_+(H) = 3|H|²−3|H|` (min) (#444)

`PencilAutocorrSubgroupExact.subgroup_multiplicativeEnergy_eq_card_cube` proves the multiplicative
energy of a subgroup is **maximal**,
`E_×(H) = ∑_ρ |H ∩ ρ·H|² = |H|³`, and its docstring *names* — but never **welds** — the contrasting
fact that the SAME subgroup has **minimal** additive energy
`E_+(H) = 3|H|² − 3|H|` (`AdditiveEnergyBridge.addEnergy_eq_of_sidonModNeg`, the Sidon-modulo-negation
value), summarising it as "additively spread (min energy) and multiplicatively rigid (max energy) —
the sum-product extremality at the heart of why μ_n is the hard thin-set." This file carries that
contrast as actual theorems welding the two proven endpoints.

## What is welded (NON-MOMENT, sign-free, EXTEND-proven on two in-tree theorems)

For the prize object — a multiplicative subgroup `H` that is also Sidon-modulo-negation (the thin
2-power `μ_n` in the prize regime `q > n³`, where `−1 ∈ μ_n` and the only additive coincidences are
the antipodal/trivial ones):

* `multEnergy_eq_card_cube_of_subgroup` — `E_×(H) = |H|³` (restated from the pencil file as the
  named multiplicative energy `multEnergy`).
* `multEnergy_eq_max_addEnergy` — `E_×(H) = |H|³` is the **maximum** value the additive energy can
  take: `E_×(H) = |H|³ ≥ E_+(K)` for *every* `|H|`-cardinality set `K` (via `addEnergy_le_cube`). The
  subgroup's multiplicative energy sits at the top of the additive-energy range.
* `multEnergy_minus_addEnergy_of_sidonModNeg` — the **exact gap**
  `E_×(H) − E_+(H) = |H|³ − 3|H|² + 3|H|` (under SidonModNeg + subgroup closure).
* `addEnergy_lt_multEnergy_of_sidonModNeg` — for `|H| ≥ 3`, `E_+(H) < E_×(H)`: multiplicative
  energy STRICTLY dominates (additive `3n²−3n < n³` for `n ≥ 3`).
* `sumProduct_ratio_identity_of_sidonModNeg` (HEADLINE) — the asymmetry RATIO as a division-free
  cross-multiplied identity:
    `3·(|H| − 1)·E_×(H) = |H|²·E_+(H)`,
  i.e. `E_×(H) / E_+(H) = |H|² / (3(|H|−1)) ~ |H|/3`. The multiplicative energy exceeds the additive
  by a factor that grows **linearly in `n = |H|`** — the maximal sum-product asymmetry, realised
  exactly by the thin subgroup.

## Why this matters (honest scope)

The √(log) prize cancellation is an `M(μ_n) = max_b ‖η_b‖` (spectral, signed) statement; the energies
here are the sign-free second-moment shadows. The point this brick pins: the subgroup is the EXTREMAL
sum-product configuration — simultaneously additively Sidon-like (energy `Θ(n²)`, no AP structure to
exploit) and multiplicatively rigid (energy `n³`, the maximum). This is precisely the configuration on
which `δ*(smooth) ≈ δ*(random) ≈ capacity` and the genuine prize wall lives strictly above the second
moment (consistent with §3 meta-thm, the cliff-at-`n/2` guard, and the Sidon-frame divergence already
logged): a single even moment is thickness-monotone and the sum-product asymmetry, while extremal, is
sign-free and does NOT by itself yield the beyond-Johnson `√(log)` saving.

PROBE `scripts/probes/probe_sumproduct_asymmetry_subgroup.py`: on TRUE thin `μ_n` (proper,
`n = 2^a`, `p ≡ 1 mod n`, prize regime `p > n³`, incl. Fermat `257`, NEVER `n = q−1`): `E_× = n³`
exact, `E_+ = 3n²−3n` exact, ratio `n²/(3(n−1))` exact in EVERY prize-regime case; the small-q
`n=16, p=257 < n³` case shows `E_+` inflating to `912` (SidonModNeg fails) — the documented boundary
of the SidonModNeg hypothesis, NOT a counterexample to the welded theorem.

NOT a CORE closure, NOT a refutation. NON-MOMENT, field- and thickness-aware (the SidonModNeg
hypothesis is exactly the thinness condition), EXTEND-proven. No capacity / beyond-Johnson / cliff-at-`n/2` claim.
`CORE M(μ_n) ≤ C·√(n·log(q/n))` with absolute `C` remains **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`/`axiom`/`native_decide`. Issue #444.
-/

set_option linter.style.longLine false


open Finset

namespace ProximityGap.Frontier.SumProductAsymmetrySubgroup

open ProximityGap.Frontier.PencilAutocorrelation
open ArkLib.ProximityGap
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy_le_cube)
open ArkLib.ProximityGap.AdditiveEnergyBridge (addEnergy_eq_of_sidonModNeg)
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg (SidonModNeg)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The multiplicative energy of a finset `H` in the autocorrelation-sum form.**
`E_×(H) = ∑_ρ |H ∩ ρ·H|²` (over the multiplicative group of units acting by dilation). For a
multiplicative subgroup this equals `|H|³` (`multEnergy_eq_card_cube_of_subgroup`). -/
noncomputable def multEnergy (H : Finset Fˣ) : ℕ :=
  ∑ ρ : Fˣ, ((H ∩ dilate ρ H).card) ^ 2

/-- **`E_×(H) = |H|³` for a multiplicative subgroup** (restated from the pencil file). The all-or-
nothing subgroup autocorrelation makes the multiplicative energy maximal. -/
theorem multEnergy_eq_card_cube_of_subgroup {H : Finset Fˣ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    multEnergy H = H.card ^ 3 := by
  unfold multEnergy
  exact subgroup_multiplicativeEnergy_eq_card_cube hmul hinv

/-- **`E_×(H) = |H|³` is the MAXIMUM additive-energy value.** The subgroup's multiplicative energy
`|H|³` dominates the additive energy `E_+(K)` of EVERY `|H|`-cardinality set `K ⊆ F`
(`addEnergy_le_cube : E_+(K) ≤ |K|³`). So the thin subgroup sits at the very top of the energy range:
multiplicatively maximal. -/
theorem multEnergy_eq_max_addEnergy {H : Finset Fˣ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {K : Finset F} (hK : K.card = H.card) :
    SubgroupGaussSumFourthMoment.addEnergy K ≤ multEnergy H := by
  rw [multEnergy_eq_card_cube_of_subgroup hmul hinv, ← hK]
  exact addEnergy_le_cube K

/-- **The exact sum-product gap.** Welding the two proven endpoints: for a subgroup whose additive
realisation `K` (`|K| = |H|`) is Sidon-modulo-negation,
`E_×(H) − E_+(K) = |H|³ − (3|H|² − 3|H|) = |H|³ − 3|H|² + 3|H|`. -/
theorem multEnergy_minus_addEnergy_of_sidonModNeg {H : Finset Fˣ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {K : Finset F} (hK : K.card = H.card)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ K) (hneg : ∀ x ∈ K, -x ∈ K) (hS : SidonModNeg K) :
    multEnergy H - SubgroupGaussSumFourthMoment.addEnergy K = H.card ^ 3 - (3 * H.card ^ 2 - 3 * H.card) := by
  rw [multEnergy_eq_card_cube_of_subgroup hmul hinv,
      addEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hK]

/-- **Multiplicative energy STRICTLY dominates additive energy** for `|H| ≥ 3`.
`E_+(K) = 3n² − 3n < n³ = E_×(H)` whenever `n = |H| ≥ 3` (since `n³ − 3n² + 3n = n((n−1)² + 1) − n
> 0` strictly for `n ≥ 3`; explicitly `n³ > 3n²` for `n ≥ 4`, and `n=3` gives `27 > 18`). -/
theorem addEnergy_lt_multEnergy_of_sidonModNeg {H : Finset Fˣ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hcard : 3 ≤ H.card)
    {K : Finset F} (hK : K.card = H.card)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ K) (hneg : ∀ x ∈ K, -x ∈ K) (hS : SidonModNeg K) :
    SubgroupGaussSumFourthMoment.addEnergy K < multEnergy H := by
  rw [multEnergy_eq_card_cube_of_subgroup hmul hinv,
      addEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hK]
  -- `3n² − 3n < n³` for `n ≥ 3`. Abstract `n := H.card`, give omega the nonlinear cube fact.
  generalize hn : H.card = n at hcard ⊢
  have hmono : 3 * n ^ 2 < n ^ 3 + 3 * n := by
    -- `n³ + 3n − 3n² = n(n² − 3n + 3) = n((n−2)(n−1) + 1) > 0` for `n ≥ 3`.
    nlinarith [hcard, sq_nonneg n, Nat.zero_le n]
  have hge : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hcard, Nat.zero_le n]
  omega

/-- **HEADLINE: the sum-product asymmetry ratio, as a division-free integer identity.**
`3·(|H| − 1)·E_×(H) = |H|²·E_+(K)`, i.e. `E_×(H)/E_+(K) = |H|²/(3(|H|−1)) ~ |H|/3`. The
multiplicative energy exceeds the additive energy by a factor growing **linearly in `n = |H|`** —
the extremal sum-product asymmetry, realised exactly by the thin Sidon-mod-neg subgroup.

Derivation: `E_× = n³`, `E_+ = 3n² − 3n = 3n(n−1)`, so `3(n−1)·n³ = n²·3n(n−1)` is the same product
`3n³(n−1)` read two ways. -/
theorem sumProduct_ratio_identity_of_sidonModNeg {H : Finset Fˣ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {K : Finset F} (hK : K.card = H.card)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ K) (hneg : ∀ x ∈ K, -x ∈ K) (hS : SidonModNeg K) :
    3 * (H.card - 1) * multEnergy H = H.card ^ 2 * SubgroupGaussSumFourthMoment.addEnergy K := by
  rw [multEnergy_eq_card_cube_of_subgroup hmul hinv,
      addEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hK]
  -- LHS = 3(n−1)·n³; RHS = n²·(3n² − 3n) = n²·3n·(n−1) = 3(n−1)·n³. Pure `Nat` arithmetic.
  generalize H.card = n
  cases n with
  | zero => simp
  | succ k =>
    -- (k+1−1) = k; 3(k+1)² − 3(k+1) = 3(k+1)·k. Both sides become `3·k·(k+1)³`.
    have h3 : 3 * (k + 1) ^ 2 - 3 * (k + 1) = 3 * (k + 1) * k := by
      have : 3 * (k + 1) ^ 2 = 3 * (k + 1) * k + 3 * (k + 1) := by ring
      omega
    simp only [Nat.succ_sub_one]
    rw [h3]; ring

end ProximityGap.Frontier.SumProductAsymmetrySubgroup

/-! ## Axiom audit — expected `propext`, `Classical.choice`, `Quot.sound` only. -/
open ProximityGap.Frontier.SumProductAsymmetrySubgroup in
#print axioms multEnergy_eq_card_cube_of_subgroup
open ProximityGap.Frontier.SumProductAsymmetrySubgroup in
#print axioms multEnergy_eq_max_addEnergy
open ProximityGap.Frontier.SumProductAsymmetrySubgroup in
#print axioms multEnergy_minus_addEnergy_of_sidonModNeg
open ProximityGap.Frontier.SumProductAsymmetrySubgroup in
#print axioms addEnergy_lt_multEnergy_of_sidonModNeg
open ProximityGap.Frontier.SumProductAsymmetrySubgroup in
#print axioms sumProduct_ratio_identity_of_sidonModNeg
