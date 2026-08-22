/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.Tactic.NormNum.Prime

/-!
# The exact `δ*` table at `n = 16` on the Fermat prime `F₄ = 65537` (#444, RQ exact-pin)

A *consolidated, fully-closed, axiom-clean* table of the **mutual-correlated-agreement
threshold `δ*`** (the prize quantity `mcaDeltaStar`, NOT a list-size crossover) for the
explicit smooth-domain Reed–Solomon codes on the order-`16` multiplicative subgroup
`μ_16 ⊆ F_p^×`, `p = 65537 = 2^16 + 1` (the Fermat prime `F₄`), at all four prize rates
`ρ ∈ {1/2, 1/4, 1/8, 1/16}`.

## Why this prime / this domain

`p = 65537` is the smallest prize-*shaped* prime for `n = 16`: it is prime, `n = 16 ∣ p − 1`
(in fact `p − 1 = 2^16`, so `μ_16` is a genuine *proper, thin* subgroup — `16 ≪ 65537`), and
`β = log_n p = log_16 65537 = 4` sits exactly on the Burgess barrier `β = 4` that defines the
prize regime `β ∈ [4, 5]`.  The evaluation domain `dom : Fin 16 ↪ F_p` enumerates
`μ_16 = ⟨4⟩ = {4^0, …, 4^15}` (`4` has multiplicative order `16`), a genuinely *smooth*
(`16 = 2^4`) domain.  Each row is the code `RS[F_p, μ_16, k]` for `k = 8, 4, 2, 1`
(rate `ρ = k/16`).

## What is pinned (closed form, from the granularity ladder)

For each rate we instantiate `mcaDeltaStar_rs_eq_granularity` (`GranularityLadderRS.lean`) at the
**maximal** band index `j` for which the ladder closes (`3(j−1)+k ≤ n` and `j+1+k ≤ n`),
yielding the *exact maximal-window* pin

  `mcaDeltaStar (RS[F_p, μ_16, k]) ε* = j / 16`   for every `ε* ∈ [j/p, (j+1)/p)`.

| `ρ`    | `k` | `j` (max) | `δ* = j/16` | window `ε* ∈ [j/p, (j+1)/p)` |
|--------|-----|-----------|-------------|------------------------------|
| `1/2`  | `8` | `3`       | `3/16`      | `[3/65537, 4/65537)`         |
| `1/4`  | `4` | `5`       | `5/16`      | `[5/65537, 6/65537)`         |
| `1/8`  | `2` | `5`       | `5/16`      | `[5/65537, 6/65537)`         |
| `1/16` | `1` | `6`       | `3/8`       | `[6/65537, 7/65537)`         |

The capstone `deltaStar_table_n16_F65537` bundles all four rows.

## Honest scope (what this is, and is NOT)

* **NEW in-tree.**  The only existing exact `mcaDeltaStar` pins are single instances at
  `n = 4` (`DeltaStarExactPinF5`), `n = 8` (`DeltaStarSecondPinF17{,Maximal}`,
  `DeltaStarPinMu8F4129`); and the only existing *table* (`DeltaStarTableSmoothInstances`)
  certifies a *different* quantity — list-size crossovers, not the threshold `mcaDeltaStar`.
  This is the first consolidated `mcaDeltaStar` table, the first at `n = 16`, the first
  covering all four prize rates on one (Fermat) field, and the first on a genuine `μ_16`
  subgroup domain.  No theorem here duplicates an existing one.
* **Sub-Johnson, honestly.**  The granularity ladder pins `δ*` only *below* the window: at
  `n = 16` it reaches `δ* ≤ 6/16 = 3/8`, while the Johnson radius `1 − √ρ` ranges over
  `0.293, 0.5, 0.646, 0.75`.  Every pin here is therefore **strictly sub-Johnson** — the
  unconditional regime.  This is the exact closed-form *below* the prize window; the
  window-interior pin (the open core) is untouched.  It is bound to a *fixed finite shape*,
  not the asymptotic `n = 2^30`, `ε* = 2^{−128}` prize family.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.DeltaStarTableN16Fermat

/-- The Fermat prime `F₄ = 2^16 + 1 = 65537`. -/
abbrev p : ℕ := 65537

/-- The field `F_p = ZMod 65537`. -/
abbrev Fp := ZMod p

instance primeFact_DeltaStarTableN16Fermat_1 : Fact (Nat.Prime p) := ⟨by norm_num⟩

/-- The smooth evaluation domain `μ_16 = ⟨4⟩ ⊆ F_p^×`, enumerated as the successive powers
`4^0, …, 4^15`.  `4` has multiplicative order `16` in `F_65537^×` (`4^8 = 65536 = −1 ≠ 1`,
`4^16 = 1`), so these `16` residues are distinct and form a genuine order-`16` (proper, thin)
multiplicative subgroup. -/
def domVals : Fin 16 → Fp :=
  ![1, 4, 16, 64, 256, 1024, 4096, 16384,
    65536, 65533, 65521, 65473, 65281, 64513, 61441, 49153]

/-- The domain as an injective embedding `Fin 16 ↪ F_p` (the `16` residues are distinct,
checked by `decide`). -/
def dom : Fin 16 ↪ Fp where
  toFun := domVals
  inj' := by decide

/-- **Smoothness witness.**  Every domain element is a `16`-th root of unity:
`(dom i)^16 = 1`, i.e. `μ_16 ⊆ {x : x^16 = 1}` — a genuine order-`16` subgroup of `F_p^×`. -/
theorem dom_pow16_eq_one : ∀ i : Fin 16, (dom i) ^ 16 = 1 := by decide

/-- `Fintype.card (ZMod 65537) = 65537`. -/
theorem card_Fp : Fintype.card Fp = 65537 := by
  simp [Fp, p, ZMod.card]

/-! ## The four rows of the table -/

open ProximityGap.SpikeFloor in
/-- **Row ρ = 1/2** (`k = 8`).  `δ* = 3/16` on `ε* ∈ [3/65537, 4/65537)`. -/
theorem deltaStar_rho_half {εstar : ℝ≥0∞}
    (hlo : (3 : ℝ≥0∞) / (65537 : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (4 : ℝ≥0∞) / (65537 : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
      ((rsCode dom 8 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) εstar
      = (3 : ℝ≥0) / 16 := by
  have h := mcaDeltaStar_rs_eq_granularity (F := Fp) (n := 16) dom (k := 8) (j := 3)
    (by norm_num) (by norm_num) (by norm_num) (by rw [card_Fp]; norm_num)
    (εstar := εstar)
    (by rw [card_Fp]; exact_mod_cast hlo)
    (by rw [card_Fp]; exact_mod_cast hhi)
  rw [Fintype.card_fin] at h
  exact h

open ProximityGap.SpikeFloor in
/-- **Row ρ = 1/4** (`k = 4`).  `δ* = 5/16` on `ε* ∈ [5/65537, 6/65537)`. -/
theorem deltaStar_rho_quarter {εstar : ℝ≥0∞}
    (hlo : (5 : ℝ≥0∞) / (65537 : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (6 : ℝ≥0∞) / (65537 : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
      ((rsCode dom 4 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) εstar
      = (5 : ℝ≥0) / 16 := by
  have h := mcaDeltaStar_rs_eq_granularity (F := Fp) (n := 16) dom (k := 4) (j := 5)
    (by norm_num) (by norm_num) (by norm_num) (by rw [card_Fp]; norm_num)
    (εstar := εstar)
    (by rw [card_Fp]; exact_mod_cast hlo)
    (by rw [card_Fp]; exact_mod_cast hhi)
  rw [Fintype.card_fin] at h
  exact h

open ProximityGap.SpikeFloor in
/-- **Row ρ = 1/8** (`k = 2`).  `δ* = 5/16` on `ε* ∈ [5/65537, 6/65537)`. -/
theorem deltaStar_rho_eighth {εstar : ℝ≥0∞}
    (hlo : (5 : ℝ≥0∞) / (65537 : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (6 : ℝ≥0∞) / (65537 : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
      ((rsCode dom 2 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) εstar
      = (5 : ℝ≥0) / 16 := by
  have h := mcaDeltaStar_rs_eq_granularity (F := Fp) (n := 16) dom (k := 2) (j := 5)
    (by norm_num) (by norm_num) (by norm_num) (by rw [card_Fp]; norm_num)
    (εstar := εstar)
    (by rw [card_Fp]; exact_mod_cast hlo)
    (by rw [card_Fp]; exact_mod_cast hhi)
  rw [Fintype.card_fin] at h
  exact h

open ProximityGap.SpikeFloor in
/-- **Row ρ = 1/16** (`k = 1`).  `δ* = 3/8` on `ε* ∈ [6/65537, 7/65537)`. -/
theorem deltaStar_rho_sixteenth {εstar : ℝ≥0∞}
    (hlo : (6 : ℝ≥0∞) / (65537 : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < (7 : ℝ≥0∞) / (65537 : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
      ((rsCode dom 1 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) εstar
      = (6 : ℝ≥0) / 16 := by
  have h := mcaDeltaStar_rs_eq_granularity (F := Fp) (n := 16) dom (k := 1) (j := 6)
    (by norm_num) (by norm_num) (by norm_num) (by rw [card_Fp]; norm_num)
    (εstar := εstar)
    (by rw [card_Fp]; exact_mod_cast hlo)
    (by rw [card_Fp]; exact_mod_cast hhi)
  rw [Fintype.card_fin] at h
  exact h

/-! ## The capstone table -/

open ProximityGap.SpikeFloor in
/-- **THE EXACT δ\* TABLE AT `n = 16` ON THE FERMAT PRIME `F₄ = 65537`.**

For the smooth-domain Reed–Solomon codes `RS[F_65537, μ_16, k]` on the order-`16`
multiplicative subgroup `μ_16 = ⟨4⟩ ⊆ F_65537^×`, the mutual-correlated-agreement threshold
`δ*` is pinned exactly, in closed form, at all four prize rates:

* `ρ = 1/2` (`k = 8`):  `δ* = 3/16` on `ε* ∈ [3/p, 4/p)`;
* `ρ = 1/4` (`k = 4`):  `δ* = 5/16` on `ε* ∈ [5/p, 6/p)`;
* `ρ = 1/8` (`k = 2`):  `δ* = 5/16` on `ε* ∈ [5/p, 6/p)`;
* `ρ = 1/16` (`k = 1`): `δ* = 6/16` on `ε* ∈ [6/p, 7/p)`.

Every entry is sub-Johnson (the unconditional regime); the window-interior pin is the open
core and is untouched. -/
theorem deltaStar_table_n16_F65537 :
    (∀ ε : ℝ≥0∞, (3 : ℝ≥0∞) / 65537 ≤ ε → ε < (4 : ℝ≥0∞) / 65537 →
      MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
        ((rsCode dom 8 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) ε
        = (3 : ℝ≥0) / 16) ∧
    (∀ ε : ℝ≥0∞, (5 : ℝ≥0∞) / 65537 ≤ ε → ε < (6 : ℝ≥0∞) / 65537 →
      MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
        ((rsCode dom 4 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) ε
        = (5 : ℝ≥0) / 16) ∧
    (∀ ε : ℝ≥0∞, (5 : ℝ≥0∞) / 65537 ≤ ε → ε < (6 : ℝ≥0∞) / 65537 →
      MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
        ((rsCode dom 2 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) ε
        = (5 : ℝ≥0) / 16) ∧
    (∀ ε : ℝ≥0∞, (6 : ℝ≥0∞) / 65537 ≤ ε → ε < (7 : ℝ≥0∞) / 65537 →
      MCAThresholdLedger.mcaDeltaStar (F := Fp) (A := Fp)
        ((rsCode dom 1 : Submodule Fp (Fin 16 → Fp)) : Set (Fin 16 → Fp)) ε
        = (6 : ℝ≥0) / 16) :=
  ⟨fun ε hlo hhi => deltaStar_rho_half hlo hhi,
   fun ε hlo hhi => deltaStar_rho_quarter hlo hhi,
   fun ε hlo hhi => deltaStar_rho_eighth hlo hhi,
   fun ε hlo hhi => by rw [deltaStar_rho_sixteenth hlo hhi]⟩

end ProximityGap.DeltaStarTableN16Fermat

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeltaStarTableN16Fermat.dom_pow16_eq_one
#print axioms ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_half
#print axioms ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_sixteenth
#print axioms ProximityGap.DeltaStarTableN16Fermat.deltaStar_table_n16_F65537
