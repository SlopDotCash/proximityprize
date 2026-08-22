/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMarkov
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality

/-!
# Exact-energy fourth-moment count for the thin `2`-power subgroup `μ_n` (#444)

The generic fourth-moment Markov bound
`SubgroupGaussSumFourthMarkov.card_johnson_scale_frequencies_le_energy_div`
gives `#{b : ‖η_b‖² ≥ q} ≤ E(G)/q` for any `G`. For the **thin `2`-power NTT subgroup**
`μ_n ⊂ F_p` (`n = 2^m`, `m ≥ 1`, `p > 2^n`) the additive energy is **exactly** the
Sidon-modulo-negation minimum `E(μ_n) = 3n² − 3n` (proven, unconditional, cyclotomic-resultant
only: `AdditiveEnergyBridge.addEnergy_eq_of_sidonModNeg`). Substituting that exact energy gives the
**explicit, field-size-free count**

> **`card_johnson_scale_frequencies_muN_le`** —
>   `#{b : ‖η_b(μ_n)‖² ≥ q} ≤ (3n² − 3n)/q = 3n(n−1)/q`.

This is the **upper-count companion** to `ShawFlatnessRefuted.shaw_flatness_false_mu_n`
(which uses the *same* exact energy `E(μ_n) = 3n²−3n` for the L⁴/L² **lower** bound
`∃ b≠0, ‖η_b‖² > 2n`). Here the same energy drives the **Markov upper bound on the count** of
Johnson-scale-exceeding frequencies.

## Thinness-essential (rule 3)

The bound rests on `E(μ_n) = 3n²−3n`, the Sidon-modulo-negation **minimum** — it is FALSE in the
thick window where the subgroup carries strictly more additive energy `E ≫ 3n²` (e.g. `μ_n` near
`n = q−1`, where `E(F_q^*) ~ q³`), so the count `E/q` is no longer `O(n²/q)`. The exactness is the
cyclotomic-resultant `|Res(Φ_n,·)| ≤ 2^n < p` lift, available only for the thin `2`-power tower.

## Scope (honest, rules 1,3,6)

This is the **fourth-moment / Markov** localization, NOT a CORE closure. `q ≈ n^β` (`β≥4`) makes the
RHS `3n(n−1)/q ≈ 3n²/n^β → 0`, i.e. for the prize prime size **no** frequency reaches the Johnson
scale `‖η_b‖² ≥ q` (consistent with `card < 1 ⟹ count = 0`) — but the prize floor lives **far below**
the Johnson scale `√q`, at `√(n·log(p/n))`, and the worst-case-over-`b≠0` sup-norm at that finer
scale is the open BGK content this count bound does not touch. No capacity over-claim. CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays **open**.

See `SubgroupGaussSumFourthMarkov.lean` (the generic count bound), `AdditiveEnergyBridge.lean`
(`addEnergy = additiveEnergy`, exact `μ_n` energy) and `ShawFlatnessRefuted.lean` (the lower-bound
companion using the same energy).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyBridge
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMarkovMuN

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **`μ_n` is negation-closed** (`n = 2^m`, `m ≥ 1` ⟹ `n` even ⟹ `(-x)^n = x^n`). -/
theorem muN_neg_closed (hn2 : n = 2 ^ m) (hm : 1 ≤ m) :
    ∀ x ∈ nthRootsFinset n (1 : ZMod p), -x ∈ nthRootsFinset n (1 : ZMod p) := by
  have hn0 : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  intro x hx
  rw [mem_nthRootsFinset hnpos] at hx ⊢
  have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  rw [neg_pow, he.neg_one_pow, one_mul]; exact hx

/-- **Exact-energy fourth-moment Johnson-scale count for `μ_n`** (multiplied form).
For `n = 2^m` (`m ≥ 1`), `p > 2^n`, a primitive `n`-th root `ω ∈ ZMod p` and a primitive additive
character `ψ`, the number of frequencies whose `η_b` over `μ_n = nthRootsFinset n 1` reaches the
Johnson scale `‖η_b‖² ≥ q` obeys `#{·}·q ≤ 3n² − 3n`. The bound is the proven exact thin-subgroup
energy fed into the generic fourth-moment count. -/
theorem card_johnson_scale_frequencies_muN_mul_le (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter
        (fun b : ZMod p =>
          (Fintype.card (ZMod p) : ℝ) ≤ ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2)).card : ℝ)
        * (Fintype.card (ZMod p) : ℝ)
      ≤ (3 * (n : ℝ) ^ 2 - 3 * n) := by
  set G : Finset (ZMod p) := nthRootsFinset n (1 : ZMod p) with hGdef
  have hn0 : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hGmem : ∀ z : ZMod p, z ∈ G ↔ z ^ n = 1 := fun z => mem_nthRootsFinset hnpos 1
  have hcard : G.card = n := hω.card_nthRootsFinset
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn0))
  have hp2 : 2 < p := by omega
  have h2F : (2 : ZMod p) ≠ 0 := by
    intro hcontra
    have hdvd : (p : ℕ) ∣ 2 := by rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast hcontra
    have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h0 : (0 : ZMod p) ∉ G := by rw [hGmem]; simp [zero_pow hn0]
  have hneg : ∀ x ∈ G, -x ∈ G := muN_neg_closed hn2 hm
  have hS := sidonModNeg_mu_n hn2 hm hp hω hGmem
  have hEnat : addEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    addEnergy_eq_of_sidonModNeg h2F h0 hneg hS
  -- generic fourth-moment count: #{·}·q ≤ E(G)
  have hqpos : 0 < Fintype.card (ZMod p) := Fintype.card_pos
  have hgen := card_johnson_scale_frequencies_mul_le_energy hψ G hqpos
  -- rewrite E(G) to the exact `3n²−3n`
  have hsub : 3 * G.card ≤ 3 * G.card ^ 2 := by
    nlinarith [Nat.le_self_pow (two_ne_zero) G.card]
  have hEreal : (addEnergy G : ℝ) = 3 * (n : ℝ) ^ 2 - 3 * n := by
    rw [hEnat, Nat.cast_sub hsub, hcard]; push_cast; ring
  rw [hEreal] at hgen
  exact hgen

/-- **Exact-energy fourth-moment Johnson-scale count for `μ_n`** (divided form).
`#{b : ‖η_b(μ_n)‖² ≥ q} ≤ (3n² − 3n)/q = 3n(n−1)/q`. The explicit, field-size-free count of
Johnson-scale-exceeding frequencies for the thin `2`-power subgroup, from its exact additive energy.
Thinness-essential (FALSE for thick subgroups whose energy exceeds `3n²`). -/
theorem card_johnson_scale_frequencies_muN_le (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter
        (fun b : ZMod p =>
          (Fintype.card (ZMod p) : ℝ) ≤ ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2)).card : ℝ)
      ≤ (3 * (n : ℝ) ^ 2 - 3 * n) / (Fintype.card (ZMod p) : ℝ) := by
  have hqpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ hqpos]
  exact card_johnson_scale_frequencies_muN_mul_le hn2 hm hp hω hψ

end ArkLib.ProximityGap.SubgroupGaussSumFourthMarkovMuN

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMarkovMuN.card_johnson_scale_frequencies_muN_mul_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMarkovMuN.card_johnson_scale_frequencies_muN_le
