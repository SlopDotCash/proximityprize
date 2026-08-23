/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Odd-character orthogonality — Parseval over the odd powers (issue #232)

Let `ζ` be a primitive `2*m2`-th root of unity in a field `F`. The *odd characters*
are the maps `i ↦ ζ^(2i+1)` for `i < m2` — over `ℚ(ζ_m)` (with `m = 2*m2` a 2-power)
these are exactly the `φ(m) = m/2` embeddings into `ℂ`, since `(ℤ/m)^×` consists of
the odd residues.

Main result (`parseval_odd_powers`): for any coefficients `c : ℕ → F`,

`∑_{i<m2} (∑_{j<m2} c j · ζ^{(2i+1)j}) · (∑_{j<m2} c j · ζ^{-(2i+1)j})
  = m2 · ∑_{j<m2} (c j)²`.

Over `ℂ`, since `conj` of a root of unity is its inverse, the left side is
`∑_{odd i} |σ_i(α)|²` for `α = ∑_j c_j ζ^j` — i.e. the **Parseval identity over odd
characters**, `∑_{i ∈ (ℤ/m)^×} |σ_i(α)|² = (m/2) · ∑ c_j²`. Combined with AM–GM over
the `m/2` embeddings this gives the norm threshold
`|N(α)| ≤ (∑ c_j²)^{m/4}`, the engine of the effective per-prime exactness bound for
subgroup subset-sum collision counts (DISPROOF_LOG O38, `EffectivePerPrimeExactness.md`):
per-prime exactness of the `N₀(m,r)` bad-scalar counts holds unconditionally above the
threshold `T(m,r) = (4·min(r, m−r))^{m/4}`, with no GRH input.

The engine here is `odd_power_orthogonality`: `∑_{i<m2} ζ^{(2i+1)δ}` equals `m2` when
`δ = 0` and vanishes for `0 < |δ| < m2`, by factoring the odd-power sum as
`ζ^δ · ∑_{i<m2} (ζ^{2δ})^i` and applying the geometric-sum formula (primitivity gives
`ζ^{2δ} ≠ 1` while `(ζ^{2δ})^{m2} = 1`).

Everything is elementary field algebra — no number-field or `ℂ`-specific machinery.
-/

namespace ArkLib.CharacterSums

open Finset

variable {F : Type*} [Field F]

/-- **Orthogonality of odd powers** of a primitive `2*m2`-th root of unity: for
`j, j' < m2`, the character sum `∑_{i<m2} ζ^{(2i+1)j} · ζ^{-(2i+1)j'}` is `m2` on the
diagonal `j = j'` and `0` off it. -/
lemma odd_power_orthogonality {m2 : ℕ} (hm2 : 0 < m2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m2)) {j j' : ℕ} (hj : j < m2) (hj' : j' < m2) :
    ∑ i ∈ range m2, (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j' =
      if j = j' then (m2 : F) else 0 := by
  have h2m2 : 2 * m2 ≠ 0 := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero h2m2
  by_cases h : j = j'
  · -- diagonal: every term is `1`
    subst h
    have hone : ∀ i ∈ range m2, (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j = 1 := by
      intro i _
      rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_pow]
    rw [sum_congr rfl hone, sum_const, card_range, if_pos rfl]
    simp
  · -- off-diagonal: factor as `ζ^δ · ∑ (ζ^{2δ})^i` and kill the geometric sum
    rw [if_neg h]
    set δ : ℤ := (j : ℤ) - (j' : ℤ) with hδdef
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hterm : ∀ i ∈ range m2,
        (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j' =
          ζ ^ δ * (ζ ^ (2 * δ)) ^ i := by
      intro i _
      have hb0 : (ζ : F) ^ (2 * i + 1) ≠ 0 := pow_ne_zero _ hζ0
      rw [inv_pow, ← zpow_natCast (ζ ^ (2 * i + 1)) j, ← zpow_natCast (ζ ^ (2 * i + 1)) j',
        ← zpow_neg, ← zpow_add₀ hb0, ← zpow_natCast ζ (2 * i + 1), ← zpow_mul,
        ← zpow_natCast (ζ ^ (2 * δ)) i, ← zpow_mul, ← zpow_add₀ hζ0]
      congr 1
      push_cast
      ring
    rw [sum_congr rfl hterm, ← mul_sum]
    have hx1 : ζ ^ (2 * δ) ≠ 1 := by
      intro hcontra
      rw [hζ.zpow_eq_one_iff_dvd] at hcontra
      have h2 : (2 : ℤ) * (m2 : ℤ) ∣ 2 * δ := by push_cast at hcontra ⊢; exact hcontra
      have hdvd : (m2 : ℤ) ∣ δ := (mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).mp h2
      have hle : (m2 : ℤ) ≤ |δ| := Int.le_of_dvd (abs_pos.mpr hδ0) ((dvd_abs _ _).mpr hdvd)
      have habs : |δ| < (m2 : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
      exact absurd hle (not_le.mpr habs)
    have hxm2 : (ζ ^ (2 * δ)) ^ m2 = 1 := by
      rw [← zpow_natCast (ζ ^ (2 * δ)) m2, ← zpow_mul]
      have hexp : 2 * δ * (m2 : ℤ) = ((2 * m2 : ℕ) : ℤ) * δ := by push_cast; ring
      rw [hexp, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [geom_sum_eq hx1, hxm2, sub_self, zero_div, mul_zero]

/-- **Parseval over the odd characters** (E1): for a primitive `2*m2`-th root of unity
`ζ` and coefficients `c`, summing `(∑_j c_j w^j)(∑_j c_j w^{-j})` over the odd powers
`w = ζ^(2i+1)` gives `m2 · ∑_j c_j²`. Over `ℂ` this reads
`∑_{i ∈ (ℤ/m)^×} |σ_i(α)|² = (m/2) ∑ c_j²` for `α = ∑ c_j ζ^j` — the identity behind
the AM–GM norm threshold for per-prime subset-sum exactness (DISPROOF_LOG O38). -/
theorem parseval_odd_powers {m2 : ℕ} (hm2 : 0 < m2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 * m2)) (c : ℕ → F) :
    ∑ i ∈ range m2,
      (∑ j ∈ range m2, c j * (ζ ^ (2 * i + 1)) ^ j) *
        (∑ j ∈ range m2, c j * ((ζ ^ (2 * i + 1))⁻¹) ^ j) =
      (m2 : F) * ∑ j ∈ range m2, c j ^ 2 := by
  have expand : ∀ i ∈ range m2,
      (∑ j ∈ range m2, c j * (ζ ^ (2 * i + 1)) ^ j) *
        (∑ j ∈ range m2, c j * ((ζ ^ (2 * i + 1))⁻¹) ^ j) =
      ∑ j ∈ range m2, ∑ j' ∈ range m2,
        c j * c j' * ((ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j') := by
    intro i _
    rw [sum_mul_sum]
    exact sum_congr rfl fun j _ => sum_congr rfl fun j' _ => by ring
  rw [sum_congr rfl expand, sum_comm]
  have swap_inner : ∀ j ∈ range m2,
      ∑ i ∈ range m2, ∑ j' ∈ range m2,
        c j * c j' * ((ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j') =
      ∑ j' ∈ range m2, c j * c j' *
        (∑ i ∈ range m2, (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j') := by
    intro j _
    rw [sum_comm]
    exact sum_congr rfl fun j' _ => by rw [← mul_sum]
  rw [sum_congr rfl swap_inner]
  have ortho : ∀ j ∈ range m2, ∀ j' ∈ range m2,
      c j * c j' * (∑ i ∈ range m2, (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j') =
      c j * c j' * (if j = j' then (m2 : F) else 0) := by
    intro j hj j' hj'
    rw [odd_power_orthogonality hm2 hζ (mem_range.mp hj) (mem_range.mp hj')]
  have diag : ∀ j ∈ range m2,
      ∑ j' ∈ range m2, c j * c j' * (if j = j' then (m2 : F) else 0) =
        c j ^ 2 * m2 := by
    intro j hj
    rw [sum_eq_single j (fun j' _ hne => by rw [if_neg (fun hh => hne hh.symm), mul_zero])
      (fun habs => absurd hj habs)]
    rw [if_pos rfl]; ring
  calc ∑ j ∈ range m2, ∑ j' ∈ range m2, c j * c j' *
        (∑ i ∈ range m2, (ζ ^ (2 * i + 1)) ^ j * ((ζ ^ (2 * i + 1))⁻¹) ^ j')
      = ∑ j ∈ range m2, ∑ j' ∈ range m2, c j * c j' * (if j = j' then (m2 : F) else 0) :=
        sum_congr rfl fun j hj => sum_congr rfl fun j' hj' => ortho j hj j' hj'
    _ = ∑ j ∈ range m2, c j ^ 2 * m2 := sum_congr rfl diag
    _ = (m2 : F) * ∑ j ∈ range m2, c j ^ 2 := by rw [← sum_mul, mul_comm]

end ArkLib.CharacterSums
