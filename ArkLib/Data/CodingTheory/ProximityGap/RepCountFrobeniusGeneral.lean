/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFrobeniusEnergy

/-!
# THE GV BOUND `≤ 2` FOR EVERY INERT-TYPE REGIME `n ∣ p^k+1` (#389)

The Frobenius-as-inversion bound generalizes from `n ∣ p+1` to `n ∣ p^k+1` for **any** `k`:
whenever the `k`-fold Frobenius `y ↦ y^{p^k}` acts on `μ_n` as inversion (i.e. `μ_n ⊂ F_{p^{2k}}`
is inert under `Frob^k`), the same degree-2 argument gives `r(c) ≤ 2` for all `c ≠ 0`.

> **`repCount_le_two_of_dvd_pow_succ`** — over a char-`p` field with `n ∣ p^k+1`, the additive
> representation count of `μ_n` is `≤ 2` for every `c ≠ 0`; hence `E(μ_n) ≤ 3n²`.

`Frob^k = y ↦ y^{p^k}` is additive (`(c−y)^{p^k} = c^{p^k} − y^{p^k}`, `sub_pow_char_pow`), and
`n ∣ p^k+1` with `y^n = 1` gives `y^{p^k} = y⁻¹`; so `(c−y)⁻¹ = c^{p^k} − y⁻¹`, forcing `y` to
be a root of `c^{p^k}·X² − c·c^{p^k}·X + c`.  This covers **every** `n` for which `−1` is a power
of `p` mod `n` (the inert-type regimes), strictly generalizing `n ∣ p+1` (the `k = 1` case).

The split case `n ∣ p−1` is *never* of this form (`p ≡ 1 ⟹ p^k ≡ 1 ≢ −1 mod n` for `n > 2`), so
it remains the unique open Stepanov regime — the dichotomy is exhaustive: inert-type
(`n ∣ p^k+1`) solved, split (`n ∣ p−1`) the wall.  Issue #389.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- `Frob^k` is inversion on `μ_n` when `n ∣ p^k+1`. -/
theorem frobenius_pow_eq_inv_of_dvd_pow_succ {n k : ℕ} (ndvd : n ∣ p ^ k + 1) {z : F}
    (hzn : z ^ n = 1) (hz0 : z ≠ 0) : z ^ p ^ k = z⁻¹ := by
  have hz1 : z ^ (p ^ k + 1) = 1 := by
    obtain ⟨j, hj⟩ := ndvd
    rw [hj, pow_mul, hzn, one_pow]
  have hmul : z ^ p ^ k * z = 1 := by rw [← pow_succ, hz1]
  calc z ^ p ^ k = z ^ p ^ k * (z * z⁻¹) := by rw [mul_inv_cancel₀ hz0, mul_one]
    _ = (z ^ p ^ k * z) * z⁻¹ := by ring
    _ = z⁻¹ := by rw [hmul, one_mul]

/-- **THE INERT-TYPE GV BOUND** (`n ∣ p^k+1`): the additive representation count of `μ_n` is
`≤ 2` for every `c ≠ 0` — unconditional, no Stepanov. -/
theorem repCount_le_two_of_dvd_pow_succ {G : Finset F} {n k : ℕ} (hn : 1 ≤ n)
    (ndvd : n ∣ p ^ k + 1) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) :
    repCount G c ≤ 2 := by
  classical
  have hcp0 : c ^ p ^ k ≠ 0 := pow_ne_zero _ hc0
  set P : F[X] := C (c ^ p ^ k) * X ^ 2 - C (c * c ^ p ^ k) * X + C c with hP
  have hPdeg : P.natDegree = 2 := by
    rw [hP]; compute_degree!; exact fun h => absurd h hc0
  have hP0 : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hPdeg; exact absurd hPdeg (by norm_num)
  have hroots : (G.filter (fun y => c - y ∈ G)) ⊆ P.roots.toFinset := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcyG
    have hy0 : y ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hyn; exact zero_ne_one hyn
    have hcy0 : c - y ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hcyn; exact zero_ne_one hcyn
    have hyp : y ^ p ^ k = y⁻¹ := frobenius_pow_eq_inv_of_dvd_pow_succ ndvd hyn hy0
    have hcyp : (c - y) ^ p ^ k = (c - y)⁻¹ := frobenius_pow_eq_inv_of_dvd_pow_succ ndvd hcyn hcy0
    have hcyinv : (c - y)⁻¹ = c ^ p ^ k - y⁻¹ := by
      rw [← hcyp, sub_pow_char_pow_of_commute (R := F) (p := p) (n := k) (Commute.all c y), hyp]
    have h2 : (c - y) * (c ^ p ^ k - y⁻¹) = 1 := by
      rw [← hcyinv]; exact mul_inv_cancel₀ hcy0
    have hyinv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp only [IsRoot, hP, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination (-y) * h2 + (-(c - y)) * hyinv
  calc repCount G c = (G.filter (fun y => c - y ∈ G)).card := rfl
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = 2 := hPdeg

/-- **THE INERT-TYPE ENERGY BOUND** (`n ∣ p^k+1`): `E(μ_n) ≤ 3·|μ_n|²`. -/
theorem additiveEnergy_le_of_dvd_pow_succ {G : Finset F} {n k : ℕ} (hn : 1 ≤ n)
    (ndvd : n ∣ p ^ k + 1) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    additiveEnergy G ≤ 3 * G.card ^ 2 :=
  additiveEnergy_le_of_repCount_le_two
    (fun c hc0 => repCount_le_two_of_dvd_pow_succ hn ndvd hGmem hc0)

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_two_of_dvd_pow_succ
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_le_of_dvd_pow_succ
