/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# THE GARCIA–VOLOCH BOUND IS `≤ 2` WHEN `n ∣ p+1` (#389): the char-`p` Frobenius regime

The char-0 bound `repCount_le_two` (`r(c) ≤ 2` over `ℂ`) used complex conjugation
(`conj y = y⁻¹` on the unit circle).  Its exact **finite-field analog** holds whenever the
Frobenius `y ↦ y^p` acts on `μ_n` as inversion — i.e. when `n ∣ p+1`, so `μ_n ⊂ F_{p²}` is
the "quadratic" / conjugate-NTT subgroup:

> **`repCount_le_two_of_dvd_succ`** — over a field of characteristic `p` containing `μ_n`,
> if `n ∣ p+1` and `c` is Frobenius-fixed (`c^p = c`, i.e. `c` in the prime field) with
> `c ≠ 0`, then `r(c) = #{y ∈ μ_n : c − y ∈ μ_n} ≤ 2`.

The proof is the char-0 argument with **Frobenius in place of conjugation**: `n ∣ p+1` and
`y^n = 1` give `y^{p+1} = 1`, hence `y^p = y⁻¹`; the same for `c − y`; and Frobenius is
additive (`(c−y)^p = c^p − y^p`), so `(c−y)⁻¹ = c − y⁻¹`, forcing `y` to be a root of the
fixed degree-2 polynomial `X² − cX + 1`.  At most two such `y`.

This is an **unconditional char-`p` Garcia–Voloch bound** — no Stepanov needed — for the
entire `n ∣ p+1` family, pinning the GV object (and hence the additive energy `≤ 3n²` and the
MCA supply) on those finite fields.  It is the complement of the deployed NTT prize regime
`n ∣ p−1` (Frobenius trivial on `μ_n ⊂ F_p`), where the surplus is the genuine Stepanov wall.
So the GV difficulty is now pinned to *exactly* the `n ∣ p−1` (split) case.  Issue #389.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- In characteristic `p` with `n ∣ p+1`, the Frobenius acts as inversion on `μ_n`. -/
theorem frobenius_eq_inv_of_dvd_succ {n : ℕ} (ndvd : n ∣ p + 1) {z : F}
    (hzn : z ^ n = 1) (hz0 : z ≠ 0) : z ^ p = z⁻¹ := by
  have hz1 : z ^ (p + 1) = 1 := by
    obtain ⟨k, hk⟩ := ndvd
    rw [hk, pow_mul, hzn, one_pow]
  have hmul : z ^ p * z = 1 := by rw [← pow_succ, hz1]
  calc z ^ p = z ^ p * (z * z⁻¹) := by rw [mul_inv_cancel₀ hz0, mul_one]
    _ = (z ^ p * z) * z⁻¹ := by ring
    _ = z⁻¹ := by rw [hmul, one_mul]

/-- **THE FINITE-FIELD GV BOUND** (Frobenius regime `n ∣ p+1`): for EVERY nonzero `c`, the
additive representation count of `μ_n` is `≤ 2` — no `c^p = c` restriction. -/
theorem repCount_le_two_of_dvd_succ {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (ndvd : n ∣ p + 1) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) :
    repCount G c ≤ 2 := by
  classical
  have hcp0 : c ^ p ≠ 0 := pow_ne_zero p hc0
  -- the fixed degree-2 polynomial `c^p·X² − c·c^p·X + c` (leading coeff `c^p ≠ 0`)
  set P : F[X] := C (c ^ p) * X ^ 2 - C (c * c ^ p) * X + C c with hP
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
    -- Frobenius = inversion on both
    have hyp : y ^ p = y⁻¹ := frobenius_eq_inv_of_dvd_succ ndvd hyn hy0
    have hcyp : (c - y) ^ p = (c - y)⁻¹ := frobenius_eq_inv_of_dvd_succ ndvd hcyn hcy0
    -- `(c−y)^p = c^p − y^p = c^p − y⁻¹`, so `(c−y)⁻¹ = c^p − y⁻¹`
    have hcyinv : (c - y)⁻¹ = c ^ p - y⁻¹ := by
      rw [← hcyp, sub_pow_char_of_commute (R := F) (p := p) (Commute.all c y), hyp]
    have h2 : (c - y) * (c ^ p - y⁻¹) = 1 := by
      rw [← hcyinv]; exact mul_inv_cancel₀ hcy0
    have hyinv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0
    -- `y` is a root of `c^p·X² − c·c^p·X + c`
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp only [IsRoot, hP, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination (-y) * h2 + (-(c - y)) * hyinv
  calc repCount G c = (G.filter (fun y => c - y ∈ G)).card := rfl
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = 2 := hPdeg

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.frobenius_eq_inv_of_dvd_succ
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_two_of_dvd_succ
