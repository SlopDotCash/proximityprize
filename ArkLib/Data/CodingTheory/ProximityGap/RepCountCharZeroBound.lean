/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# THE CHARACTERISTIC-ZERO GARCIA–VOLOCH BOUND IS `≤ 2` (#389): the hardness is purely char-`p`

Over `ℂ`, the Garcia–Voloch object `r(c) = #{y ∈ μ_n : c − y ∈ μ_n}` is bounded by **2** for
every `c ≠ 0` — the entire `n^{2/3}` difficulty is the *characteristic-`p` surplus*, nothing
intrinsic to the subgroup:

> **`repCount_le_two`** — over `ℂ`, for `c ≠ 0`, `r(c) ≤ 2`.

The reason is geometric: `y ∈ μ_n` lies on the unit circle `|y| = 1`, and `c − y ∈ μ_n` lies
on the unit circle `|c − y| = 1`, i.e. `y` lies on the unit circle *centred at `c`*.  Two
distinct circles meet in at most two points.  Algebraically (using `conj y = y⁻¹` for `|y|=1`),
every such `y` is a root of the **fixed degree-2 polynomial**
`P(Y) = c̄·Y² − c·c̄·Y + c` (`c̄ = conj c`, leading coefficient `c̄ ≠ 0`), so there are at most
`deg P = 2` of them.

Consequently the char-`0` additive energy is `E_ℂ(μ_n) = Σ_c r(c)² ≤ 4·|μ_n + μ_n| = O(n²)`,
far below the char-`p` `|G|^{8/3}` — so the Heath-Brown–Konyagin / Stepanov bound is needed
*only* to control the prime-characteristic surplus over the char-`0` value, exactly localising
the open kernel (`StepanovAux` Wronskian) to the char-`p` excess.  Issue #389.
-/

open Finset Polynomial Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- For a root of unity `y` in `ℂ` (`yⁿ = 1`, `n ≠ 0`), `y · conj y = 1`. -/
theorem mul_conj_eq_one_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {y : ℂ} (hy : y ^ n = 1) :
    y * (starRingEnd ℂ) y = 1 := by
  have hnorm : ‖y‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg y) hn).mp (by rw [← norm_pow, hy, norm_one])
  have hns : Complex.normSq y = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
  rw [Complex.mul_conj, hns, Complex.ofReal_one]

/-- **THE CHAR-0 GV BOUND**: over `ℂ`, the additive representation count of `μ_n` is `≤ 2`. -/
theorem repCount_le_two {G : Finset ℂ} {n : ℕ} (hn : n ≠ 0)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : ℂ} (hc : c ≠ 0) :
    repCount G c ≤ 2 := by
  classical
  set cc := (starRingEnd ℂ) c with hcc
  have hcc0 : cc ≠ 0 := by rw [hcc, starRingEnd_apply]; exact star_ne_zero.mpr hc
  -- the fixed degree-2 polynomial whose roots contain the representation set
  set P : ℂ[X] := C cc * X ^ 2 - C (c * cc) * X + C c with hP
  have hPdeg : P.natDegree = 2 := by
    rw [hP]
    compute_degree!
  have hP0 : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hPdeg; exact absurd hPdeg (by norm_num)
  -- every representation point is a root of `P`
  have hroots : (G.filter (fun y => c - y ∈ G)) ⊆ P.roots.toFinset := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcyG
    have hy1 : y * (starRingEnd ℂ) y = 1 := mul_conj_eq_one_of_pow_eq_one hn hyn
    have hcy1 : (c - y) * (starRingEnd ℂ) (c - y) = 1 :=
      mul_conj_eq_one_of_pow_eq_one hn hcyn
    rw [map_sub] at hcy1
    -- `P.eval y = 0` from the two unit-modulus relations
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp only [IsRoot, hP, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    -- `cc·y² − c·cc·y + c = 0` from the two unit-modulus relations
    linear_combination (-y) * hcy1 + (-(c - y)) * hy1
  calc repCount G c = (G.filter (fun y => c - y ∈ G)).card := rfl
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' _
    _ = 2 := hPdeg

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_two
