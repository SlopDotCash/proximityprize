/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Sweep A04 — Constant-index Gauss-sum bound (`ConstantIndexGaussSumBound`)

**Actionable A04 (re-land).** A clean, fully-provable substrate result. Prove the
**constant-index** upper bound on the Gauss period and document the **barrier** that makes it
vacuous at the prize.

## Setup (the object)

`F_q` a finite field, `μ_n ≤ F_q^*` the multiplicative subgroup of order `n`, index
`m = (q-1)/n`. For `b ≠ 0`, the Gauss period
`η_b = Σ_{x∈μ_n} ψ(b x)`, `ψ` a fixed primitive additive character.

## The structural decomposition (the input)

`1_{μ_n}` expands over the `m` multiplicative characters `χ` trivial on `μ_n` (the order-`m`
subgroup `μ_n^⊥` of the dual). Multiplying by `m`,
`m · η_b = Σ_{j<m} gaussSum(χ_j, ψ_b)`,
where `χ_0 = 1` is principal. The principal term is `Σ_{x∈F_q^*} ψ(b x) = -1`, and each of the
other `m-1` terms is a **nontrivial** Gauss sum, of modulus `√q` exactly
(mathlib `gaussSum_mul_gaussSum_eq_card` ⟹ `‖gaussSum χ ψ‖ = √q` for `χ≠1`, `ψ` primitive;
character values have unit modulus). Hence, writing `η := η_b`, `τ : Fin m → ℂ` for the Gauss
sums with `‖τ 0‖ = 1` (the principal term `-1`) and `‖τ j‖ = √q` for `j ≠ 0`:

`m · η = Σ_{j<m} τ j`  and  `m‖η‖ ≤ 1 + (m-1)√q`,

i.e. `‖η_b‖ ≤ ((m-1)√q + 1) / m ≤ √q`.

**This file's content.** We package the *exact* structural facts as hypotheses (the
decomposition `m • η = Σ τ` and the term moduli) and prove the upper bound by triangle
inequality (`index_decomp_norm_le`, `eta_constIndex_norm_le`). We additionally prove,
**unconditionally**, the **barrier**: `f(m) := ((m-1)√q+1)/m` is increasing in `m` and
`f(m) ≥ √q/2` for every `m ≥ 2`, so its square is `≥ q/4` for ALL indices — the lever NEVER
beats `√q/2`, and at the prize index `m = 2^128` it is `≈ √q`, exponentially above the prize
floor `√(n·log(q/n))`. So this is a genuine sub-`√q` result **only for constant / polylog
index** `m`; it is **vacuous at the prize**.

**Honesty.** The Gauss-sum moduli `‖τ j‖ = √q (j≠0)` and `‖τ 0‖ = 1` are the standard mathlib
facts (`gaussSum_mul_gaussSum_eq_card`); we take them as the named structural input and prove the
*arithmetic* consequence and the *barrier* axiom-clean. This is NOT a step toward the prize floor
— the barrier theorem proves it cannot be — it is a faithful, fully-proven substrate brick plus
its explicit limitation. No fabricated closure. Cross-checked exactly by
`scripts/probes/sweep_A04_constindex_gausssum.py` (identity error ~1e-13; bound holds; barrier
confirmed at prize scale).
-/

namespace ArkLib.ProximityGap.Sweep_A04

open scoped BigOperators
open Finset

/-! ### The structural triangle bound -/

/-- **Triangle bound on the index-`m` decomposition (abstract).** If `m • η = Σ_{j∈Fin m} τ j`,
the `0`-th term has norm `≤ 1` (the principal Gauss-sum term `-1`), and every other term has
norm `≤ s` (think `s = √q`), then `m · ‖η‖ ≤ (m-1)·s + 1`. Pure triangle inequality on `ℂ`. -/
theorem index_decomp_norm_le {m : ℕ} (hm : 1 ≤ m) (η : ℂ) (τ : Fin m → ℂ) (s : ℝ)
    (hsum : (m : ℂ) * η = ∑ j, τ j)
    (h0 : ‖τ ⟨0, hm⟩‖ ≤ 1)
    (hpos : ∀ j : Fin m, j ≠ ⟨0, hm⟩ → ‖τ j‖ ≤ s) :
    (m : ℝ) * ‖η‖ ≤ (m - 1 : ℝ) * s + 1 := by
  classical
  -- `‖m • η‖ = m * ‖η‖`.
  have hlhs : ‖(m : ℂ) * η‖ = (m : ℝ) * ‖η‖ := by
    rw [norm_mul, Complex.norm_natCast]
  -- `‖Σ τ j‖ ≤ Σ ‖τ j‖`.
  have htri : ‖∑ j, τ j‖ ≤ ∑ j, ‖τ j‖ := norm_sum_le _ _
  -- Split the RHS sum: the `0`-term `≤ 1`, the other `m-1` terms each `≤ s`.
  set j0 : Fin m := ⟨0, hm⟩ with hj0
  have hsplit : ∑ j, ‖τ j‖ = ‖τ j0‖ + ∑ j ∈ univ.erase j0, ‖τ j‖ := by
    rw [← Finset.add_sum_erase univ (fun j => ‖τ j‖) (Finset.mem_univ j0)]
  have hrest : ∑ j ∈ univ.erase j0, ‖τ j‖ ≤ ∑ _j ∈ univ.erase j0, s := by
    apply Finset.sum_le_sum
    intro j hj
    exact hpos j (Finset.ne_of_mem_erase hj)
  have hcard : (univ.erase j0).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
  have hconst : ∑ _j ∈ univ.erase j0, s = (m - 1 : ℝ) * s := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    congr 1
    rw [Nat.cast_sub hm, Nat.cast_one]
  -- Chain.
  calc (m : ℝ) * ‖η‖ = ‖(m : ℂ) * η‖ := hlhs.symm
    _ = ‖∑ j, τ j‖ := by rw [hsum]
    _ ≤ ∑ j, ‖τ j‖ := htri
    _ = ‖τ j0‖ + ∑ j ∈ univ.erase j0, ‖τ j‖ := hsplit
    _ ≤ 1 + (m - 1 : ℝ) * s := by
        apply add_le_add h0
        rw [← hconst]; exact hrest
    _ = (m - 1 : ℝ) * s + 1 := by ring

/-- **The constant-index Gauss-sum bound** `eta_constIndex_norm_le`. With the standard Gauss-sum
moduli `s = √q` and `‖τ 0‖ = 1`, the index-`m` Gauss period satisfies
`‖η_b‖ ≤ ((m-1)·√q + 1) / m`. Immediate from `index_decomp_norm_le` by dividing by `m > 0`. -/
theorem eta_constIndex_norm_le {m : ℕ} (hm : 1 ≤ m) (η : ℂ) (τ : Fin m → ℂ) (q : ℝ)
    (hsum : (m : ℂ) * η = ∑ j, τ j)
    (h0 : ‖τ ⟨0, hm⟩‖ ≤ 1)
    (hpos : ∀ j : Fin m, j ≠ ⟨0, hm⟩ → ‖τ j‖ ≤ Real.sqrt q) :
    ‖η‖ ≤ ((m - 1 : ℝ) * Real.sqrt q + 1) / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hmpos, mul_comm]
  exact index_decomp_norm_le hm η τ (Real.sqrt q) hsum h0 hpos

/-- **Corollary: `‖η_b‖ ≤ √q`** for every index `m ≥ 1`, whenever `q ≥ 1`. The constant-index
bound is at worst the trivial completion bound (consistent with the average `√n`). -/
theorem eta_constIndex_le_sqrt {m : ℕ} (hm : 1 ≤ m) (η : ℂ) (τ : Fin m → ℂ) (q : ℝ)
    (hq : 1 ≤ q)
    (hsum : (m : ℂ) * η = ∑ j, τ j)
    (h0 : ‖τ ⟨0, hm⟩‖ ≤ 1)
    (hpos : ∀ j : Fin m, j ≠ ⟨0, hm⟩ → ‖τ j‖ ≤ Real.sqrt q) :
    ‖η‖ ≤ Real.sqrt q := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hq
  refine le_trans (eta_constIndex_norm_le hm η τ q hsum h0 hpos) ?_
  rw [div_le_iff₀ hmpos]
  -- ((m-1)√q + 1) ≤ √q · m  ⟺  1 ≤ √q  (since 1 ≤ √q).
  have : (m - 1 : ℝ) * Real.sqrt q + 1 ≤ (m - 1 : ℝ) * Real.sqrt q + Real.sqrt q := by
    linarith
  refine le_trans this ?_
  have hexp : (m - 1 : ℝ) * Real.sqrt q + Real.sqrt q = Real.sqrt q * m := by ring
  rw [hexp]

/-! ### The barrier (unconditional, real-arithmetic) — why this is vacuous at the prize -/

/-- The constant-index bound value as a function of the index `m` (for `q ≥ 0`). -/
noncomputable def boundVal (m : ℝ) (q : ℝ) : ℝ := ((m - 1) * Real.sqrt q + 1) / m

/-- **Barrier (lower bound on the bound).** For every index `m ≥ 2` and `q ≥ 1`, the
constant-index bound is `≥ √q / 2`. So it NEVER beats `√q/2`: the squared scale is `≥ q/4` at
every `m ≥ 2`. -/
theorem boundVal_ge_half_sqrt {m q : ℝ} (hm : 2 ≤ m) :
    Real.sqrt q / 2 ≤ boundVal m q := by
  have hmpos : (0 : ℝ) < m := by linarith
  have hsq0 : (0 : ℝ) ≤ Real.sqrt q := Real.sqrt_nonneg q
  unfold boundVal
  rw [le_div_iff₀ hmpos]
  -- want: √q/2 · m ≤ (m-1)√q + 1.
  -- Since m ≥ 2: (m-1) ≥ m/2, so (m-1)√q ≥ (m/2)√q = √q/2·m, and +1 only helps.
  have hstep : Real.sqrt q / 2 * m ≤ (m - 1) * Real.sqrt q := by
    have : Real.sqrt q / 2 * m = (m / 2) * Real.sqrt q := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hsq0
    linarith
  linarith

/-- **Barrier (squared form).** For `m ≥ 2`, `q ≥ 1`, the SQUARE of the constant-index bound is
`≥ q/4`. This is the quantitative "vacuous at the prize" statement: the bound's scale is `Θ(√q)`,
never below `√q/2`, whatever the index. -/
theorem boundVal_sq_ge_quarter {m q : ℝ} (hm : 2 ≤ m) (hq : 1 ≤ q) :
    q / 4 ≤ (boundVal m q) ^ 2 := by
  have h1 : Real.sqrt q / 2 ≤ boundVal m q := boundVal_ge_half_sqrt hm
  have hb0 : (0 : ℝ) ≤ Real.sqrt q / 2 := by positivity
  have hsq : (Real.sqrt q / 2) ^ 2 ≤ (boundVal m q) ^ 2 :=
    pow_le_pow_left₀ hb0 h1 2
  have hqsq : (Real.sqrt q / 2) ^ 2 = q / 4 := by
    rw [div_pow, Real.sq_sqrt (le_trans zero_le_one hq)]; norm_num
  rw [← hqsq]; exact hsq

/-- **Barrier (monotonicity).** `m ↦ boundVal m q` is monotone INCREASING for `m ≥ 1`, `q ≥ 1`:
larger index ⟹ weaker bound, approaching `√q`. So shrinking the index helps, but only down to
`m = 2` where the floor `√q/2` already bites; the prize index `m = 2^128` sits at the worst
(`≈ √q`) end. Formally `boundVal m q = √q + (1 - √q)/m`, manifestly increasing in `m` since
`1 - √q ≤ 0`. -/
theorem boundVal_eq_affine {m q : ℝ} (hm : 0 < m) :
    boundVal m q = Real.sqrt q + (1 - Real.sqrt q) / m := by
  unfold boundVal
  field_simp
  ring

theorem boundVal_mono {m₁ m₂ q : ℝ} (h1 : 1 ≤ m₁) (h12 : m₁ ≤ m₂) (hq : 1 ≤ q) :
    boundVal m₁ q ≤ boundVal m₂ q := by
  have hm1 : (0 : ℝ) < m₁ := by linarith
  have hm2 : (0 : ℝ) < m₂ := by linarith
  rw [boundVal_eq_affine hm1, boundVal_eq_affine hm2]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hq
  -- `(1-√q)/m` with `1-√q ≤ 0` is increasing in `m`: `(1-√q)/m₁ ≤ (1-√q)/m₂`.
  have hneg : (1 - Real.sqrt q) ≤ 0 := by linarith
  -- write as `c * (1/m)` with `c ≤ 0`; `1/m₂ ≤ 1/m₁` so `c·(1/m₁) ≤ c·(1/m₂)`.
  have hinv : (1 : ℝ) / m₂ ≤ 1 / m₁ := by
    apply one_div_le_one_div_of_le hm1 h12
  have hkey : (1 - Real.sqrt q) / m₁ ≤ (1 - Real.sqrt q) / m₂ := by
    rw [div_eq_mul_one_div (1 - Real.sqrt q) m₁, div_eq_mul_one_div (1 - Real.sqrt q) m₂]
    exact mul_le_mul_of_nonpos_left hinv hneg
  linarith

end ArkLib.ProximityGap.Sweep_A04

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.Sweep_A04.eta_constIndex_norm_le
#print axioms ArkLib.ProximityGap.Sweep_A04.eta_constIndex_le_sqrt
#print axioms ArkLib.ProximityGap.Sweep_A04.boundVal_sq_ge_quarter
#print axioms ArkLib.ProximityGap.Sweep_A04.boundVal_mono
