/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B2_char0_logconcave
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lane L2 (#444): partial DISCHARGE of `SharpNewtonBessel` (char-0 step-ratio monotonicity)

`_wf8B2_char0_logconcave.lean` reduced the **characteristic-zero** half of the prize moment
monotonicity [W3-anti] *exactly* (axiom-clean) to the named classical input

  `SharpNewtonBessel d : ∀ r ≥ 1, (r+1)·c_{r-1}·c_{r+1} ≤ r·c_r²`,    `c_r := besselCoeff d r`

— the Laguerre–Pólya class type-I second-quotient inequality for the entire function
`I₀(2√x)^d`. Mathlib has **no** Pólya-frequency / Newton-inequality / real-rooted-polynomial
machinery (verified: no `Newton`, `logConcave`, `Maclaurin`, `PolyaFrequency` API), so the
general-`d` general-`r` statement cannot be built on the present substrate without first
formalising the whole LP-I limit theory (a large independent project).

This lane discharges the two sub-instances that ARE elementary, **fully axiom-clean**, and pins
precisely where the remaining gap is:

* **`sharpNewtonBessel_one`** — `SharpNewtonBessel 1` UNCONDITIONALLY (the base generator
  `g = I₀(2√x)`, `c_r = 1/(r!)²`). Here the sharp Newton inequality collapses to the schoolbook
  `r ≤ r+1` after clearing factorials. So for `d = 1` the headline
  `char0_W3anti_of_sharpNewton 1` becomes an **unconditional** theorem (`char0_W3anti_d_one`).

* **`sharpNewton_at_one`** — the `r = 1` instance `2·c₀·c₂ ≤ c₁²` for **every** `d ≥ 1`. This is
  the *prize-regime worst case*: the probe shows the minimal slack
  `min_r r·c_r²/((r+1)c_{r-1}c_{r+1})` sits at `r = 1` for large `d`
  (`= 2d/(2d−1) → 1`, asymptotically tight). It is proven from the **already-proven** Bessel
  sub-Gaussian bound `besselCoeff d r ≤ gaussianCoeff d r` (`bessel_energy_le_gaussian`) at
  `r = 2`, together with the exact evaluations `c₀ = 1`, `c₁ = d`, and `gaussianCoeff d 2 = d²/2`.
  No LP-I content is used: `2·c₂ ≤ 2·gaussianCoeff d 2 = d² = c₁²`.

## What remains genuinely open (the LP-I wall)

The intermediate band `2 ≤ r < d` is the only part still carried by the named
`SharpNewtonBessel`. There the sharp constant `(r+1)/r` is *forced* (the slack `→ 1` as
`d → ∞`), so no crude positive-slack elementary bound can close it — it is exactly the
real-rootedness (Laguerre–Pólya type-I) content of `I₀(2√x)^d`, the same class of obstruction as
the BGK wall on the prize-side. Tagged **CHAR0-ONLY** for those `r`: discharged at the endpoints
`d = 1` (all `r`) and `r = 1` (all `d`), open in the interior pending Newton-inequality machinery.

Pre-screen (exact rationals, `probe_wf8B2_sharpnewton_bessel.py`): `SharpNewtonBessel d` holds
strictly `> 1` to `n = 1024`, `r = 55`; the worst slack is the `r = 1` closed form `2d/(2d−1)`.
-/

open Finset BigOperators

namespace ProximityGap.PrizeWorkbench

/-! ## The `d = 1` generator: `c_r = 1/(r!)²`, full discharge -/

/-- `besselCoeff 1 r = 1/(r!)²`: the antidiagonal of `Fin 1`-tuples summing to `r` is the
singleton `{![r]}`, whose single product is `1/(r!)²`. -/
theorem besselCoeff_one_dim (r : ℕ) : besselCoeff 1 r = (1 : ℚ) / (r.factorial : ℚ) ^ 2 := by
  unfold besselCoeff
  rw [Finset.Nat.antidiagonalTuple_one]
  rw [Finset.sum_singleton]
  rw [Fin.prod_univ_one]
  norm_num

/-- **`SharpNewtonBessel 1`** (UNCONDITIONAL). For the base generator `g = I₀(2√x)` the sharp
Newton inequality `(r+1)·c_{r-1}·c_{r+1} ≤ r·c_r²` with `c_r = 1/(r!)²` clears all factorials
to the schoolbook `r ≤ r+1`. -/
theorem sharpNewtonBessel_one : SharpNewtonBessel 1 := by
  intro r hr
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  -- c_{k} = 1/(k!)², c_{k+1} = 1/((k+1)!)², c_{k+2} = 1/((k+2)!)².
  rw [besselCoeff_one_dim, besselCoeff_one_dim, besselCoeff_one_dim]
  simp only [Nat.add_sub_cancel]
  -- factorial successor expansions
  have hk : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos k
  have hf1 : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf2 : ((k + 2).factorial : ℚ) = ((k : ℚ) + 2) * ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    rw [show k + 2 = (k + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf1, hf2]
  -- goal: (k+1+1)·(1/(k!)²)·(1/(((k+2)(k+1)k!)²)) ≤ (k+1)·(1/(((k+1)k!)²))²
  have hk1pos : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have hk2pos : (0 : ℚ) < (k : ℚ) + 2 := by positivity
  push_cast
  -- Both sides are (positive rational) / (positive square); clear all denominators.
  have hbase : (0 : ℚ) < (k.factorial : ℚ) := hk
  have hkne : (k.factorial : ℚ) ≠ 0 := ne_of_gt hk
  have h1ne : (k : ℚ) + 1 ≠ 0 := ne_of_gt hk1pos
  have h2ne : (k : ℚ) + 2 ≠ 0 := ne_of_gt hk2pos
  -- Clearing all (positive) denominators reduces to the schoolbook `(k+1)(k+2) ≤ (k+2)²`.
  field_simp
  nlinarith [hk1pos, hk2pos]

/-- **Char-0 W3-anti for `d = 1`, UNCONDITIONAL**: the step ratio of the base generator is
`≤ 1` for all `r`, with no named hypothesis (`SharpNewtonBessel 1` is discharged above). -/
theorem char0_W3anti_d_one : ∀ r, Rstep 1 r ≤ 1 :=
  char0_W3anti_of_sharpNewton (le_refl 1) sharpNewtonBessel_one

/-! ## The `r = 1` worst case for every `d`, via the proven sub-Gaussian bound -/

/-- **Multinomial closed form for `gaussianCoeff`**: `gaussianCoeff d r = dʳ/r!`.
For each tuple `m` with `Σ mᵢ = r`, `∏ 1/mᵢ! = multinomial(m)/r!` by `Nat.multinomial_spec`;
summing the multinomial coefficients over `antidiagonalTuple d r = piAntidiag univ r` gives
`(∑_{i:Fin d} 1)ʳ = dʳ` by `Finset.sum_pow_eq_sum_piAntidiag`. Hence the sum is `dʳ/r!`. -/
theorem gaussianCoeff_eq (d r : ℕ) :
    gaussianCoeff d r = (d : ℚ) ^ r / (r.factorial : ℚ) := by
  unfold gaussianCoeff
  -- Bridge the index set to `piAntidiag univ r` over `Fin d`.
  rw [← Finset.piAntidiag_univ_fin_eq_antidiagonalTuple r d]
  have hfac : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  -- The multinomial sum over `piAntidiag univ r` equals `dʳ`.
  have hsum : ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin d)) r,
      (Nat.multinomial (Finset.univ : Finset (Fin d)) k : ℚ) = (d : ℚ) ^ r := by
    have := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin d))
      (fun _ : Fin d => (1 : ℚ)) r
    simp only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    rw [this]
  -- Termwise: `∏ 1/(kᵢ!) = multinomial(k) / r!` for `k ∈ piAntidiag univ r`.
  rw [eq_div_iff hfac, Finset.sum_mul]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_piAntidiag] at hk
  -- `∏ i, 1/(k i)! = 1 / ∏ i, (k i)!`.
  have hprod_pos : (0 : ℚ) < ∏ i, (Nat.factorial (k i) : ℚ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast Nat.factorial_pos (k i)
  have hprod_ne : (∏ i, (Nat.factorial (k i) : ℚ)) ≠ 0 := ne_of_gt hprod_pos
  -- `Nat.multinomial_spec`: `(∏ (k i)!) * multinomial = (∑ k i)! = r!`.
  have hspec : (∏ i, (Nat.factorial (k i) : ℚ)) *
      (Nat.multinomial (Finset.univ : Finset (Fin d)) k : ℚ) = (r.factorial : ℚ) := by
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin d)) k
    rw [hk.1] at h
    have := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at this
    convert this using 2
  -- rewrite `∏ 1/(k i)!` as `1 / ∏ (k i)!`.
  rw [show (∏ i, (1 : ℚ) / (Nat.factorial (k i)))
        = 1 / ∏ i, (Nat.factorial (k i) : ℚ) by
      rw [Finset.prod_div_distrib]; simp]
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hprod_ne]
  linear_combination -hspec

/-- `gaussianCoeff d 2 = d²/2`, the `r = 2` specialization of `gaussianCoeff_eq`
(the `Fin d`-tuples summing to `2`: the `d` tuples with one coord `= 2`, each `1/2`, and the
`C(d,2)` tuples with two coords `= 1`, each `1`; sum `= d/2 + d(d−1)/2 = d²/2`). -/
theorem gaussianCoeff_two (d : ℕ) : gaussianCoeff d 2 = (d : ℚ) ^ 2 / 2 := by
  rw [gaussianCoeff_eq d 2]
  norm_num [Nat.factorial]

/-- **`SharpNewtonBessel` at `r = 1`, for every `d ≥ 1`** (UNCONDITIONAL, no LP-I).
`2·c₀·c₂ ≤ c₁²`, the prize-regime worst case. Proof: `c₀ = 1`, `c₁ = d`, and
`c₂ ≤ gaussianCoeff d 2 = d²/2` by the proven Bessel sub-Gaussian bound, so
`2·c₂ ≤ d² = c₁²`. -/
theorem sharpNewton_at_one (d : ℕ) :
    (2 : ℚ) * besselCoeff d 0 * besselCoeff d 2 ≤ (1 : ℚ) * (besselCoeff d 1) ^ 2 := by
  rw [besselCoeff_zero, besselCoeff_one]
  have hsub : besselCoeff d 2 ≤ gaussianCoeff d 2 := bessel_energy_le_gaussian d 2
  rw [gaussianCoeff_two] at hsub
  -- 2 * 1 * c₂ ≤ 2 * (d²/2) = d² = 1 * d²
  nlinarith [hsub]

end ProximityGap.PrizeWorkbench

/-! ## Axiom audit -/
#print axioms ProximityGap.PrizeWorkbench.besselCoeff_one_dim
#print axioms ProximityGap.PrizeWorkbench.sharpNewtonBessel_one
#print axioms ProximityGap.PrizeWorkbench.char0_W3anti_d_one
#print axioms ProximityGap.PrizeWorkbench.gaussianCoeff_eq
#print axioms ProximityGap.PrizeWorkbench.gaussianCoeff_two
#print axioms ProximityGap.PrizeWorkbench.sharpNewton_at_one
