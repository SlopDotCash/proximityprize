/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharFactorPi
import ArkLib.Data.CodingTheory.ProximityGap.KrawtchoukPoly
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The Hamming-shell Fourier transform IS the Krawtchouk polynomial (#389)

The generating function of an additive character over the Hamming weight factorizes into the
Krawtchouk generating function:

> **`shellGenFun_eq`** — `∑_e ψ(e)·X^{wt(e)} = (1+(q−1)X)^{n−w}·(1−X)^w`  (`w = ` character weight).
> **`shell_fourier`** — `∑_{wt(e)=k} ψ(e) = K_k(w)`  (the Fourier transform of the weight-`k` shell).

This is the bridge that turns the Shaw operator (the unified prize unknown) into a Krawtchouk-weighted
dual-MDS character sum. Axiom-clean.
-/
set_option linter.style.longLine false
set_option maxHeartbeats 800000


open Finset Polynomial
open ArkLib.ProximityGap.CharFactor ArkLib.ProximityGap.Krawtchouk

namespace ArkLib.ProximityGap.ShellFourier

variable {ι F : Type*} [Field F] [Fintype F] [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- The character weight: number of coordinates on which `ψ` is nontrivial. -/
noncomputable def charWeight (ψ : AddChar (ι → F) ℂ) : ℕ := #{i | axisChar ψ i ≠ 0}

/-- The character–Hamming generating function `∑_e ψ(e)·X^{wt e}`. -/
noncomputable def shellGenFun (ψ : AddChar (ι → F) ℂ) : Polynomial ℂ :=
  ∑ e : ι → F, (ψ e) • (X : ℂ[X]) ^ (hammingNorm e)

/-- A product of scalar-smul-monomials distributes: `∏ (aᵢ • pᵢ) = (∏ aᵢ) • (∏ pᵢ)`. -/
theorem prod_smul_distrib {a : ι → ℂ} {p : ι → ℂ[X]} :
    ∏ i, (a i • p i) = (∏ i, a i) • ∏ i, p i := by
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

/-- The per-axis generating factor. -/
theorem axis_factor (ψ : AddChar (ι → F) ℂ) (i : ι) :
    (∑ x : F, (axisChar ψ i x) • (X : ℂ[X]) ^ (if x = 0 then 0 else 1))
      = if axisChar ψ i = 0 then 1 + C ((Fintype.card F : ℂ) - 1) * X else 1 - X := by
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : F))]
  rw [if_pos rfl, pow_zero, smul_eq_C_mul, mul_one, AddChar.map_zero_eq_one, map_one]
  have hrest : ∀ x ∈ (univ : Finset F).erase 0,
      (axisChar ψ i x) • (X : ℂ[X]) ^ (if x = 0 then 0 else 1) = (axisChar ψ i x) • X := by
    intro x hx; rw [if_neg (Finset.ne_of_mem_erase hx), pow_one]
  rw [Finset.sum_congr rfl hrest, ← Finset.sum_smul, smul_eq_C_mul]
  -- ∑_{x≠0} ψ_i x = (∑_x) − ψ_i 0 = (if ψ_i=0 then q else 0) − 1
  have hsum : ∑ x ∈ (univ : Finset F).erase 0, axisChar ψ i x
      = (if axisChar ψ i = 0 then (Fintype.card F : ℂ) else 0) - 1 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), AddChar.sum_eq_ite,
      AddChar.map_zero_eq_one]
  rw [hsum]
  by_cases h : axisChar ψ i = 0 <;> simp [h] <;> ring

/-- **The shell generating function is the Krawtchouk generating function.** -/
theorem shellGenFun_eq (ψ : AddChar (ι → F) ℂ) :
    shellGenFun ψ
      = (1 + C ((Fintype.card F : ℂ) - 1) * X)
            ^ (Finset.univ.filter (fun i => axisChar ψ i = 0)).card
          * (1 - X) ^ (Finset.univ.filter (fun i => ¬ axisChar ψ i = 0)).card := by
  classical
  rw [shellGenFun]
  -- ψ e • X^wt = ∏_i (ψ_i(e_i) • X^[e_i≠0])
  have hterm : ∀ e : ι → F,
      (ψ e) • (X : ℂ[X]) ^ (hammingNorm e)
        = ∏ i, ((axisChar ψ i (e i)) • (X : ℂ[X]) ^ (if e i = 0 then 0 else 1)) := by
    intro e
    rw [prod_smul_distrib, ← addChar_pi_factor]
    congr 1
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    unfold hammingNorm
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : e i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  -- ∑_e ∏_i f i (e i) = ∏_i ∑_x f i x
  rw [← Fintype.prod_sum (fun i (x : F) => (axisChar ψ i x) • (X : ℂ[X]) ^ (if x = 0 then 0 else 1))]
  rw [Finset.prod_congr rfl (fun i _ => axis_factor ψ i)]
  -- ∏_i (if ψ_i=0 then A else B) = A^#(filter ·=0) · B^#(filter ¬·=0), exactly the RHS
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]


/-- The `k`-th coefficient of the shell generating function is the Fourier transform of the Hamming
weight-`k` shell. -/
theorem coeff_shellGenFun (ψ : AddChar (ι → F) ℂ) (k : ℕ) :
    (shellGenFun ψ).coeff k = ∑ e ∈ Finset.univ.filter (fun e => hammingNorm e = k), ψ e := by
  rw [shellGenFun, Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
  by_cases h : hammingNorm e = k
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (mt Eq.symm h), mul_zero]

/-- **The Hamming-shell Fourier transform is the Krawtchouk generating-polynomial coefficient.**
`∑_{wt(e)=k} ψ(e) = [z^k] (1+(q−1)z)^{#trivial axes}·(1−z)^{#nontrivial axes}`. By
`Krawtchouk.krawtchouk_eq_coeff` this coefficient is exactly `K_k(charWeight ψ)` — so the shell
Fourier transform of any product character is a Krawtchouk value. -/
theorem shell_fourier (ψ : AddChar (ι → F) ℂ) (k : ℕ) :
    (∑ e ∈ Finset.univ.filter (fun e => hammingNorm e = k), ψ e)
      = ((1 + C ((Fintype.card F : ℂ) - 1) * X)
            ^ (Finset.univ.filter (fun i => axisChar ψ i = 0)).card
          * (1 - X) ^ (Finset.univ.filter (fun i => ¬ axisChar ψ i = 0)).card).coeff k := by
  rw [← coeff_shellGenFun, shellGenFun_eq]

end ArkLib.ProximityGap.ShellFourier

#print axioms ArkLib.ProximityGap.ShellFourier.shellGenFun_eq
#print axioms ArkLib.ProximityGap.ShellFourier.shell_fourier
