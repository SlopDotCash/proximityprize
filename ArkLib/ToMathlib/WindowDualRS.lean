/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

/-!
# Window ⟺ dual-RS bridge over a root-of-unity domain

Let `ζ` be a primitive `n`-th root of unity in a field `F` with `n` invertible in `F`
(`(n : F) ≠ 0`), and let `v : F → F` be a word on the smooth domain
`μ_n = {ζ^0, …, ζ^{n-1}}`. This file proves the exact **dual Reed–Solomon
characterization** of vanishing power-sum windows, for any window length `1 ≤ t ≤ n`:

`∑_{i<n} v(ζ^i)·(ζ^i)^j = 0` for all `1 ≤ j < t`
  **iff**
`v` agrees on `μ_n` with the evaluation of a polynomial `f` with `natDegree f ≤ n − t`.

In coding-theory terms: the words on `μ_n` orthogonal to the power-sum window of length
`t − 1` (frequencies `1, …, t−1`) are *exactly* the Reed–Solomon codewords of dimension
`n − t + 1` — the dual of an RS code on a root-of-unity domain is again RS (the
cyclic/BCH picture). The forward direction (`window_vanishes_of_low_degree`) is monomial
orthogonality; the converse (`exists_low_degree_of_window`) is **inverse-DFT
reconstruction**: the interpolant is written down explicitly with coefficients
`c_k = n⁻¹ · ∑_{i<n} v(ζ^i)·(ζ^i)^{n−k}`, and the window hypothesis kills exactly the
coefficients `c_k` with `k > n − t` (note `(ζ^i)^{n-k} = (ζ^i)^{-k}` on the domain, so
`c_k` is the `k`-th inverse-DFT coefficient; the window starting at `j = 1` is what
spares the constant term `c_0`).

The engine is `pow_orbit_sum`: `∑_{i<n} (ζ^a)^i = n` if `n ∣ a` and `0` otherwise
(geometric sum + primitivity), specialized to a diagonal detector `dft_kernel_sum`:
`∑_{k<n} (ζ^i)^{n−k}·(ζ^{i₀})^k = n·[i = i₀]` for `i, i₀ < n`.

Everything is elementary field algebra over concrete `Finset.range` sums — no module
theory, no `CharZero`, no two-power assumption on `n`.

A `Finset.image`-domain form (`window_iff_exists_low_degree_image`) is provided for use
with set-indexed sums `∑ x ∈ μ_n, v x · x^j`.
-/

namespace ArkLib.WindowDualRS

open Finset Polynomial

variable {F : Type*} [Field F]

/-- **Orbit power-sum orthogonality** (the DFT engine): for a primitive `n`-th root of
unity `ζ`, the full-orbit geometric sum `∑_{i<n} (ζ^a)^i` equals `n` when `n ∣ a` and
vanishes otherwise. -/
theorem pow_orbit_sum {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (a : ℕ) :
    ∑ i ∈ Finset.range n, (ζ ^ a) ^ i = if n ∣ a then (n : F) else 0 := by
  by_cases h : n ∣ a
  · rw [if_pos h, (hζ.pow_eq_one_iff_dvd a).mpr h]
    simp
  · rw [if_neg h]
    have hα1 : ζ ^ a ≠ 1 := fun he => h ((hζ.pow_eq_one_iff_dvd a).mp he)
    have hαn : (ζ ^ a) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hα1, hαn, sub_self, zero_div]

/-- Diagonal detector on exponents: for `i, i₀ < n`, the frequency `i₀ + (n − i)`
(representing `i₀ − i` mod `n` with natural-number exponents) is divisible by `n`
iff `i = i₀`. -/
theorem dvd_add_sub_iff {n i i₀ : ℕ} (hi : i < n) (hi₀ : i₀ < n) :
    n ∣ i₀ + (n - i) ↔ i = i₀ := by
  constructor
  · intro hdvd
    have h1 : n ≤ i₀ + (n - i) := Nat.le_of_dvd (by omega) hdvd
    have h2 : n ∣ i₀ + (n - i) - n := Nat.dvd_sub hdvd dvd_rfl
    have h4 : i₀ + (n - i) - n = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  · rintro rfl
    exact ⟨1, by omega⟩

/-- Kernel-term normalization: on the orbit, `(ζ^i)^{n−k}·(ζ^{i₀})^k` is the `k`-th
power of the single root `ζ^{i₀ + (n − i)}` (using `ζ^n = 1` to absorb wrap-around). -/
theorem dft_kernel_term {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    {i i₀ k : ℕ} (hi : i < n) (hk : k ≤ n) :
    (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k = (ζ ^ (i₀ + (n - i))) ^ k := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hzk : (ζ ^ i) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hζ0)
  have h1 : (ζ ^ i) ^ (n - k) * (ζ ^ i) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, ← pow_mul, mul_comm i n, pow_mul,
      hζ.pow_eq_one, one_pow]
  have hL : (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k * (ζ ^ i) ^ k = (ζ ^ i₀) ^ k := by
    calc (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k * (ζ ^ i) ^ k
        = ((ζ ^ i) ^ (n - k) * (ζ ^ i) ^ k) * (ζ ^ i₀) ^ k := by ring
      _ = (ζ ^ i₀) ^ k := by rw [h1, one_mul]
  have hR : (ζ ^ (i₀ + (n - i))) ^ k * (ζ ^ i) ^ k = (ζ ^ i₀) ^ k := by
    rw [← mul_pow, ← pow_add]
    have hexp : i₀ + (n - i) + i = i₀ + n := by omega
    rw [hexp, pow_add, hζ.pow_eq_one, mul_one]
  exact mul_right_cancel₀ hzk (hL.trans hR.symm)

/-- **DFT kernel orthogonality**: `∑_{k<n} (ζ^i)^{n−k}·(ζ^{i₀})^k = n·[i = i₀]`
for `i, i₀ < n`. This is the inner sum of the inverse-DFT composed with the DFT. -/
theorem dft_kernel_sum {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    {i i₀ : ℕ} (hi : i < n) (hi₀ : i₀ < n) :
    ∑ k ∈ Finset.range n, (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k
      = if i = i₀ then (n : F) else 0 := by
  have hterm : ∀ k ∈ Finset.range n,
      (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k = (ζ ^ (i₀ + (n - i))) ^ k := fun k hk =>
    dft_kernel_term hζ hi (Finset.mem_range.mp hk).le
  rw [Finset.sum_congr rfl hterm, pow_orbit_sum hζ]
  by_cases h : i = i₀
  · rw [if_pos ((dvd_add_sub_iff hi hi₀).mpr h), if_pos h]
  · rw [if_neg fun hd => h ((dvd_add_sub_iff hi hi₀).mp hd), if_neg h]

/-- **Inverse-DFT reconstruction** of a word from its full power-sum spectrum: for any
`v : F → F` and `i₀ < n`,
`n⁻¹ · ∑_{k<n} (∑_{i<n} v(ζ^i)·(ζ^i)^{n−k}) · (ζ^{i₀})^k = v(ζ^{i₀})`. -/
theorem dft_inversion {ζ : F} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : (n : F) ≠ 0)
    (v : F → F) {i₀ : ℕ} (hi₀ : i₀ < n) :
    (n : F)⁻¹ * ∑ k ∈ Finset.range n,
        (∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k)) * (ζ ^ i₀) ^ k
      = v (ζ ^ i₀) := by
  have key : ∑ k ∈ Finset.range n,
      (∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k)) * (ζ ^ i₀) ^ k
      = (n : F) * v (ζ ^ i₀) := by
    calc ∑ k ∈ Finset.range n,
          (∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k)) * (ζ ^ i₀) ^ k
        = ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range n,
            v (ζ ^ i) * ((ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ Finset.range n,
            v (ζ ^ i) * ∑ k ∈ Finset.range n, (ζ ^ i) ^ (n - k) * (ζ ^ i₀) ^ k := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]
      _ = ∑ i ∈ Finset.range n, v (ζ ^ i) * (if i = i₀ then (n : F) else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [dft_kernel_sum hζ (Finset.mem_range.mp hi) hi₀]
      _ = (n : F) * v (ζ ^ i₀) := by
          rw [Finset.sum_eq_single i₀ (fun i _ hne => by rw [if_neg hne, mul_zero])
            (fun habs => absurd (Finset.mem_range.mpr hi₀) habs)]
          rw [if_pos rfl, mul_comm]
  rw [key, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- **Easy direction (dual-code containment)**: if `v` agrees on the orbit with the
evaluation of a polynomial of degree `≤ n − t`, then every power sum in the window
`1 ≤ j < t` vanishes. No invertibility of `n` is needed. -/
theorem window_vanishes_of_low_degree {ζ : F} {n t : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (htn : t ≤ n) {v : F → F} {f : F[X]} (hdeg : f.natDegree ≤ n - t)
    (hf : ∀ i < n, v (ζ ^ i) = f.eval (ζ ^ i))
    {j : ℕ} (hj : 1 ≤ j) (hjt : j < t) :
    ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ j = 0 := by
  have hdeg' : f.natDegree < n - t + 1 := by omega
  calc ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ j
      = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (n - t + 1),
          f.coeff k * ((ζ ^ i) ^ k * (ζ ^ i) ^ j) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hf i (Finset.mem_range.mp hi), eval_eq_sum_range' hdeg', Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ Finset.range (n - t + 1),
          f.coeff k * ∑ i ∈ Finset.range n, (ζ ^ (k + j)) ^ i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← pow_add, pow_right_comm]
    _ = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_range] at hk
        have hnd : ¬ n ∣ k + j := fun hdvd => by
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        rw [pow_orbit_sum hζ, if_neg hnd, mul_zero]

/-- **Inversion direction (dual-RS reconstruction)**: if all power sums in the window
`1 ≤ j < t` vanish (with `1 ≤ t ≤ n` and `n` invertible in `F`), then `v` agrees on the
orbit with the evaluation of an *explicit* polynomial of degree `≤ n − t`, namely the
inverse-DFT interpolant `∑_{k ≤ n−t} C(n⁻¹·∑_{i<n} v(ζ^i)(ζ^i)^{n−k})·X^k`. -/
theorem exists_low_degree_of_window {ζ : F} {n t : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : F) ≠ 0) (ht : 1 ≤ t) (htn : t ≤ n) {v : F → F}
    (hw : ∀ j, 1 ≤ j → j < t → ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ j = 0) :
    ∃ f : F[X], f.natDegree ≤ n - t ∧ ∀ i < n, v (ζ ^ i) = f.eval (ζ ^ i) := by
  refine ⟨∑ k ∈ Finset.range (n - t + 1),
      Polynomial.C ((n : F)⁻¹ * ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k))
        * Polynomial.X ^ k, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (by rw [Finset.mem_range] at hk; omega)
  · intro i₀ hi₀
    rw [Polynomial.eval_finset_sum]
    have heval : ∀ k ∈ Finset.range (n - t + 1),
        (Polynomial.C ((n : F)⁻¹ * ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k))
          * Polynomial.X ^ k).eval (ζ ^ i₀)
        = (n : F)⁻¹ *
            ((∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k)) * (ζ ^ i₀) ^ k) := by
      intro k _
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        mul_assoc]
    rw [Finset.sum_congr rfl heval]
    have hsub : Finset.range (n - t + 1) ⊆ Finset.range n := by
      intro k hk
      rw [Finset.mem_range] at *
      omega
    have hvanish : ∀ k ∈ Finset.range n, k ∉ Finset.range (n - t + 1) →
        (n : F)⁻¹ *
          ((∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ (n - k)) * (ζ ^ i₀) ^ k) = 0 := by
      intro k hk hk'
      rw [Finset.mem_range] at hk
      rw [Finset.mem_range, not_lt] at hk'
      rw [hw (n - k) (by omega) (by omega), zero_mul, mul_zero]
    rw [Finset.sum_subset hsub hvanish, ← Finset.mul_sum]
    exact (dft_inversion hζ hn v hi₀).symm

/-- **The window ⟺ dual-RS bridge** (range-indexed form). For a primitive `n`-th root
of unity `ζ` with `(n : F) ≠ 0` and any window length `1 ≤ t ≤ n`: the power sums
`∑_{i<n} v(ζ^i)·(ζ^i)^j` vanish for all `1 ≤ j < t` **iff** `v` agrees on the orbit
with a polynomial of degree `≤ n − t`. Equivalently: the dual of the power-sum window
code on a root-of-unity domain is exactly the Reed–Solomon code of dimension
`n − t + 1`. -/
theorem window_iff_exists_low_degree {ζ : F} {n t : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : F) ≠ 0) (ht : 1 ≤ t) (htn : t ≤ n) (v : F → F) :
    (∀ j, 1 ≤ j → j < t → ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ j = 0) ↔
      ∃ f : F[X], f.natDegree ≤ n - t ∧ ∀ i < n, v (ζ ^ i) = f.eval (ζ ^ i) := by
  constructor
  · exact exists_low_degree_of_window hζ hn ht htn
  · rintro ⟨f, hdeg, hf⟩ j hj hjt
    exact window_vanishes_of_low_degree hζ htn hdeg hf hj hjt

/-- Domain-set form of the bridge: sums over the orbit Finset
`μ_n = (range n).image (ζ ^ ·)` instead of indexed sums. -/
theorem window_iff_exists_low_degree_image [DecidableEq F] {ζ : F} {n t : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : F) ≠ 0) (ht : 1 ≤ t) (htn : t ≤ n)
    (v : F → F) :
    (∀ j, 1 ≤ j → j < t →
        ∑ x ∈ (Finset.range n).image (ζ ^ ·), v x * x ^ j = 0) ↔
      ∃ f : F[X], f.natDegree ≤ n - t ∧
        ∀ x ∈ (Finset.range n).image (ζ ^ ·), v x = f.eval x := by
  have hinj : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, ζ ^ i = ζ ^ j → i = j :=
    fun i hi j hj h =>
      hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have hsum : ∀ j : ℕ, ∑ x ∈ (Finset.range n).image (ζ ^ ·), v x * x ^ j
      = ∑ i ∈ Finset.range n, v (ζ ^ i) * (ζ ^ i) ^ j := fun j =>
    Finset.sum_image hinj
  constructor
  · intro hwin
    obtain ⟨f, hdeg, hf⟩ := (window_iff_exists_low_degree hζ hn ht htn v).mp
      fun j hj hjt => by rw [← hsum j]; exact hwin j hj hjt
    refine ⟨f, hdeg, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hf i (Finset.mem_range.mp hi)
  · rintro ⟨f, hdeg, hf⟩ j hj hjt
    rw [hsum j]
    exact window_vanishes_of_low_degree hζ htn hdeg
      (fun i hi => hf (ζ ^ i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩))
      hj hjt

end ArkLib.WindowDualRS

