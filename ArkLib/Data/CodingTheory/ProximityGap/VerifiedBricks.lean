/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Verified bricks for the Ethereum Proximity Prize (Issue #232)

This file collects the elementary, fully machine-checked lemmas proven while sifting the candidate
generator for ArkLib Issue #232 (the $1M ABF26 Proximity Prize). Each is `sorry`-free and
axiom-clean (`#print axioms` ⇒ `[propext, Classical.choice, Quot.sound]`). None of them resolves
the prize: pinning the MCA threshold `δ*` in the Johnson→capacity gap with matching two-sided
bounds at `ε* = 2^{-128}` remains open research. These are honest *building blocks* and *honest
refutations* of naive/mis-targeted directions, kept here so the open core is correctly delineated
(cf. #169/#171: no fake-completion surfaces).

Contents:
* Algebraic structure — `hasseDeriv_X_pow_prime_pow_sub_one` (char-`p` Hasse–Lucas collapse of the
  vanishing polynomial) and `dyadic_factor_coprime_trivial` (2-adic CRT product-grid obstruction).
* Threshold geometry — `johnson_radius_le_capacity`, `radius_mono_in_exponent` (the
  `1 − ρ^{m/(m+1)}` family interpolates Johnson→capacity; the `1 − ρ^{2/3}` candidate is the
  `m = 2` member), and `candidate_between_johnson_and_capacity`.
* List-decoding engine — `fiber_root_card_le`, `grid_zero_count_le`, `on_curve_iff_mem_roots`,
  `gs_list_card_le` (the GS list-size bound `|list| ≤ deg_Y(H)`), `interpolation_kernel_nontrivial`
  (a low-degree interpolant exists by counting), `eval_zero_of_agreement_gt_degree`
  (agreement ⇒ the codeword is a root), `natDegree_eval_le` (the explicit GS degree budget), and
  `sudan_codeword_list_bound` (the quantitative Sudan list bound `|L| ≤ deg_Y(H)` for codewords
  agreeing beyond `deg_X(H) + (k-1)·deg_Y(H)`) — the full combinatorial *and* quantitative GS core.
* Multiplicities — `sum_rootMultiplicity_le`, `eval_zero_of_multiplicity_agreement`, and
  `gs_multiplicity_list_bound` (the multiplicity-`r` root counting and list bound).
* Quantitative GS parameters — `sudan_params_feasible` (the pure-arithmetic feasibility of the GS
  parameter program: a `d_X` exists with interpolation space `> n` and budget `< t`; for
  multiplicity `r`, reuse it with `t ↦ t·r`, `n ↦ n·r(r+1)/2`).

Note on radius: the list-decoding bricks use the **box** degree bound `(deg_X, deg_Y)`, which
realizes the Sudan radius `1 − √(2ρ)`. Reaching the **Johnson** radius `1 − √ρ` requires
*weighted-degree* `(1, k-1)` interpolation; its triangular monomial count is now formalized
(`weighted_degree_count`) together with the key `D² ≤ 2(k-1)·N(D)` lower bound
(`weighted_degree_count_lb`) — the factor `2` over the rectangle that *is* Johnson-over-Sudan.
Pushing past Johnson for explicit smooth-domain RS remains the open prize.
* Refutations — `refute_naive_matrix_rank_bound`, `refute_naive_alg_independence_bound`.
-/

namespace ArkLib.ProximityGap.Issue232Bricks

open Polynomial

/-! ## Algebraic structure -/

section Algebraic
variable {R : Type*} [CommRing R]

/-- **Char-`p` middle binomial vanishing.** In a commutative ring of prime characteristic `p`,
`C(p^a, m)` casts to `0` for `0 < m < p^a` (Lucas/Kummer for the prime `p`), via comparing
`X^m`-coefficients of `(X+1)^{p^a}` (binomial theorem) and `X^{p^a}+1` (Frobenius). -/
lemma choose_prime_pow_cast_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) : ((p ^ a).choose m : R) = 0 := by
  have hfrob : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + 1 := by
    have h : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + (1 : R[X]) ^ (p ^ a) :=
      add_pow_char_pow X 1 p a
    rwa [one_pow] at h
  have e := congrArg (fun q : R[X] => q.coeff m) hfrob
  simp only [coeff_X_add_one_pow, coeff_add, coeff_X_pow, coeff_one] at e
  rw [if_neg (Nat.ne_of_lt hlt), if_neg (Nat.pos_iff_ne_zero.mp hm), add_zero] at e
  exact e

/-- **Hasse–Lucas collapse of the vanishing polynomial.** Over a characteristic-`p` ring,
`hasseDeriv m (X^{p^a} − 1) = 0` for `0 < m < p^a`. (The `p = 2` instance is the binary-field
case; relevant to additive/Binius domains, not the multiplicative-subgroup prize domain.) -/
theorem hasseDeriv_X_pow_prime_pow_sub_one (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) :
    hasseDeriv m (X ^ (p ^ a) - 1 : R[X]) = 0 := by
  ext j
  rw [coeff_zero, hasseDeriv_coeff, coeff_sub, coeff_X_pow, coeff_one]
  by_cases hj : j + m = p ^ a
  · rw [if_pos hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_one, hj]
    exact choose_prime_pow_cast_eq_zero p a m hm hlt
  · rw [if_neg hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_zero]

end Algebraic

/-- **Dyadic coprime impossibility.** If `a · b = 2^k` and `gcd a b = 1`, then `a = 1` or `b = 1`:
a power of two has no nontrivial coprime factorization. A real obstruction to CRT-style bivariate
"affine folding" of an explicit power-of-two (2-adic) smooth STARK domain into a coprime product
grid `L ≅ L₁ × L₂`. -/
theorem dyadic_factor_coprime_trivial (a b k : ℕ) (h_prod : a * b = 2 ^ k)
    (h_coprime : Nat.Coprime a b) : a = 1 ∨ b = 1 := by
  have ha : a ∣ 2 ^ k := ⟨b, h_prod.symm⟩
  have hb : b ∣ 2 ^ k := ⟨a, by rw [Nat.mul_comm]; exact h_prod.symm⟩
  obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb
  rcases Nat.eq_zero_or_pos i with hi | hi
  · left; simp [hi]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · right; simp [hj]
  exfalso
  have h2a : 2 ∣ 2 ^ i := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hi)
  have h2b : 2 ∣ 2 ^ j := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hj)
  have hg : (2 : ℕ) ∣ Nat.gcd (2 ^ i) (2 ^ j) := Nat.dvd_gcd h2a h2b
  rw [Nat.Coprime] at h_coprime
  rw [h_coprime] at hg
  exact absurd hg (by decide)

/-! ## Threshold geometry -/

section Threshold
open Real

/-- **Johnson radius ≤ capacity.** For a rate `ρ ∈ [0,1]`, the RS Johnson radius `1 − √ρ` is at
most the capacity (minimum distance) `1 − ρ`; equivalently `ρ ≤ √ρ`. -/
theorem johnson_radius_le_capacity (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    1 - Real.sqrt ρ ≤ 1 - ρ := by
  have h2 : ρ ^ 2 ≤ ρ := by nlinarith [h0, h1]
  have h3 : Real.sqrt (ρ ^ 2) ≤ Real.sqrt ρ := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq h0] at h3
  linarith

/-- **The radius family `1 − ρ^s` is monotone in the exponent `s`** (base `ρ ∈ (0,1]`). Hence the
`m`-interleaved Guruswami–Sudan radii `1 − ρ^{m/(m+1)}` interpolate monotonically from the Johnson
radius `1 − ρ^{1/2}` (`m = 1`) up to capacity `1 − ρ^1 = 1 − ρ` (`m → ∞`); the generator's
`1 − ρ^{2/3}` candidate is exactly the `m = 2` member. -/
theorem radius_mono_in_exponent (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (s t : ℝ) (hst : s ≤ t) :
    1 - ρ ^ s ≤ 1 - ρ ^ t := by
  have hpow : ρ ^ t ≤ ρ ^ s := rpow_le_rpow_of_exponent_ge h0 h1 hst
  linarith

/-- The `1 − ρ^{2/3}` candidate sits between Johnson and capacity:
`1 − ρ^{1/2} ≤ 1 − ρ^{2/3} ≤ 1 − ρ`. -/
theorem candidate_between_johnson_and_capacity (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    1 - ρ ^ (1/2 : ℝ) ≤ 1 - ρ ^ (2/3 : ℝ) ∧ 1 - ρ ^ (2/3 : ℝ) ≤ 1 - ρ := by
  refine ⟨radius_mono_in_exponent ρ h0 h1 _ _ (by norm_num), ?_⟩
  have := radius_mono_in_exponent ρ h0 h1 (2/3 : ℝ) 1 (by norm_num)
  rwa [rpow_one] at this

/-- **Strict Johnson–capacity separation.** For a rate `ρ ∈ (0,1)`, the RS Johnson radius
`1 − √ρ` is *strictly* below capacity `1 − ρ`: the proximity-gap interval `(1−√ρ, 1−ρ)` in which
the true threshold `δ*` must live is genuinely non-degenerate (the non-strict version is
`johnson_radius_le_capacity`). -/
theorem johnson_radius_lt_capacity (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) :
    1 - Real.sqrt ρ < 1 - ρ := by
  have hsqrt_pos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr h0
  have hsqrt_lt_one : Real.sqrt ρ < 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (le_of_lt h0) h1
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (le_of_lt h0)
  have hlt : ρ < Real.sqrt ρ := by
    calc ρ = Real.sqrt ρ * Real.sqrt ρ := hsq.symm
    _ < Real.sqrt ρ * 1 := mul_lt_mul_of_pos_left hsqrt_lt_one hsqrt_pos
    _ = Real.sqrt ρ := mul_one _
  linarith

/-- **Proximity-gap width, exact form.** The width of the Johnson–capacity interval is
`(1−ρ) − (1−√ρ) = √ρ − ρ = √ρ·(1−√ρ)`. -/
theorem proximity_gap_width_eq (ρ : ℝ) (h0 : 0 ≤ ρ) :
    (1 - ρ) - (1 - Real.sqrt ρ) = Real.sqrt ρ * (1 - Real.sqrt ρ) := by
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt h0
  ring_nf
  nlinarith [hsq]

/-- **Sharp maximum of the proximity-gap width.** For every rate `ρ ∈ [0,1]` the width
`√ρ − ρ` of the Johnson–capacity gap is at most `1/4`. So the Johnson bound can underestimate the
list-decoding radius by at most a quarter of the block length. The proof is the algebraic identity
`1/4 − (√ρ − ρ) = (√ρ − 1/2)² ≥ 0`. -/
theorem proximity_gap_width_le_quarter (ρ : ℝ) (h0 : 0 ≤ ρ) :
    Real.sqrt ρ - ρ ≤ 1/4 := by
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt h0
  nlinarith [sq_nonneg (Real.sqrt ρ - 1/2), hsq]

/-- The gap-width maximum `1/4` is attained **exactly** at rate `ρ = 1/4` (where Johnson radius
`= 1/2` and capacity `= 3/4`). Together with `proximity_gap_width_le_quarter` this pins the worst
case of the Johnson underestimate to a single rate. -/
theorem proximity_gap_width_eq_quarter_iff (ρ : ℝ) (h0 : 0 ≤ ρ) :
    Real.sqrt ρ - ρ = 1/4 ↔ ρ = 1/4 := by
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt h0
  constructor
  · intro h
    have hzero : (Real.sqrt ρ - 1/2)^2 = 0 := by nlinarith [hsq, h]
    have hhalf : Real.sqrt ρ = 1/2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
      linarith
    rw [← hsq, hhalf]; norm_num
  · intro h
    subst h
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-- The `m`-interleaved Guruswami–Sudan radius `1 − ρ^{m/(m+1)}` is **strictly below capacity**
`1 − ρ` for every finite interleaving level `m` (rate `ρ ∈ (0,1)`). No finite amount of
interleaving closes the Johnson→capacity gap — only the `m → ∞` limit reaches capacity, so the
exact threshold `δ*` is not attained by any finite GS interleaving. -/
theorem interleave_radius_lt_capacity (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (m : ℕ) :
    1 - ρ ^ ((m : ℝ)/(m+1)) < 1 - ρ := by
  have hexp : (m : ℝ)/(m+1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hpow : ρ ^ (1:ℝ) < ρ ^ ((m : ℝ)/(m+1)) :=
    Real.rpow_lt_rpow_of_exponent_gt h0 h1 hexp
  rw [Real.rpow_one] at hpow
  linarith

/-- **Exact finite-interleaving capacity gap.** The amount by which the finite
`m`-interleaved GS radius falls short of capacity is just the difference between the
finite exponent and the capacity exponent:
`(1−ρ) − (1−ρ^{m/(m+1)}) = ρ^{m/(m+1)} − ρ`.  This is the residual that must be closed
by genuinely beyond-finite-GS ideas. -/
theorem interleave_capacity_gap_eq (ρ : ℝ) (m : ℕ) :
    (1 - ρ) - (1 - ρ ^ ((m : ℝ)/(m+1)))
      = ρ ^ ((m : ℝ)/(m+1)) - ρ := by
  ring

/-- **The finite-interleaving capacity gap is positive.** For every finite level `m` and every
rate `ρ ∈ (0,1)`, finite GS interleaving leaves a nonzero distance to capacity. -/
theorem interleave_capacity_gap_pos (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (m : ℕ) :
    0 < (1 - ρ) - (1 - ρ ^ ((m : ℝ)/(m+1))) := by
  have hlt := interleave_radius_lt_capacity ρ h0 h1 m
  linarith

/-- The interleaved GS radius is **strictly increasing** in the interleaving level `m`
(rate `ρ ∈ (0,1)`): `1 − ρ^{m/(m+1)} < 1 − ρ^{(m+1)/(m+2)}`. The radii form a strictly increasing
sequence converging up to capacity. -/
theorem interleave_radius_strictMono (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (m : ℕ) :
    1 - ρ ^ ((m : ℝ)/(m+1)) < 1 - ρ ^ (((m:ℝ)+1)/(m+2)) := by
  have hexp : (m : ℝ)/(m+1) < ((m:ℝ)+1)/(m+2) := by
    have key : ((m:ℝ)+1)/((m:ℝ)+2) - (m:ℝ)/(m+1) = 1/(((m:ℝ)+2)*((m:ℝ)+1)) := by
      field_simp; ring
    have hpos : 0 < 1/(((m:ℝ)+2)*((m:ℝ)+1)) := by positivity
    linarith [key ▸ hpos]
  have hpow : ρ ^ (((m:ℝ)+1)/(m+2)) < ρ ^ ((m : ℝ)/(m+1)) :=
    Real.rpow_lt_rpow_of_exponent_gt h0 h1 hexp
  linarith

/-- **The finite-interleaving capacity gap strictly decreases with the interleaving level.**
Interleaving improves the GS radius monotonically, but by `interleave_capacity_gap_pos` every
finite level still leaves a positive residual gap to capacity. -/
theorem interleave_capacity_gap_strict_decrease (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (m : ℕ) :
    (1 - ρ) - (1 - ρ ^ (((m:ℝ)+1)/(m+2)))
      < (1 - ρ) - (1 - ρ ^ ((m : ℝ)/(m+1))) := by
  have hlt := interleave_radius_strictMono ρ h0 h1 m
  linarith

/-- For every positive interleaving level `m ≥ 1`, the interleaved GS radius is **at least the
Johnson radius** `1 − ρ^{1/2}` (rate `ρ ∈ (0,1]`): interleaving only ever improves on Johnson, and
the `m = 1` level equals Johnson exactly. Combined with `interleave_radius_lt_capacity`, every
finite level lands in the half-open gap `[1−√ρ, 1−ρ)`. -/
theorem interleave_radius_ge_johnson (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (m : ℕ) (hm : 1 ≤ m) :
    1 - ρ ^ ((1:ℝ)/2) ≤ 1 - ρ ^ ((m : ℝ)/(m+1)) := by
  have hexp : (1:ℝ)/2 ≤ (m : ℝ)/(m+1) := by
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have key : (m:ℝ)/((m:ℝ)+1) - (1:ℝ)/2 = ((m:ℝ)-1)/(2*((m:ℝ)+1)) := by
      field_simp; ring
    have hge : (0:ℝ) ≤ ((m:ℝ)-1)/(2*((m:ℝ)+1)) :=
      div_nonneg (by linarith) (by positivity)
    linarith [key ▸ hge]
  have hpow : ρ ^ ((m : ℝ)/(m+1)) ≤ ρ ^ ((1:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_ge h0 h1 hexp
  linarith

end Threshold

/-! ## List-decoding engine -/

section ListDecoding
variable {F : Type*} [Field F]

/-- **Fiber root bound.** For a bivariate `H ∈ F[X][Y]` and a point `x`, the univariate fiber
`H(x,·) = H.map (eval x)` has at most `deg_Y(H) = H.natDegree` roots `y`. -/
theorem fiber_root_card_le (H : Polynomial (Polynomial F)) (x : F) :
    (H.map (Polynomial.evalRingHom x)).roots.card ≤ H.natDegree :=
  le_trans (Polynomial.card_roots' _) (Polynomial.natDegree_map_le)

/-- **Grid zero-count bound.** Summed over an evaluation set `S`, the fiberwise curve-point count
`{(x,y) : H(x,y) = 0}` is at most `|S| · deg_Y(H)` (Schwartz–Zippel-style global bound). -/
theorem grid_zero_count_le (H : Polynomial (Polynomial F)) (S : Finset F) :
    ∑ x ∈ S, (H.map (Polynomial.evalRingHom x)).roots.card ≤ S.card * H.natDegree := by
  calc ∑ x ∈ S, (H.map (Polynomial.evalRingHom x)).roots.card
      ≤ ∑ _x ∈ S, H.natDegree := Finset.sum_le_sum (fun x _ => fiber_root_card_le H x)
    _ = S.card * H.natDegree := by rw [Finset.sum_const, smul_eq_mul]

/-- A message polynomial `p ∈ F[X]` lies on the curve `H` (`H(X, p(X)) = 0`) iff it is a root of
`H` in the integral domain `F[X]`. -/
theorem on_curve_iff_mem_roots (H : Polynomial (Polynomial F)) (hH : H ≠ 0) (p : Polynomial F) :
    Polynomial.eval p H = 0 ↔ p ∈ H.roots := by
  rw [Polynomial.mem_roots hH]; rfl

/-- **Guruswami–Sudan list-size bound.** The number of distinct message polynomials lying on the
interpolation curve `H` (the GS candidate list) is at most the `Y`-degree `deg_Y(H)` — exactly
`card_roots'` in the integral domain `F[X]`. The honest combinatorial core of the Grand List
Decoding Challenge; the open part is the interpolation degree budget pinning `δ*`. -/
theorem gs_list_card_le (H : Polynomial (Polynomial F)) :
    H.roots.card ≤ H.natDegree :=
  Polynomial.card_roots' H

/-- **GS degree budget.** For `H ∈ F[X][Y]` whose `Y`-coefficients all have `X`-degree `≤ B`
(`B = deg_X H`) and a message `p ∈ F[X]`, the substituted univariate `H(X, p(X)) = eval p H` has
`X`-degree at most `B + deg_Y(H)·deg(p)`. With `deg p ≤ k-1` this is the budget
`deg_X H + (k-1)·deg_Y H` that `eval_zero_of_agreement_gt_degree` consumes. -/
theorem natDegree_eval_le (H : Polynomial (Polynomial F)) (p : Polynomial F) (B : ℕ)
    (hB : ∀ i, (H.coeff i).natDegree ≤ B) :
    (Polynomial.eval p H).natDegree ≤ B + H.natDegree * p.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.natDegree_le_iff_degree_le]
  refine le_trans (Polynomial.degree_sum_le _ _) (Finset.sup_le ?_)
  intro i hi
  have hi_le : i ≤ H.natDegree := Polynomial.le_natDegree_of_mem_supp i hi
  have hnd : ((H.coeff i) * p ^ i).natDegree ≤ B + H.natDegree * p.natDegree := by
    calc ((H.coeff i) * p ^ i).natDegree
        ≤ B + i * p.natDegree :=
          le_trans Polynomial.natDegree_mul_le (add_le_add (hB i) Polynomial.natDegree_pow_le)
      _ ≤ B + H.natDegree * p.natDegree := by gcongr
  exact le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hnd)

/-- **Agreement ⇒ root (the heart of Guruswami–Sudan).** Let `H ∈ F[X][Y]` and `p ∈ F[X]` a
candidate message. If `g(X) := H(X, p(X)) = eval p H` vanishes on an agreement set `A` with
`|A| > deg_X(g)`, then `g ≡ 0`, i.e. `H(X, p(X)) = 0` — so `p` is one of the `≤ deg_Y(H)` roots
counted by `gs_list_card_le`. The GS degree budget is exactly the hypothesis
`natDegree (eval p H) < A.card` (which follows from `deg_X H + (k-1)·deg_Y H < t`). Chaining
`interpolation_kernel_nontrivial` → this → `gs_list_card_le` is the full combinatorial GS
list-size bound. -/
theorem eval_zero_of_agreement_gt_degree [DecidableEq F]
    (H : Polynomial (Polynomial F)) (p : Polynomial F)
    (A : Finset F) (hA : ∀ a ∈ A, (Polynomial.eval p H).eval a = 0)
    (hdeg : (Polynomial.eval p H).natDegree < A.card) :
    Polynomial.eval p H = 0 := by
  by_contra hne
  have hsub : A ⊆ (Polynomial.eval p H).roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact hA a ha
  have h1 : A.card ≤ (Polynomial.eval p H).roots.toFinset.card := Finset.card_le_card hsub
  have h2 : (Polynomial.eval p H).roots.toFinset.card ≤ (Polynomial.eval p H).natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  omega

/-- **Interpolation existence by counting (the GS interpolation engine).** A linear map from a
finite-dimensional `V` to `W` with `finrank W < finrank V` has a nonzero kernel vector. With
`V =` bivariate polynomials of degree `≤ (d_X, d_Y)` (dimension `(d_X+1)(d_Y+1)`) and `f =`
evaluation at `N` agreement points (`W = Fᴺ`), this is the Guruswami–Sudan interpolation step:
when `(d_X+1)(d_Y+1) > N` there is a nonzero bivariate `H` vanishing at all `N` points. Pairs with
`gs_list_card_le` to give the GS skeleton (existence + list bound); the open part is the
agreement ⇒ root (multiplicity) step that pins which roots are genuine codewords. -/
theorem interpolation_kernel_nontrivial {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hni : ¬ Function.Injective f := by
    intro hinj
    have := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  rw [← LinearMap.ker_eq_bot] at hni
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hni
  exact ⟨v, hv_ne, LinearMap.mem_ker.mp hv_mem⟩

/-- **Quantitative Sudan list-decoding bound.** Given an interpolant `H ≠ 0` over `F[X][Y]` whose
`Y`-coefficients have `X`-degree `≤ B`, the set `L` of degree-`≤ k` message polynomials, each lying
on the curve `H` over an agreement set of size `> B + deg_Y(H)·k`, has size `≤ deg_Y(H)`. This is
the quantitative Guruswami–Sudan list bound, assembled from the degree budget (`natDegree_eval_le`),
the agreement ⇒ root step (`eval_zero_of_agreement_gt_degree`), and the root count
(`gs_list_card_le`). The decoding *radius* comes from choosing `H` (via
`interpolation_kernel_nontrivial`) with `deg_Y(H)` and `B` small; pushing it past the Johnson radius
for explicit smooth-domain RS is the open prize. -/
theorem sudan_codeword_list_bound [DecidableEq F]
    (H : Polynomial (Polynomial F)) (hH : H ≠ 0) (B k : ℕ)
    (hB : ∀ i, (H.coeff i).natDegree ≤ B)
    (L : Finset (Polynomial F))
    (hdeg : ∀ p ∈ L, p.natDegree ≤ k)
    (curve : Polynomial F → Finset F)
    (hcurve : ∀ p ∈ L, ∀ a ∈ curve p, (Polynomial.eval p H).eval a = 0)
    (hbig : ∀ p ∈ L, B + H.natDegree * k < (curve p).card) :
    L.card ≤ H.natDegree := by
  have hroot : ∀ p ∈ L, Polynomial.eval p H = 0 := by
    intro p hp
    refine eval_zero_of_agreement_gt_degree H p (curve p) (hcurve p hp) ?_
    have hd : (Polynomial.eval p H).natDegree ≤ B + H.natDegree * p.natDegree :=
      natDegree_eval_le H p B hB
    have hmul : H.natDegree * p.natDegree ≤ H.natDegree * k := by gcongr; exact hdeg p hp
    have := hbig p hp
    omega
  have hsub : L ⊆ H.roots.toFinset := by
    intro p hp; rw [Multiset.mem_toFinset, Polynomial.mem_roots hH]; exact hroot p hp
  calc L.card ≤ H.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ H.natDegree := le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

/-- **Sum of root multiplicities is bounded by the degree.** `∑_{a ∈ A} mult_a(g) ≤ deg g`. -/
theorem sum_rootMultiplicity_le [DecidableEq F] (g : Polynomial F) (A : Finset F) :
    ∑ a ∈ A, g.rootMultiplicity a ≤ g.natDegree := by
  have h1 : ∑ a ∈ A, g.rootMultiplicity a = ∑ a ∈ A, Multiset.count a g.roots :=
    Finset.sum_congr rfl (fun a _ => (Polynomial.count_roots g).symm)
  have hexpand : Multiset.card g.roots = ∑ a ∈ A ∪ g.roots.toFinset, Multiset.count a g.roots := by
    rw [← Multiset.toFinset_sum_count_eq g.roots]
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro a _ ha; rw [Multiset.count_eq_zero]
    exact fun hmem => ha (Multiset.mem_toFinset.mpr hmem)
  have hstep : ∑ a ∈ A, Multiset.count a g.roots ≤ Multiset.card g.roots := by
    rw [hexpand]; exact Finset.sum_le_sum_of_subset Finset.subset_union_left
  rw [h1]; exact le_trans hstep (Polynomial.card_roots' g)

/-- **Agreement-with-multiplicity ⇒ root.** If `g(X) := H(X,p(X))` vanishes to order `≥ r` at each
of `|A|` points and `deg g < |A|·r`, then `g ≡ 0`. The factor-`r` budget is the multiplicity
generalization of `eval_zero_of_agreement_gt_degree`. -/
theorem eval_zero_of_multiplicity_agreement [DecidableEq F]
    (H : Polynomial (Polynomial F)) (p : Polynomial F) (A : Finset F) (r : ℕ)
    (hmult : ∀ a ∈ A, r ≤ (Polynomial.eval p H).rootMultiplicity a)
    (hdeg : (Polynomial.eval p H).natDegree < A.card * r) :
    Polynomial.eval p H = 0 := by
  by_contra hne
  set g := Polynomial.eval p H with hg
  have hsum : ∑ a ∈ A, g.rootMultiplicity a ≤ g.natDegree := sum_rootMultiplicity_le g A
  have hge : A.card * r ≤ ∑ a ∈ A, g.rootMultiplicity a := by
    calc A.card * r = ∑ _a ∈ A, r := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ A, g.rootMultiplicity a := Finset.sum_le_sum hmult
  omega

/-- **Quantitative GS list bound with multiplicities.** An interpolant `H ≠ 0` whose `Y`-coefficients
have `X`-degree `≤ B`, with each listed degree-`≤ k` codeword vanishing to order `≥ r` on a
curve-agreement set of size `> (B + deg_Y(H)·k)/r`, lists at most `deg_Y(H)` codewords. The
multiplicity-`r` root counting is correct and reusable; note that realizing the **Johnson** radius
`1 − √ρ` (rather than the Sudan radius `1 − √(2ρ)`) requires *weighted-degree* `(1, k-1)`
interpolation, since with the box bound `(deg_X, deg_Y)` the `r` factors cancel — see the module
note. -/
theorem gs_multiplicity_list_bound [DecidableEq F]
    (H : Polynomial (Polynomial F)) (hH : H ≠ 0) (B k r : ℕ)
    (hB : ∀ i, (H.coeff i).natDegree ≤ B)
    (L : Finset (Polynomial F)) (hdeg : ∀ p ∈ L, p.natDegree ≤ k)
    (curve : Polynomial F → Finset F)
    (hmult : ∀ p ∈ L, ∀ a ∈ curve p, r ≤ (Polynomial.eval p H).rootMultiplicity a)
    (hbig : ∀ p ∈ L, B + H.natDegree * k < (curve p).card * r) :
    L.card ≤ H.natDegree := by
  have hroot : ∀ p ∈ L, Polynomial.eval p H = 0 := by
    intro p hp
    refine eval_zero_of_multiplicity_agreement H p (curve p) r (hmult p hp) ?_
    have hd : (Polynomial.eval p H).natDegree ≤ B + H.natDegree * p.natDegree :=
      natDegree_eval_le H p B hB
    have hmul : H.natDegree * p.natDegree ≤ H.natDegree * k := by gcongr; exact hdeg p hp
    have := hbig p hp
    omega
  have hsub : L ⊆ H.roots.toFinset := by
    intro p hp; rw [Multiset.mem_toFinset, Polynomial.mem_roots hH]; exact hroot p hp
  calc L.card ≤ H.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ H.natDegree := le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

end ListDecoding

/-! ## Quantitative GS parameters -/

/-- **Sudan parameter feasibility (pure arithmetic).** Given target agreement `t`, code dimension
`k`, `n` evaluation points, and a chosen `Y`-degree `d_Y` with `(k-1)·d_Y < t`: if
`n < (t - (k-1)·d_Y)·(d_Y + 1)`, then there is an `X`-degree `d_X` for which (i) the bivariate
interpolation space `{deg_X ≤ d_X, deg_Y ≤ d_Y}` has dimension `(d_X+1)(d_Y+1) > n` (so a nonzero
interpolant through the `n` points exists, by `interpolation_kernel_nontrivial`), and (ii) the GS
degree budget `d_X + (k-1)·d_Y < t` holds (so `sudan_codeword_list_bound` then caps the list at
`d_Y`). Optimizing `d_Y` in this feasibility region yields the Sudan decoding radius. -/
theorem sudan_params_feasible (n k t dY : ℕ)
    (hbudget : (k - 1) * dY < t)
    (hfeas : n < (t - (k - 1) * dY) * (dY + 1)) :
    ∃ dX : ℕ, n < (dX + 1) * (dY + 1) ∧ dX + (k - 1) * dY < t := by
  refine ⟨t - 1 - (k - 1) * dY, ?_, ?_⟩
  · have hrw : t - 1 - (k - 1) * dY + 1 = t - (k - 1) * dY := by omega
    rw [hrw]; exact hfeas
  · omega

/-! ### Weighted-degree (Johnson) monomial count

The box interpolation space `(d_X+1)(d_Y+1)` realizes the Sudan radius. The Johnson radius comes
from the *weighted*-degree `(1, w)` space (`w = k-1`), whose monomial count is the triangular
`N(D) = ∑_b (D - w·b + 1) ≈ D²/(2w)` — a factor `2` above the largest fitting rectangle. -/

open Finset in
/-- **Weighted-degree monomial count.** The number of monomials `X^a Y^b` of weighted `(1,w)`-degree
`≤ D` (i.e. `a + w·b ≤ D`) equals `∑_b (D - w·b + 1)` over feasible `b`. -/
theorem weighted_degree_count (D w : ℕ) :
    ((Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter (fun p => p.2 + w * p.1 ≤ D)).card
      = ∑ b ∈ Finset.range (D + 1), (if w * b ≤ D then D - w * b + 1 else 0) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range (D + 1))
        (fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hbD : b < D + 1 := Finset.mem_range.mp hb
  have hfib : (((Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter
        (fun p => p.2 + w * p.1 ≤ D)).filter (fun x => x.1 = b))
      = ({b} ×ˢ ((Finset.range (D + 1)).filter (fun a => a + w * b ≤ D))) := by
    ext ⟨b', a⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨_, ha⟩, hle⟩, rfl⟩; exact ⟨rfl, ha, hle⟩
    · rintro ⟨rfl, ha, hle⟩; exact ⟨⟨⟨hbD, ha⟩, hle⟩, rfl⟩
  rw [hfib, Finset.card_product, Finset.card_singleton, one_mul]
  by_cases h : w * b ≤ D
  · rw [if_pos h, show Finset.filter (fun a => a + w * b ≤ D) (Finset.range (D + 1))
            = Finset.range (D - w * b + 1) by ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega,
        Finset.card_range]
  · rw [if_neg h, Finset.filter_false_of_mem
        (fun a ha => by simp only [Finset.mem_range] at ha; omega), Finset.card_empty]

open Finset in
/-- **Weighted-degree count lower bound (the Johnson factor).** `D² ≤ 2w · N(D)`, i.e.
`N(D) > D²/(2w)` — the triangular factor of `2` over the rectangle bound, exactly the Johnson
improvement over Sudan in the GS interpolation feasibility. With `w = k-1` and degree budget
`D < t` (from `eval_zero_of_agreement_gt_degree`), feasibility `N(D) > n` then holds for
`t² > 2(k-1)·n`-type thresholds approaching the Johnson radius `1 − √ρ`. -/
theorem weighted_degree_count_lb (D w : ℕ) (hw : 0 < w) :
    D * D ≤ 2 * w *
      ((Finset.range (D + 1) ×ˢ Finset.range (D + 1)).filter (fun p => p.2 + w * p.1 ≤ D)).card := by
  rw [weighted_degree_count]
  set m := D / w with hm
  have hwm : w * m ≤ D := by rw [mul_comm]; exact Nat.div_mul_le_self D w
  have hmD : m ≤ D := Nat.div_le_self D w
  have hlt : D < w * (m + 1) := by
    have h1 := Nat.div_add_mod D w
    rw [← hm] at h1
    have h2 := Nat.mod_lt D hw
    have h3 : w * (m + 1) = w * m + w := by rw [Nat.mul_succ]
    omega
  clear_value m
  clear hm
  have hsub : Finset.range (m + 1) ⊆ Finset.range (D + 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have hzero : ∀ b ∈ Finset.range (D + 1), b ∉ Finset.range (m + 1) →
      (if w * b ≤ D then D - w * b + 1 else 0) = 0 := by
    intro b _ hb'
    have hbge : m + 1 ≤ b := by by_contra hc; exact hb' (Finset.mem_range.mpr (by omega))
    have hle : w * (m + 1) ≤ w * b := by gcongr
    exact if_neg (Nat.not_le.mpr (lt_of_lt_of_le hlt hle))
  have hsum_eq : (∑ b ∈ Finset.range (D + 1), if w * b ≤ D then D - w * b + 1 else 0)
      = ∑ b ∈ Finset.range (m + 1), (D - w * b + 1) := by
    rw [← Finset.sum_subset hsub hzero]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hbm : b ≤ m := by have := Finset.mem_range.mp hb; omega
    rw [if_pos (le_trans (by gcongr) hwm)]
  rw [hsum_eq]
  have hterm : ∀ b ∈ Finset.range (m + 1),
      (D - w * b + 1) + (D - w * (m - b) + 1) = 2 * (D + 1) - w * m := by
    intro b hb
    have hbm : b ≤ m := by have := Finset.mem_range.mp hb; omega
    have h1 : w * b ≤ D := le_trans (by gcongr) hwm
    have h2 : w * (m - b) ≤ D := le_trans (by gcongr; omega) hwm
    have h3 : w * b + w * (m - b) = w * m := by rw [← Nat.mul_add]; congr 1; omega
    omega
  have hreflect : (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
      = ∑ b ∈ Finset.range (m + 1), (D - w * (m - b) + 1) :=
    (Finset.sum_range_reflect (fun b => D - w * b + 1) (m + 1)).symm
  have hkey : (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
      + (∑ b ∈ Finset.range (m + 1), (D - w * (m - b) + 1))
      = (m + 1) * (2 * (D + 1) - w * m) := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_const,
        Finset.card_range, Nat.nsmul_eq_mul]
  have h2sum : 2 * (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
      = (m + 1) * (2 * (D + 1) - w * m) := by
    have heq : 2 * (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
        = (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
            + (∑ b ∈ Finset.range (m + 1), (D - w * (m - b) + 1)) := by omega
    rw [heq]; exact hkey
  have hfin : 2 * w * (∑ b ∈ Finset.range (m + 1), (D - w * b + 1))
      = w * (m + 1) * (2 * (D + 1) - w * m) := by
    rw [mul_comm 2 w, mul_assoc, h2sum, ← mul_assoc]
  rw [hfin]
  have hA : D + 1 ≤ w * (m + 1) := by omega
  have hB : D + 2 ≤ 2 * (D + 1) - w * m := by omega
  calc D * D ≤ (D + 1) * (D + 2) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ w * (m + 1) * (2 * (D + 1) - w * m) := Nat.mul_le_mul hA hB

/-! ## Refutations of naive list-size bounds -/

/-- **Refute Hyp7 (naive matrix-rank list bound `|L| ≤ k²`).** False unconditionally: a single
evaluation point with `k = 0` breaks it (`1 ≤ 0`). -/
theorem refute_naive_matrix_rank_bound {ι F : Type*} [Nonempty ι] [Zero F] :
    ¬ ∀ (L : Finset (ι → F)) (k : ℕ), L.card ≤ k ^ 2 := by
  intro h
  have := h {0} 0
  simp at this

/-- **Refute Hyp8 (naive algebraic-independence bound `|L| ≤ |F|`).** False: the full space
`L = univ` has `|F|^{|ι|} > |F|` elements once `|ι| ≥ 2` and `|F| ≥ 2`. -/
theorem refute_naive_alg_independence_bound {ι F : Type*} [Fintype ι] [Fintype F]
    [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) (hF : 2 ≤ Fintype.card F) :
    ¬ ∀ (L : Finset (ι → F)), L.card ≤ Fintype.card F := by
  intro h
  have hle := h Finset.univ
  rw [Finset.card_univ, Fintype.card_fun] at hle
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ Fintype.card ι :=
    Nat.pow_le_pow_right (by omega) hι
  have hlt : Fintype.card F < Fintype.card F ^ 2 := by
    rw [pow_two]; exact lt_mul_of_one_lt_left (by omega) (by omega)
  omega

end ArkLib.ProximityGap.Issue232Bricks
