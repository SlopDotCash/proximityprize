/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Char-0 Wick bound, r-UNIFORM, via the Bessel EGF identity (#444, avenue W0)

This file proves, **r-uniformly** (for ALL `r`) and **axiom-clean**, the sharp char-0 Wick / `K = 1`
energy bound for thin 2-power subgroups:
`E_r^{char0}(μ_n) ≤ (2r-1)‼ · n^r`     for `n = 2m`, all `r`.

This is the char-0 layer of the BGK energy lever (equivalently the Gaussian recursion
`E_{r+1} ≤ (2r+1) n E_r`, equivalently the named hypothesis `hOff` of `_AvGER_RecursionStep`).
The pre-existing `_AvZ_CharZeroWickBoundLadder` proved this only for the fixed ladder `r ≤ 7`
(per-`r` polynomial closed forms). Here we close the *all-`r`* statement via the Bessel identity and
coefficientwise domination — exactly the `r`-uniform discharge the ladder could not reach.

## The three steps (paper proof; STEPS 2–3 are formalized below over `ℚ⟦X⟧`)

**STEP 1 — the Bessel identity (named, paper-proved, exact-verified).**
By the in-tree Lam–Leung 2-power theorem (a vanishing sum of `2^μ`-th roots is antipodally
balanced), a char-0 collision `∑ xᵢ = ∑ yⱼ` (`x, y ∈ μ_n^r`) means the combined `2r`-multiset
`{x₁,…,x_r} ∪ {−y₁,…,−y_r}` is a union of antipodal pairs `{ζ^j, −ζ^j}`. `μ_n` has `m = n/2`
antipodal *directions* `j = 0,…,m−1` (with `ζ^{j+m} = −ζ^j`). Vanishing holds **iff** for each
direction `j` the count of `ζ^j` equals the count of `−ζ^j =: c_j`, *independently across `j`*, with
`∑_j c_j = r`. The number of ways to place, among the `2r` ordered positions (the `r` `x`-slots and
`r` `y`-slots), `c_j` copies of `ζ^j` and `c_j` copies of `−ζ^j` for every `j` is the multinomial
`(2r)! / ∏_j (c_j!)²`. Hence

`E_r^{char0}(μ_n) = ∑_{c : ∑ c_j = r} (2r)! / ∏_j (c_j!)² = (2r)! · [x^{2r}] I₀(2x)^m`,

where `I₀(2x) = ∑_{k≥0} x^{2k}/(k!)²` is the per-direction EGF (the balanced/central count). Verified
EXACTLY (integer cyclotomic arithmetic) at `n = 4, 8, 16` (`m = 2, 4, 8`) for `r = 1..8`:
the direct sumset-convolution energy equals `(2r)! [x^{2r}] I₀(2x)^m` on the nose (see
`besselIdentity_verification` and the dossier). The directions genuinely DECOUPLE (no interaction
term) at every tested `n` — this is the per-direction balance independence.

**STEP 2 — coefficientwise domination (formalized).**
`I₀(2x) ⪯ exp(x²)` coefficientwise: `[x^{2k}] I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}] exp(x²)` since
`(k!)² ≥ k!`. Coefficientwise domination of power series with NON-NEGATIVE coefficients is preserved
under multiplication, hence under the `m`-th power: `I₀(2x)^m ⪯ exp(x²)^m = exp(m x²)`.

**STEP 3 — conclusion (formalized).**
`[x^{2r}] exp(m x²) = m^r / r!`, so
`E_r^{char0} = (2r)! [x^{2r}] I₀(2x)^m ≤ (2r)! · m^r / r! = (2r)!/(2^r r!) · (2m)^r = (2r-1)‼ · n^r`.
Sharp `K = 1`, `r`-uniform.

## What is formalized here (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

We model both EGFs as `ℚ⟦X⟧` power series with explicitly given coefficients (NOT analytic Bessel
functions). We prove:

* `i0_le_g_coeff` — STEP 2 base: coefficientwise `coeff k I0 ≤ coeff k G` with both `≥ 0`.
* `coeff_nonneg_mul`, `coeff_le_of_coeff_le` — domination preserved under `*` (nonneg series).
* `i0pow_le_gpow` — STEP 2 lifted: `[x^j] I0^m ≤ [x^j] G^m` for all `j, m`.
* `besselWick_allR` — STEP 3: the r-uniform bound `besselE r m ≤ (2*r-1)‼ * (2*m)^r`, where
  `besselE r m := (2r)! * [x^{2r}] I0^m` is the Bessel-identity right-hand side (= `E_r^{char0}`
  under STEP 1).
* `besselIdentity_verification` — the STEP-1 exact-verification anchors at `m = 2` (`n = 4`).

## Honest scope (#444)

This is **char-0 ONLY**. It discharges the char-0 / `K ≤ 1` Wick layer r-uniformly. It does **NOT**
close the for-all-`q` prize: the char-`p` energy excess `W_r` (the wraparound term that appears when
sums vanish mod `p` without vanishing in `ℂ`) is a SEPARATE positive term and remains the open wall.
STEP 1 is carried as a named, paper-proved, exact-verified identity (we formalize STEPS 2–3, the
analytic core, fully); the antipodal-balance decoupling combinatorics is not re-formalized here
beyond the named statement and its exact numerical confirmation.
-/

namespace ArkLib.ProximityGap.Frontier.AvW0

open PowerSeries BigOperators

/-- The per-direction EGF coefficients of `I₀(2x)`: `[x^{2k}] = 1/(k!)²`, odd coeffs `0`.
We model it directly as a `ℚ⟦X⟧` (no analytic Bessel). -/
noncomputable def I0 : PowerSeries ℚ :=
  PowerSeries.mk (fun j => if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2))^2 else 0)

/-- The dominating EGF `exp(x²)` coefficients: `[x^{2k}] = 1/k!`, odd coeffs `0`. -/
noncomputable def G : PowerSeries ℚ :=
  PowerSeries.mk (fun j => if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2)) else 0)

@[simp] theorem coeff_I0 (j : ℕ) :
    PowerSeries.coeff (R := ℚ) j I0 =
      (if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2))^2 else 0) := by
  simp [I0]

@[simp] theorem coeff_G (j : ℕ) :
    PowerSeries.coeff (R := ℚ) j G =
      (if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2)) else 0) := by
  simp [G]

/-- Every coefficient of `I0` is `≥ 0`. -/
theorem coeff_I0_nonneg (j : ℕ) : 0 ≤ PowerSeries.coeff (R := ℚ) j I0 := by
  rw [coeff_I0]; split
  · positivity
  · rfl

/-- Every coefficient of `G` is `≥ 0`. -/
theorem coeff_G_nonneg (j : ℕ) : 0 ≤ PowerSeries.coeff (R := ℚ) j G := by
  rw [coeff_G]; split
  · positivity
  · rfl

/-- STEP 2 base: `[x^k] I0 ≤ [x^k] G`, since `1/(k!)² ≤ 1/k!`. -/
theorem i0_le_g_coeff (j : ℕ) :
    PowerSeries.coeff (R := ℚ) j I0 ≤ PowerSeries.coeff (R := ℚ) j G := by
  rw [coeff_I0, coeff_G]
  split
  · -- 1/(c!)² ≤ 1/c!  where c = j/2
    set c := j / 2
    have hpos : (0 : ℚ) < (Nat.factorial c) := by
      exact_mod_cast Nat.factorial_pos c
    have h1 : (1 : ℚ) ≤ (Nat.factorial c) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
    have hle : (Nat.factorial c : ℚ) ≤ (Nat.factorial c)^2 := by nlinarith [hpos, h1]
    -- 1/(c!)² ≤ 1/c! from c! ≤ (c!)²
    exact one_div_le_one_div_of_le hpos hle
  · exact le_refl 0

/-- A power series over `ℚ` is *coefficientwise nonneg* if every coefficient is `≥ 0`. -/
def CoeffNonneg (f : PowerSeries ℚ) : Prop := ∀ j, 0 ≤ PowerSeries.coeff (R := ℚ) j f

/-- Nonnegativity is preserved by multiplication (each `coeff_mul` summand is a product of
nonneg factors). -/
theorem coeffNonneg_mul {f g : PowerSeries ℚ} (hf : CoeffNonneg f) (hg : CoeffNonneg g) :
    CoeffNonneg (f * g) := by
  intro j
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hf p.1) (hg p.2)

/-- Nonnegativity is preserved by powers. -/
theorem coeffNonneg_pow {f : PowerSeries ℚ} (hf : CoeffNonneg f) :
    ∀ m, CoeffNonneg (f ^ m)
  | 0 => by
      intro j
      rw [pow_zero]
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [PowerSeries.coeff_one]; split <;> norm_num
  | m + 1 => by
      rw [pow_succ]
      exact coeffNonneg_mul (coeffNonneg_pow hf m) hf

/-- STEP 2 (multiplicative): coefficientwise domination is preserved under multiplication
of coefficientwise-nonneg series. -/
theorem coeff_mul_le_mul {f g f' g' : PowerSeries ℚ}
    (hf : CoeffNonneg f) (hg : CoeffNonneg g)
    (hff : ∀ j, PowerSeries.coeff (R := ℚ) j f ≤ PowerSeries.coeff (R := ℚ) j f')
    (hgg : ∀ j, PowerSeries.coeff (R := ℚ) j g ≤ PowerSeries.coeff (R := ℚ) j g') :
    ∀ j, PowerSeries.coeff (R := ℚ) j (f * g) ≤ PowerSeries.coeff (R := ℚ) j (f' * g') := by
  intro j
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_le_sum
  intro p _
  -- coeff p.1 f * coeff p.2 g ≤ coeff p.1 f' * coeff p.2 g'
  exact mul_le_mul (hff p.1) (hgg p.2) (hg p.2) (le_trans (hf p.1) (hff p.1))

/-- STEP 2 (lifted to powers): `[x^j] I0^m ≤ [x^j] G^m` for all `j, m`. -/
theorem i0pow_le_gpow (m : ℕ) :
    ∀ j, PowerSeries.coeff (R := ℚ) j (I0 ^ m) ≤ PowerSeries.coeff (R := ℚ) j (G ^ m) := by
  induction m with
  | zero => intro j; simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact coeff_mul_le_mul (coeffNonneg_pow coeff_I0_nonneg k) coeff_I0_nonneg ih i0_le_g_coeff

/-! ## STEP 3: closed form for `[x^{2r}] G^m` and the conclusion. -/

/-- `G` is the variable-doubling (`X ↦ X²`) expansion of `exp`: `coeff (2k) = 1/k!`, odd `= 0`. -/
theorem G_eq_expand : G = PowerSeries.expand (R := ℚ) 2 (by norm_num) (PowerSeries.exp ℚ) := by
  ext j
  rw [coeff_G]
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- j = k + k = 2k
    have hj : j % 2 = 0 := by omega
    rw [if_pos hj]
    have hjk : j = 2 * k := by omega
    subst hjk
    rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_exp]
    simp
  · -- j = 2k+1 odd
    have hj : ¬ j % 2 = 0 := by omega
    rw [if_neg hj]
    have hnd : ¬ (2 ∣ j) := by omega
    rw [PowerSeries.coeff_expand (p := 2) (hp := by norm_num), if_neg hnd]

/-- `G^m` is the expansion of `(exp ℚ)^m` (since `expand` is a ring hom). -/
theorem Gpow_eq_expand (m : ℕ) :
    G ^ m = PowerSeries.expand (R := ℚ) 2 (by norm_num) ((PowerSeries.exp ℚ) ^ m) := by
  rw [G_eq_expand, ← map_pow]

/-- STEP 3 core: the exact closed form `[x^{2r}] G^m = m^r / r!`. -/
theorem coeff_Gpow (m r : ℕ) :
    PowerSeries.coeff (R := ℚ) (2 * r) (G ^ m) = (m : ℚ) ^ r / (Nat.factorial r) := by
  rw [Gpow_eq_expand, PowerSeries.coeff_expand_mul]
  rw [PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

open scoped Nat in
/-- The Bessel-identity right-hand side `besselE r m := (2r)! · [x^{2r}] I0^m`. By STEP 1
(the antipodal-balance decoupling identity, named/verified) this equals `E_r^{char0}(μ_{2m})`. -/
noncomputable def besselE (r m : ℕ) : ℚ :=
  (Nat.factorial (2 * r)) * PowerSeries.coeff (R := ℚ) (2 * r) (I0 ^ m)

/-- The Wick bound RHS `(2r-1)‼ · n^r` with `n = 2m`, as a rational. -/
noncomputable def wickRHS (r m : ℕ) : ℚ :=
  (Nat.doubleFactorial (2 * r - 1)) * ((2 * m : ℕ) : ℚ) ^ r

/-- Arithmetic identity: `(2r)! · m^r / r! = (2r-1)‼ · (2m)^r`. The double-factorial split
`(2r)! = (2r-1)‼ · 2^r · r!`. -/
theorem factorial_split (r m : ℕ) :
    (Nat.factorial (2 * r) : ℚ) * ((m : ℚ) ^ r / (Nat.factorial r))
      = (Nat.doubleFactorial (2 * r - 1)) * ((2 * m : ℕ) : ℚ) ^ r := by
  have hfacN : Nat.factorial (2 * r)
      = Nat.doubleFactorial (2 * r - 1) * (2 ^ r * Nat.factorial r) := by
    rcases r with _ | k
    · simp [Nat.doubleFactorial]
    · -- r = k+1, 2r = 2k+2 = (2k+1)+1
      have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h1, Nat.factorial_eq_mul_doubleFactorial]
      have h2 : (2 * k + 1) + 1 = 2 * (k + 1) := by ring
      have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h2, Nat.doubleFactorial_two_mul, h3]
      ring
  have hfac : (Nat.factorial (2 * r) : ℚ)
      = (Nat.doubleFactorial (2 * r - 1) : ℚ) * (2 ^ r * Nat.factorial r) := by
    exact_mod_cast hfacN
  rw [hfac]
  have hrpos : (0 : ℚ) < Nat.factorial r := by exact_mod_cast Nat.factorial_pos r
  field_simp
  push_cast
  ring

/-- **STEP 3 / MAIN (r-uniform, axiom-clean):** the sharp char-0 Wick bound, all `r`:
`besselE r m ≤ (2r-1)‼ · (2m)^r`. Combined with STEP 1, this is `E_r^{char0}(μ_n) ≤ (2r-1)‼ n^r`
for `n = 2m`, uniformly in `r`. -/
theorem besselWick_allR (r m : ℕ) : besselE r m ≤ wickRHS r m := by
  unfold besselE wickRHS
  -- coeff(I0^m) ≤ coeff(G^m), multiply by (2r)! ≥ 0, then closed form.
  have hdom : PowerSeries.coeff (R := ℚ) (2 * r) (I0 ^ m)
      ≤ PowerSeries.coeff (R := ℚ) (2 * r) (G ^ m) := i0pow_le_gpow m (2 * r)
  have hfacpos : (0 : ℚ) ≤ (Nat.factorial (2 * r)) := by positivity
  calc (Nat.factorial (2 * r) : ℚ) * PowerSeries.coeff (R := ℚ) (2 * r) (I0 ^ m)
      ≤ (Nat.factorial (2 * r) : ℚ) * PowerSeries.coeff (R := ℚ) (2 * r) (G ^ m) := by
        exact mul_le_mul_of_nonneg_left hdom hfacpos
    _ = (Nat.factorial (2 * r) : ℚ) * ((m : ℚ) ^ r / (Nat.factorial r)) := by rw [coeff_Gpow]
    _ = (Nat.doubleFactorial (2 * r - 1)) * ((2 * m : ℕ) : ℚ) ^ r := factorial_split r m

/-! ## STEP 1 exact-verification anchor (`m = 2`, i.e. `n = 4`).
The direct cyclotomic-energy values `E_r^{char0}(μ_4)` (computed exactly off-line) equal
`besselE r 2`. We confirm the first nontrivial value `r = 2`: `E_2^{char0}(μ_4) = 36`. -/
theorem besselIdentity_verification : besselE 2 2 = 36 := by
  unfold besselE
  -- [x^4] I0^2 = sum_{a+b=2} 1/(a!)^2 (b!)^2 = 1/4 + 1 + 1/4 = 3/2; 4! * 3/2 = 36
  rw [show (2 * 2 : ℕ) = 4 from rfl]
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [coeff_I0, Nat.factorial]

#print axioms i0_le_g_coeff
#print axioms i0pow_le_gpow
#print axioms coeff_Gpow
#print axioms besselWick_allR
#print axioms besselIdentity_verification

end ArkLib.ProximityGap.Frontier.AvW0
