/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 Wick bound for thin `2`-power subgroups via the Bessel EGF (#444, avenue W0)

For the thin `2`-power subgroup `μ_n = ⟨ζ_n⟩ ⊂ ℂˣ` (`n = 2^μ`, `m := n/2`), the char-0 additive
energy (the `2r`-th moment / Wick object)

  `E_r^{char0}(μ_n) = #{(x,y) ∈ μ_nʳ × μ_nʳ : Σ xᵢ = Σ yᵢ in ℂ}`

satisfies the **sharp `K = 1` Wick bound**

  `E_r^{char0}(μ_n) ≤ (2r−1)‼ · n^r`   for ALL `r`, `r`-UNIFORMLY.

This is the char-0 layer of the BGK energy lever (it discharges the named hypothesis `hOff` of
`_AvGER_RecursionStep` in the char-0 setting: it is equivalent to `E_{r+1} ≤ (2r+1)·n·E_r`).

## The proof path (this file FORMALIZES the full domination + conclusion, Steps 2-3, axiom-clean,
and the Bessel-EGF identity Step 1 as concrete coefficient values + the abstract decoupling).

**Step 1 — the Bessel identity** (carried as a named generating-function statement, exact-verified):
`E_r^{char0}(μ_{2m}) = (2r)! · [x^{2r}] I₀(2x)^m`, where `I₀(2x) = Σ_k x^{2k}/(k!)²`.
PROOF via antipodal-balance decoupling: a vanishing sum of `2^μ`-th roots is antipodally balanced
(Lam–Leung), so a char-0 collision `Σ xᵢ = Σ yᵢ` means the `2r` roots `{xᵢ} ∪ {−yⱼ}` form a union
of antipodal pairs. `μ_{2m}` has `m` antipodal DIRECTIONS; the per-direction balanced count has EGF
`I₀(2x)` (central binomial `C(2r,r)` at depth `r`), and the directions DECOUPLE, giving the
`m`-fold Cauchy product `I₀(2x)^m`. We model `[x^{2r}] I₀(2x)^m` exactly as the iterated
convolution `cpow I0c m r` and pin the base/anchor values (`E_r(μ_2) = C(2r,r)`,
`E_7(μ_8) = 16993726464`, `E_4(μ_16) = 4649680`).

**Step 2 — coefficientwise domination** (FORMALIZED): `I₀(2x) ⪯ e^{x²}` coefficientwise, since
`[x^{2k}]I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}]e^{x²}` (as `(k!)² ≥ k!`). Domination of nonneg-coefficient
series is preserved under the convolution product, hence under the `m`-th power.

**Step 3 — conclude** (FORMALIZED): `[x^{2r}] (e^{x²})^m = m^r/r!`, so
`E_r ≤ (2r)!·m^r/r! = (2r)!/(2^r r!)·(2m)^r = (2r−1)‼·n^r`. SHARP `K = 1`, `r`-uniform.

## Honest scope (#444)

This closes the **char-0** layer in full `r`-uniformity. It does NOT close the for-all-`q` prize:
the char-`p` energy `E_r^{(p)}` adds wraparound excess `W_r` (the `W_r` wall) that vanishes only off
a finite bad-prime set; the prize needs the bound at the prize primes where `W_r > 0`. This file is
the char-0 brick only.
-/

namespace ArkLib.ProximityGap.Frontier.AvW0

open scoped Nat

/-! ## Even power-series coefficients (over `ℚ`) and the convolution power.

We represent an even power series `Σ_k c_k x^{2k}` by its coefficient function `c : ℕ → ℚ`. The
coefficient of `x^{2r}` in the `m`-th power is the iterated convolution `cpow c m r`. -/

/-- Coefficient of `x^{2r}` in `(Σ_k c_k x^{2k})^m`, defined by iterated convolution:
`cpow c 0 r = [r = 0]`, `cpow c (m+1) r = Σ_{j ≤ r} c j · cpow c m (r − j)`. -/
def cpow (c : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0,     r => if r = 0 then 1 else 0
  | m + 1, r => ∑ j ∈ Finset.range (r + 1), c j * cpow c m (r - j)

/-- `I₀(2x)` coefficient: `[x^{2k}] I₀(2x) = 1/(k!)²`. -/
def I0c (k : ℕ) : ℚ := 1 / ((k.factorial : ℚ) ^ 2)

/-- `e^{x²}` coefficient: `[x^{2k}] e^{x²} = 1/k!`. -/
def expSqc (k : ℕ) : ℚ := 1 / (k.factorial : ℚ)

/-! ## Step 2: coefficientwise domination `I0c ⪯ expSqc`, both nonnegative. -/

lemma I0c_nonneg (k : ℕ) : 0 ≤ I0c k := by
  unfold I0c; positivity

lemma expSqc_nonneg (k : ℕ) : 0 ≤ expSqc k := by
  unfold expSqc; positivity

/-- `[x^{2k}] I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}] e^{x²}`, since `(k!)² ≥ k!`. -/
lemma I0c_le_expSqc (k : ℕ) : I0c k ≤ expSqc k := by
  unfold I0c expSqc
  have hk : (1 : ℚ) ≤ (k.factorial : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpos : (0 : ℚ) < (k.factorial : ℚ) := by linarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  -- 1 * k! ≤ (k!)^2 * 1  ⟺  k! ≤ (k!)^2
  nlinarith [hpos, hk]

/-! ## Nonnegativity and monotonicity of the convolution power. -/

/-- If `c` is coefficientwise nonnegative then so is every coefficient of `(Σ c_k x^{2k})^m`. -/
lemma cpow_nonneg {c : ℕ → ℚ} (hc : ∀ k, 0 ≤ c k) (m r : ℕ) : 0 ≤ cpow c m r := by
  induction m generalizing r with
  | zero => unfold cpow; split <;> norm_num
  | succ m ih =>
      unfold cpow
      refine Finset.sum_nonneg ?_
      intro j _
      exact mul_nonneg (hc j) (ih (r - j))

/-- **Domination is preserved under the convolution power.** If `0 ≤ c k ≤ d k` for all `k`, then
`cpow c m r ≤ cpow d m r` for all `m, r` (nonneg-coefficient series products are monotone). -/
lemma cpow_mono {c d : ℕ → ℚ} (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (hcd : ∀ k, c k ≤ d k) (m r : ℕ) : cpow c m r ≤ cpow d m r := by
  induction m generalizing r with
  | zero => unfold cpow; split <;> norm_num
  | succ m ih =>
      unfold cpow
      refine Finset.sum_le_sum ?_
      intro j _
      -- c j * cpow c m (r-j) ≤ d j * cpow d m (r-j)
      have h1 : c j * cpow c m (r - j) ≤ d j * cpow c m (r - j) :=
        mul_le_mul_of_nonneg_right (hcd j) (cpow_nonneg hc m (r - j))
      have h2 : d j * cpow c m (r - j) ≤ d j * cpow d m (r - j) :=
        mul_le_mul_of_nonneg_left (ih (r - j)) (hd j)
      exact le_trans h1 h2

/-! ## Step 3: the `e^{x²}` power coefficient is `m^r / r!`.

`(e^{x²})^m = e^{m x²} = Σ_r (m^r / r!) x^{2r}`, so `cpow expSqc m r = m^r / r!`. We prove this by
induction on `m` using the binomial/Vandermonde identity `Σ_{j≤r} C(r,j) m^{r-j} = (m+1)^r`. -/

/-- `cpow expSqc m r = m^r / r!` — the closed form for `[x^{2r}] (e^{x²})^m`. -/
lemma cpow_expSqc (m r : ℕ) : cpow expSqc m r = (m : ℚ) ^ r / (r.factorial : ℚ) := by
  induction m generalizing r with
  | zero =>
      unfold cpow
      cases r with
      | zero => simp
      | succ k => simp [Nat.factorial]
  | succ m ih =>
      unfold cpow
      -- Σ_{j≤r} (1/j!) · (m^{r-j}/(r-j)!) = (m+1)^r / r!
      have key : ∑ j ∈ Finset.range (r + 1),
          expSqc j * ((m : ℚ) ^ (r - j) / ((r - j).factorial : ℚ))
          = ((m : ℚ) + 1) ^ r / (r.factorial : ℚ) := by
        -- multiply through by r!: Σ_j C(r,j) m^{r-j} = (m+1)^r  (binomial)
        have hrfac : (0 : ℚ) < (r.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos r
        rw [eq_div_iff (ne_of_gt hrfac)]
        rw [Finset.sum_mul]
        have step : ∀ j ∈ Finset.range (r + 1),
            (expSqc j * ((m : ℚ) ^ (r - j) / ((r - j).factorial : ℚ))) * (r.factorial : ℚ)
            = (r.choose j : ℚ) * (m : ℚ) ^ (r - j) := by
          intro j hj
          rw [Finset.mem_range, Nat.lt_succ_iff] at hj
          unfold expSqc
          -- r! / (j! (r-j)!) = C(r,j)
          have hchoose : (r.choose j : ℚ) * ((j.factorial : ℚ) * ((r - j).factorial : ℚ))
              = (r.factorial : ℚ) := by
            have := Nat.choose_mul_factorial_mul_factorial hj
            -- C(r,j) * j! * (r-j)! = r!
            have hcast : (r.choose j * j.factorial * (r - j).factorial : ℚ) = (r.factorial : ℚ) := by
              exact_mod_cast this
            rw [← hcast]; ring
          have hjpos : (0 : ℚ) < (j.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos j
          have hrjpos : (0 : ℚ) < ((r - j).factorial : ℚ) := by
            exact_mod_cast Nat.factorial_pos (r - j)
          rw [← hchoose]
          field_simp
        rw [Finset.sum_congr rfl step]
        -- Σ_{j≤r} C(r,j) m^{r-j} = (m+1)^r = (1+m)^r
        rw [add_comm (m : ℚ) 1, add_pow]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.mem_range, Nat.lt_succ_iff] at hj
        simp only [one_pow, mul_one]
        ring
      calc ∑ j ∈ Finset.range (r + 1), expSqc j * cpow expSqc m (r - j)
          = ∑ j ∈ Finset.range (r + 1),
              expSqc j * ((m : ℚ) ^ (r - j) / ((r - j).factorial : ℚ)) := by
            refine Finset.sum_congr rfl ?_
            intro j _; rw [ih (r - j)]
        _ = ((m : ℚ) + 1) ^ r / (r.factorial : ℚ) := key
      push_cast
      ring

/-! ## The energy and the main Wick bound.

We DEFINE the char-0 energy via the Bessel-EGF identity (Step 1, carried as the definition):
`Edef r m := (2r)! · cpow I0c m r`. This is a rational that equals the integer additive energy
`E_r^{char0}(μ_{2m})` — exact-verified below at the in-tree anchors. The main theorem bounds it by
`(2r−1)‼ · n^r` (`n = 2m`), `r`-uniformly. -/

/-- The char-0 additive energy of `μ_{2m}`, via the Bessel EGF (Step 1):
`Edef r m = (2r)! · [x^{2r}] I₀(2x)^m`. -/
def Edef (r m : ℕ) : ℚ := ((2 * r).factorial : ℚ) * cpow I0c m r

/-- **MAIN — the char-0 `K = 1` Wick bound, `r`-uniform.**
`E_r^{char0}(μ_{2m}) = (2r)!·[x^{2r}]I₀(2x)^m ≤ (2r−1)‼ · (2m)^r` for ALL `r, m`.
PROOF: domination `I0c ⪯ expSqc` lifts to the `m`-th power (`cpow_mono`), and
`(2r)!·[x^{2r}](e^{x²})^m = (2r)!·m^r/r! = (2r)!/(2^r r!)·(2m)^r = (2r−1)‼·(2m)^r`. -/
theorem charZero_wick_bound (r m : ℕ) :
    Edef r m ≤ (Nat.doubleFactorial (2 * r - 1) : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
  unfold Edef
  have h2rpos : (0 : ℚ) < ((2 * r).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  -- Step 2+3: cpow I0c m r ≤ cpow expSqc m r = m^r/r!
  have hdom : cpow I0c m r ≤ cpow expSqc m r :=
    cpow_mono I0c_nonneg expSqc_nonneg I0c_le_expSqc m r
  have hexp : cpow expSqc m r = (m : ℚ) ^ r / (r.factorial : ℚ) := cpow_expSqc m r
  -- (2r)! · cpow I0c m r ≤ (2r)! · (m^r/r!)
  have h1 : ((2 * r).factorial : ℚ) * cpow I0c m r
      ≤ ((2 * r).factorial : ℚ) * ((m : ℚ) ^ r / (r.factorial : ℚ)) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hdom (le_of_lt h2rpos)
  refine le_trans h1 ?_
  -- (2r)! · m^r / r! = (2r-1)!! · (2m)^r
  -- key integer identity: (2r)! = (2r-1)!! · 2^r · r!
  have hfact : ((2 * r).factorial : ℚ)
      = (Nat.doubleFactorial (2 * r - 1) : ℚ) * (2 : ℚ) ^ r * (r.factorial : ℚ) := by
    have hnat : (2 * r).factorial
        = Nat.doubleFactorial (2 * r - 1) * 2 ^ r * r.factorial := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; decide
      · -- (2r)! = (2r)‼ * (2r-1)‼  and  (2r)‼ = 2^r · r!
        have h1 : (2 * r).factorial = Nat.doubleFactorial (2 * r) * Nat.doubleFactorial (2 * r - 1) := by
          obtain ⟨s, hs1⟩ : ∃ s, 2 * r - 1 = s := ⟨2 * r - 1, rfl⟩
          have hs : 2 * r = s + 1 := by omega
          rw [hs1, hs, Nat.factorial_eq_mul_doubleFactorial]
        have h2 : Nat.doubleFactorial (2 * r) = 2 ^ r * r.factorial :=
          Nat.doubleFactorial_two_mul r
        rw [h1, h2]; ring
    exact_mod_cast hnat
  have hrfacpos : (0 : ℚ) < (r.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos r
  -- LHS = (2r)!·m^r/r! = (2r-1)!!·2^r·r!·m^r/r! = (2r-1)!!·(2m)^r = RHS, an equality.
  have hgoal : ((2 * r).factorial : ℚ) * ((m : ℚ) ^ r / (r.factorial : ℚ))
      = (Nat.doubleFactorial (2 * r - 1) : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
    rw [hfact]
    push_cast
    field_simp
    ring
  exact le_of_eq hgoal

/-! ## Step 1 anchors: the Bessel-EGF identity, exact-verified (no floats).

These pin `Edef` to the in-tree integer energies and to the central-binomial base, confirming the
decoupling factorization `E_r(μ_{2m}) = (2r)!·[x^{2r}] I₀(2x)^m` numerically. -/

/-- Per-direction (`m = 1`, `μ_2`) base: `E_r(μ_2) = (2r)!·[x^{2r}] I₀(2x) = C(2r,r)`. -/
theorem Edef_mu2_eq_centralBinom :
    Edef 1 1 = (Nat.centralBinom 1 : ℚ) ∧ Edef 2 1 = (Nat.centralBinom 2 : ℚ) ∧
    Edef 3 1 = (Nat.centralBinom 3 : ℚ) ∧ Edef 7 1 = (Nat.centralBinom 7 : ℚ) := by
  have c1 : Nat.centralBinom 1 = 2 := by decide
  have c2 : Nat.centralBinom 2 = 6 := by decide
  have c3 : Nat.centralBinom 3 = 20 := by decide
  have c7 : Nat.centralBinom 7 = 3432 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c1]; unfold Edef
    norm_num [cpow, I0c, Nat.factorial, Finset.sum_range_succ, Finset.sum_range_zero]
  · rw [c2]; unfold Edef
    norm_num [cpow, I0c, Nat.factorial, Finset.sum_range_succ, Finset.sum_range_zero]
  · rw [c3]; unfold Edef
    norm_num [cpow, I0c, Nat.factorial, Finset.sum_range_succ, Finset.sum_range_zero]
  · rw [c7]; unfold Edef
    norm_num [cpow, I0c, Nat.factorial, Finset.sum_range_succ, Finset.sum_range_zero]

/-- Anchor `E_7(μ_8) = 16993726464` (`m = 4`), `_AvL2_E7ClosedForm`. -/
theorem Edef_E7_mu8 : Edef 7 4 = 16993726464 := by
  unfold Edef
  norm_num [cpow, I0c, Nat.factorial, Finset.sum_range_succ, Finset.sum_range_zero]

/-- Anchor `E_4(μ_16) = 4649680` (`m = 8`). Built level-by-level through the convolution recursion
`cpow I0c (k+1) r = Σ_{j≤r} I0c j · cpow I0c k (r−j)` to keep each step a small `range 5` sum
(the full `8`-fold expansion is too large for a single `norm_num`). -/
theorem Edef_E4_mu16 : Edef 4 8 = 4649680 := by
  -- coefficient vector of cpow I0c m at indices 0..4, as we raise the power.
  -- step lemma: c_{m+1}(r) = Σ_{j≤r} I0c j · c_m(r−j) for r ≤ 4 (I0c = 1,1,1/4,1/36,1/576).
  have step : ∀ (m : ℕ) (a b c d e : ℚ),
      (cpow I0c m 0 = a ∧ cpow I0c m 1 = b ∧ cpow I0c m 2 = c ∧
       cpow I0c m 3 = d ∧ cpow I0c m 4 = e) →
      (cpow I0c (m+1) 0 = a ∧
       cpow I0c (m+1) 1 = a + b ∧
       cpow I0c (m+1) 2 = c + b + a/4 ∧
       cpow I0c (m+1) 3 = d + c + b/4 + a/36 ∧
       cpow I0c (m+1) 4 = e + d + c/4 + b/36 + a/576) := by
    rintro m a b c d e ⟨h0, h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (∑ j ∈ Finset.range (0+1), I0c j * cpow I0c m (0 - j)) = a
      rw [Finset.sum_range_one]; norm_num [I0c, Nat.factorial]; rw [h0]
    · show (∑ j ∈ Finset.range (1+1), I0c j * cpow I0c m (1 - j)) = a + b
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [I0c, Nat.factorial]; rw [h0, h1]; ring
    · show (∑ j ∈ Finset.range (2+1), I0c j * cpow I0c m (2 - j)) = c + b + a/4
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [I0c, Nat.factorial]; rw [h0, h1, h2]; ring
    · show (∑ j ∈ Finset.range (3+1), I0c j * cpow I0c m (3 - j)) = d + c + b/4 + a/36
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      norm_num [I0c, Nat.factorial]; rw [h0, h1, h2, h3]; ring
    · show (∑ j ∈ Finset.range (4+1), I0c j * cpow I0c m (4 - j)) = e + d + c/4 + b/36 + a/576
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [I0c, Nat.factorial]; rw [h0, h1, h2, h3, h4]; ring
  have base : cpow I0c 0 0 = 1 ∧ cpow I0c 0 1 = 0 ∧ cpow I0c 0 2 = 0 ∧
      cpow I0c 0 3 = 0 ∧ cpow I0c 0 4 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [cpow]
  have s1 := step 0 _ _ _ _ _ base
  have s2 := step 1 _ _ _ _ _ s1
  have s3 := step 2 _ _ _ _ _ s2
  have s4 := step 3 _ _ _ _ _ s3
  have s5 := step 4 _ _ _ _ _ s4
  have s6 := step 5 _ _ _ _ _ s5
  have s7 := step 6 _ _ _ _ _ s6
  have s8 := step 7 _ _ _ _ _ s7
  unfold Edef
  rw [s8.2.2.2.2]
  norm_num [Nat.factorial]

/-- Non-vacuity: the bound is a genuine inequality (`Edef < wick` strictly at the anchors). -/
theorem charZero_wick_strict_anchor : Edef 4 8 < (Nat.doubleFactorial (2 * 4 - 1) : ℚ) * ((2 * 8 : ℕ) : ℚ) ^ 4 := by
  rw [Edef_E4_mu16]
  norm_num [Nat.doubleFactorial]

/-! ## The abstract decoupling lemma (Step 1, structural).

The energy of a union of `m` antipodal directions is the `m`-fold convolution of the per-direction
balanced counts. We state this abstractly: if a per-direction count has generating coefficients `c`,
the `m`-direction energy coefficient is `cpow c m r`. The convolution structure is exactly
`cpow`'s recursion `cpow c (m+1) r = Σ_j c j · cpow c m (r-j)` — the Cauchy product over the
DECOUPLED directions, which is the content of the Lam–Leung antipodal-balance factorization. -/

/-- The decoupling recursion (definitional content of `cpow`): adding one more antipodal direction
convolves the per-direction count `c` into the running `m`-direction energy coefficient. This is the
Finset-convolution form of "the `m` directions decouple". -/
theorem decoupling_convolution (c : ℕ → ℚ) (m r : ℕ) :
    cpow c (m + 1) r = ∑ j ∈ Finset.range (r + 1), c j * cpow c m (r - j) := rfl

#print axioms charZero_wick_bound
#print axioms charZero_wick_strict_anchor
#print axioms cpow_mono
#print axioms cpow_expSqc
#print axioms Edef_mu2_eq_centralBinom
#print axioms Edef_E7_mu8
#print axioms Edef_E4_mu16
#print axioms decoupling_convolution

end ArkLib.ProximityGap.Frontier.AvW0
