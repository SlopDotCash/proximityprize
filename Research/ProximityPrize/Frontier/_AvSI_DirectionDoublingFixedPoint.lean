/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Self-improving char-0 Wick bound via the direction-doubling fixed point (#444, SELF_IMPROVING)

The char-0 energy is `E_r(μ_{2m}) = besselE r m := (2r)! · [x^{2r}] I0^m` (the Bessel-identity RHS
of `_AvW0_BesselWickAllR`, with `I0 = Σ_k x^{2k}/(k!)²` the per-direction central count). Adding
directions is the power `I0 ↦ I0^m`. Because `I0^{m₁+m₂} = I0^{m₁}·I0^{m₂}`, the energy of the
**product of two direction-systems** is the binomial convolution of the factors' energies — an
EXACT self-improving (tensor-doubling) recursion. The **fixed point** of that recursion is the
Gaussian (Wick) envelope `Wick_r(m) = (2r-1)‼·(2m)^r` (the `2r`-th moment of `N(0,2m)`): it is
**convolution-stable with EQUALITY** (Gaussian stability `N(0,1)+N(0,1)=N(0,2)`), via the kernel
identity

    `Σ_{a+b=r} C(2r,2a)·(2a-1)‼·(2b-1)‼ = (2r-1)‼·2^r`.

With the base case `E_r(1)=C(2r,r) ≤ Wick_r(1)` (slack `1/r!`) the Wick bound then propagates up
the entire 2-power tower `m=2^μ` by induction, with NO loss — a second self-contained derivation
of `besselWick_allR`.

## Proven here (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

* `besselE_add` — the EXACT self-improving recursion `besselE r (m₁+m₂) =
  Σ_{a+b=r} C(2r,2a)·besselE a m₁·besselE b m₂`, proved from `I0^{m₁+m₂}=I0^{m₁}·I0^{m₂}` and the
  odd-coefficient vanishing of `I0^m` (`coeff_I0pow_odd`). This is a THEOREM (not just a verified
  identity): adding direction-systems convolves their energies.
* `wick_convStable` — the Gaussian (Wick) envelope is the EXACT fixed point of that recursion:
  `Σ_{a+b=r} C(2r,2a)·Wick_a(m₁)·Wick_b(m₂) = Wick_r(m₁+m₂)`.
* `wickKernel` — the kernel identity `Σ C(2r,2a)(2a-1)‼(2b-1)‼ = (2r-1)‼·2^r` (`N(0,1)+N(0,1)=N(0,2)`).
* `besselE_one` — base case `besselE r 1 = C(2r,r)`.
* `besselE_one_le_wick` — base case under the Wick envelope, slack `1/r!`.

Together: base case `besselE r 1 ≤ Wick_r(1)` + the recursion `besselE_add` (which is termwise
dominated by `wick_convStable` when each factor is) gives, by induction on the tower height,
`besselE r m ≤ Wick_r(m)` for every `m` — a self-contained second proof of `besselWick_allR`.

## Honest scope (#444)

**Char-0 ONLY**, and improves the number of directions `m`, **not the depth `r`**. The prize wall
is large `r≈log p` at FIXED `m=n/2`; this fixed point convolves at fixed `r` (orthogonal to depth).
The depth-halving `E_{2K} ≤ p·E_K²` loses a factor `p` per step (`p^{K-1}n^K`, overshoots Wick
~10–50× at `K≈log p`), so the depth self-improvement reduces to the char-`p` cancellation `W_K`
(the open kernel). What lands here is the char-0 fixed point: the Gaussian envelope is
convolution-stable with equality.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.SelfImproving

open PowerSeries BigOperators Finset

/-! ## The Gaussian/Wick envelope and its exact fixed-point (convolution-stability) -/

/-- The Wick envelope `Wick_r(m) = (2r-1)‼·(2m)^r`, the `2r`-th moment of `N(0,2m)`. -/
noncomputable def wickW (r m : ℕ) : ℚ := (Nat.doubleFactorial (2 * r - 1)) * ((2 * m : ℕ) : ℚ) ^ r

/-- `(2a-1)‼ · 2^a · a! = (2a)!`: the double-factorial split (Gaussian moment in factorial form). -/
theorem dfac_mul (a : ℕ) :
    (Nat.doubleFactorial (2 * a - 1) : ℚ) * (2 ^ a * Nat.factorial a) = Nat.factorial (2 * a) := by
  have hN : Nat.factorial (2 * a)
      = Nat.doubleFactorial (2 * a - 1) * (2 ^ a * Nat.factorial a) := by
    rcases a with _ | k
    · simp [Nat.doubleFactorial]
    · have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h1, Nat.factorial_eq_mul_doubleFactorial]
      have h2 : (2 * k + 1) + 1 = 2 * (k + 1) := by ring
      have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [h2, Nat.doubleFactorial_two_mul, h3]; ring
  exact_mod_cast hN.symm

/-- **The kernel identity (fixed-point equation):**
`Σ_{a+b=r} C(2r,2a)·(2a-1)‼·(2b-1)‼ = (2r-1)‼·2^r`. This is Gaussian stability
`N(0,1)+N(0,1)=N(0,2)` written on `2r`-th moments. Proved by reducing each summand to
`(2r)!/(2^r·a!·b!)` and using the binomial sum `Σ_{a+b=r} C(r,a) = 2^r`. -/
theorem wickKernel (r : ℕ) :
    ∑ a ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * a) : ℚ)
          * (Nat.doubleFactorial (2 * a - 1)) * (Nat.doubleFactorial (2 * (r - a) - 1))
      = (Nat.doubleFactorial (2 * r - 1)) * (2 ^ r : ℚ) := by
  -- Multiply both sides by 2^r * r! and show equality of integers, then divide.
  have key : ∀ a ∈ Finset.range (r + 1),
      (Nat.choose (2 * r) (2 * a) : ℚ)
          * (Nat.doubleFactorial (2 * a - 1)) * (Nat.doubleFactorial (2 * (r - a) - 1))
        = (Nat.factorial (2 * r) : ℚ) / (2 ^ r * Nat.factorial a * Nat.factorial (r - a)) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    have hab : a + (r - a) = r := by omega
    -- C(2r,2a) = (2r)! / ((2a)! (2(r-a))!)
    have hch : (Nat.choose (2 * r) (2 * a) : ℚ)
        = (Nat.factorial (2 * r) : ℚ) / (Nat.factorial (2 * a) * Nat.factorial (2 * (r - a))) := by
      have h2 : 2 * a ≤ 2 * r := by omega
      have := Nat.choose_mul_factorial_mul_factorial h2
      have hsub : 2 * r - 2 * a = 2 * (r - a) := by omega
      rw [hsub] at this
      have hpos : (0 : ℚ) < Nat.factorial (2 * a) * Nat.factorial (2 * (r - a)) := by
        have := Nat.factorial_pos (2 * a); have := Nat.factorial_pos (2 * (r-a)); positivity
      field_simp
      exact_mod_cast this
    rw [hch]
    -- (2a-1)‼ = (2a)!/(2^a a!), (2(r-a)-1)‼ = (2(r-a))!/(2^{r-a} (r-a)!)
    have hfa : (Nat.factorial (2 * a) : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
    have hfb : (Nat.factorial (2 * (r-a)) : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
    have haa : (2 ^ a * Nat.factorial a : ℚ) > 0 := by
      have := Nat.factorial_pos a; positivity
    have hbb : (2 ^ (r-a) * Nat.factorial (r-a) : ℚ) > 0 := by
      have := Nat.factorial_pos (r-a); positivity
    have da := dfac_mul a
    have db := dfac_mul (r - a)
    -- express dfac in division form
    have da' : (Nat.doubleFactorial (2 * a - 1) : ℚ)
        = Nat.factorial (2 * a) / (2 ^ a * Nat.factorial a) := by
      rw [eq_div_iff (ne_of_gt haa)]; exact_mod_cast da
    have db' : (Nat.doubleFactorial (2 * (r-a) - 1) : ℚ)
        = Nat.factorial (2 * (r-a)) / (2 ^ (r-a) * Nat.factorial (r-a)) := by
      rw [eq_div_iff (ne_of_gt hbb)]; exact_mod_cast db
    rw [da', db']
    have hpow : (2 : ℚ) ^ r = 2 ^ a * 2 ^ (r - a) := by
      rw [← pow_add, hab]
    rw [hpow]
    field_simp
  rw [Finset.sum_congr rfl key]
  -- Σ_a (2r)!/(2^r a!(r-a)!) = (2r)!/2^r · Σ 1/(a!(r-a)!) = (2r)!/2^r · 2^r/r! = (2r)!/r!
  -- and (2r-1)‼ 2^r = (2r)!/r!.
  have hbin : ∑ a ∈ Finset.range (r + 1),
      (Nat.factorial (2 * r) : ℚ) / (2 ^ r * Nat.factorial a * Nat.factorial (r - a))
      = (Nat.factorial (2 * r) : ℚ) / (2 ^ r) * ∑ a ∈ Finset.range (r + 1),
          ((Nat.choose r a : ℚ) / Nat.factorial r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_range] at ha
    have hch : (Nat.choose r a : ℚ)
        = (Nat.factorial r : ℚ) / (Nat.factorial a * Nat.factorial (r - a)) := by
      have hle : a ≤ r := by omega
      have := Nat.choose_mul_factorial_mul_factorial hle
      have hpos : (0 : ℚ) < Nat.factorial a * Nat.factorial (r - a) := by
        have := Nat.factorial_pos a; have := Nat.factorial_pos (r-a); positivity
      field_simp; exact_mod_cast this
    rw [hch]
    have hfr : (Nat.factorial r : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos r
    have hfa : (Nat.factorial a : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos a
    have hfb : (Nat.factorial (r-a) : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos (r-a)
    field_simp
  rw [hbin]
  -- Σ C(r,a)/r! = (Σ C(r,a))/r! = 2^r/r!
  have hsum : ∑ a ∈ Finset.range (r + 1), ((Nat.choose r a : ℚ) / Nat.factorial r)
      = (2 ^ r : ℚ) / Nat.factorial r := by
    rw [← Finset.sum_div]
    congr 1
    have h := Nat.sum_range_choose r
    have : ∑ i ∈ Finset.range (r + 1), ((Nat.choose r i : ℚ))
        = ((∑ i ∈ Finset.range (r + 1), Nat.choose r i : ℕ) : ℚ) := by push_cast; rfl
    rw [this, h]; push_cast; ring
  rw [hsum]
  -- (2r)!/2^r * 2^r/r! = (2r)!/r! = (2r-1)‼ 2^r
  have hfr : (Nat.factorial r : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos r
  have hsplit : (Nat.factorial (2 * r) : ℚ) = Nat.doubleFactorial (2 * r - 1) * (2 ^ r * Nat.factorial r) :=
    (dfac_mul r).symm
  rw [hsplit]
  field_simp

/-- **The Wick envelope is the EXACT fixed point** of the direction-convolution recursion:
`Σ_{a+b=r} C(2r,2a)·Wick_a(m₁)·Wick_b(m₂) = Wick_r(m₁+m₂)`. (Gaussian convolution
`N(0,2m₁)+N(0,2m₂)=N(0,2(m₁+m₂))`, exact.) -/
theorem wick_convStable (r m₁ m₂ : ℕ) :
    ∑ a ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * a) : ℚ) * wickW a m₁ * wickW (r - a) m₂
      = wickW r (m₁ + m₂) := by
  unfold wickW
  -- factor out: each summand = C(2r,2a)(2a-1)‼(2(r-a)-1)‼ · (2m₁)^a (2m₂)^{r-a}
  -- Σ = (Σ kernel-weighted) but with the (2m)^a split; use binomial theorem in (2m₁,2m₂).
  -- Cleanest: prove via the multinomial form. We show LHS = Σ_a C(2r,2a)(2a-1)‼(2(r-a)-1)‼ x^a y^{r-a}
  -- = (2r-1)‼ (x+y)^r with x=2m₁, y=2m₂ — a WEIGHTED kernel identity. Prove that weighted form:
  have hkey : ∀ a ∈ Finset.range (r + 1),
      (Nat.choose (2 * r) (2 * a) : ℚ) * ((Nat.doubleFactorial (2 * a - 1)) * ((2 * m₁ : ℕ) : ℚ) ^ a)
        * ((Nat.doubleFactorial (2 * (r - a) - 1)) * ((2 * m₂ : ℕ) : ℚ) ^ (r - a))
      = (Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a)
          * ((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a) := by
    intro a ha
    simp only [Finset.mem_range] at ha
    -- C(2r,2a)(2a-1)‼(2(r-a)-1)‼ = (2r-1)‼ C(r,a). Prove this scalar identity.
    have hscal : (Nat.choose (2 * r) (2 * a) : ℚ)
          * (Nat.doubleFactorial (2 * a - 1)) * (Nat.doubleFactorial (2 * (r - a) - 1))
        = (Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a) := by
      have hab : a + (r - a) = r := by omega
      have h2 : 2 * a ≤ 2 * r := by omega
      have hch : (Nat.choose (2 * r) (2 * a) : ℚ)
          = (Nat.factorial (2 * r) : ℚ) / (Nat.factorial (2 * a) * Nat.factorial (2 * (r - a))) := by
        have := Nat.choose_mul_factorial_mul_factorial h2
        have hsub : 2 * r - 2 * a = 2 * (r - a) := by omega
        rw [hsub] at this
        have hpos : (0 : ℚ) < Nat.factorial (2 * a) * Nat.factorial (2 * (r - a)) := by
          have := Nat.factorial_pos (2 * a); have := Nat.factorial_pos (2 * (r-a)); positivity
        field_simp; exact_mod_cast this
      have hcr : (Nat.choose r a : ℚ)
          = (Nat.factorial r : ℚ) / (Nat.factorial a * Nat.factorial (r - a)) := by
        have hle : a ≤ r := by omega
        have := Nat.choose_mul_factorial_mul_factorial hle
        have hpos : (0 : ℚ) < Nat.factorial a * Nat.factorial (r - a) := by
          have := Nat.factorial_pos a; have := Nat.factorial_pos (r-a); positivity
        field_simp; exact_mod_cast this
      have hfa : (0:ℚ) < (2 ^ a * Nat.factorial a) := by have := Nat.factorial_pos a; positivity
      have hfb : (0:ℚ) < (2 ^ (r-a) * Nat.factorial (r-a)) := by
        have := Nat.factorial_pos (r-a); positivity
      have da' : (Nat.doubleFactorial (2 * a - 1) : ℚ)
          = Nat.factorial (2 * a) / (2 ^ a * Nat.factorial a) := by
        rw [eq_div_iff (ne_of_gt hfa)]; exact_mod_cast dfac_mul a
      have db' : (Nat.doubleFactorial (2 * (r-a) - 1) : ℚ)
          = Nat.factorial (2 * (r-a)) / (2 ^ (r-a) * Nat.factorial (r-a)) := by
        rw [eq_div_iff (ne_of_gt hfb)]; exact_mod_cast dfac_mul (r-a)
      have dr' : (Nat.doubleFactorial (2 * r - 1) : ℚ)
          = Nat.factorial (2 * r) / (2 ^ r * Nat.factorial r) := by
        have hfr : (0:ℚ) < (2 ^ r * Nat.factorial r) := by have := Nat.factorial_pos r; positivity
        rw [eq_div_iff (ne_of_gt hfr)]; exact_mod_cast dfac_mul r
      rw [hch, da', db', hcr, dr']
      have hpow : (2 : ℚ) ^ r = 2 ^ a * 2 ^ (r - a) := by rw [← pow_add, hab]
      have h2a : (Nat.factorial (2*a):ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
      have h2b : (Nat.factorial (2*(r-a)):ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
      have hra : (Nat.factorial a:ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
      have hrb : (Nat.factorial (r-a):ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
      have hrr : (Nat.factorial r:ℚ) > 0 := by exact_mod_cast Nat.factorial_pos _
      rw [hpow]
      field_simp
    calc (Nat.choose (2 * r) (2 * a) : ℚ)
            * ((Nat.doubleFactorial (2 * a - 1)) * ((2 * m₁ : ℕ) : ℚ) ^ a)
            * ((Nat.doubleFactorial (2 * (r - a) - 1)) * ((2 * m₂ : ℕ) : ℚ) ^ (r - a))
        = ((Nat.choose (2 * r) (2 * a) : ℚ)
            * (Nat.doubleFactorial (2 * a - 1)) * (Nat.doubleFactorial (2 * (r - a) - 1)))
            * (((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a)) := by ring
      _ = ((Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a))
            * (((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a)) := by rw [hscal]
      _ = (Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a)
            * ((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a) := by ring
  rw [Finset.sum_congr rfl hkey]
  -- Σ_a (2r-1)‼ C(r,a) x^a y^{r-a} = (2r-1)‼ (x+y)^r = (2r-1)‼ (2(m₁+m₂))^r
  have hbin : ∑ a ∈ Finset.range (r + 1),
      (Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a)
        * ((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a)
      = (Nat.doubleFactorial (2 * r - 1) : ℚ)
        * ((((2 * m₁ : ℕ) : ℚ) + ((2 * m₂ : ℕ) : ℚ)) ^ r) := by
    have hfactor : ∑ a ∈ Finset.range (r + 1),
        (Nat.doubleFactorial (2 * r - 1) : ℚ) * (Nat.choose r a)
          * ((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a)
        = (Nat.doubleFactorial (2 * r - 1) : ℚ) * ∑ a ∈ Finset.range (r + 1),
            ((Nat.choose r a : ℚ) * ((2 * m₁ : ℕ) : ℚ) ^ a * ((2 * m₂ : ℕ) : ℚ) ^ (r - a)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [hfactor]
    congr 1
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro a ha
    push_cast
    ring
  rw [hbin]
  congr 1
  push_cast
  ring

/-! ## The base case `besselE r 1 = C(2r,r) ≤ Wick_r(1)` (slack `1/r!`). -/

/-- The per-direction EGF, identical to `_AvW0_BesselWickAllR.I0`. -/
noncomputable def I0 : PowerSeries ℚ :=
  PowerSeries.mk (fun j => if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2))^2 else 0)

/-- The Bessel char-0 energy `besselE r m := (2r)!·[x^{2r}] I0^m`, identical to
`_AvW0_BesselWickAllR.besselE`. -/
noncomputable def besselE (r m : ℕ) : ℚ :=
  (Nat.factorial (2 * r)) * PowerSeries.coeff (R := ℚ) (2 * r) (I0 ^ m)

/-- Odd coefficients of every power `I0^m` vanish (each `I0` coeff is even-supported). -/
theorem coeff_I0pow_odd (m j : ℕ) (hj : j % 2 = 1) :
    PowerSeries.coeff (R := ℚ) j (I0 ^ m) = 0 := by
  induction m generalizing j with
  | zero =>
      simp only [pow_zero]; rw [PowerSeries.coeff_one]
      have : j ≠ 0 := by omega
      simp [this]
  | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero; intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.even_or_odd p.2 with hev | hod
      · have hp1 : p.1 % 2 = 1 := by obtain ⟨t, ht⟩ := hev; omega
        rw [ih p.1 hp1]; ring
      · have hp2 : p.2 % 2 = 1 := by obtain ⟨t, ht⟩ := hod; omega
        have : PowerSeries.coeff (R := ℚ) p.2 I0 = 0 := by simp [I0]; omega
        rw [this]; ring

/-- Reindex an even-supported sum `Σ_{i∈range(2r+1)} f i = Σ_{a∈range(r+1)} f(2a)`. -/
theorem sum_even_reindex {M : Type*} [AddCommMonoid M] (r : ℕ) (f : ℕ → M)
    (hodd : ∀ i, i % 2 = 1 → f i = 0) :
    ∑ i ∈ Finset.range (2 * r + 1), f i = ∑ a ∈ Finset.range (r + 1), f (2 * a) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2*r+1)) (fun i => i % 2 = 0) f]
  have hodd0 : ∑ i ∈ (Finset.range (2*r+1)).filter (fun i => ¬ i % 2 = 0), f i = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [Finset.mem_filter] at hi; exact hodd i (by omega)
  rw [hodd0, add_zero]
  apply Finset.sum_nbij' (fun i => i / 2) (fun a => 2 * a)
  · intro i hi; rw [Finset.mem_filter, Finset.mem_range] at hi; rw [Finset.mem_range]; omega
  · intro a ha; rw [Finset.mem_range] at ha; rw [Finset.mem_filter, Finset.mem_range]; omega
  · intro i hi; rw [Finset.mem_filter] at hi; omega
  · intro a ha; omega
  · intro i hi; rw [Finset.mem_filter] at hi; congr 1; omega

/-- **EXACT direction-doubling (tensor) recursion** — the self-improving relation. Because
`I0^{m₁+m₂} = I0^{m₁}·I0^{m₂}`, the energy of the product direction-system is the binomial
convolution of the factor energies:
`besselE r (m₁+m₂) = Σ_{a+b=r} C(2r,2a)·besselE a m₁·besselE b m₂`. (Odd cross-terms vanish.) -/
theorem besselE_add (r m₁ m₂ : ℕ) :
    besselE r (m₁ + m₂)
      = ∑ a ∈ Finset.range (r + 1),
          (Nat.choose (2 * r) (2 * a) : ℚ) * besselE a m₁ * besselE (r - a) m₂ := by
  unfold besselE
  rw [pow_add, PowerSeries.coeff_mul, Finset.mul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_even_reindex r (fun i => (Nat.factorial (2 * r) : ℚ)
        * (PowerSeries.coeff (R := ℚ) i (I0 ^ m₁)
            * PowerSeries.coeff (R := ℚ) (2 * r - i) (I0 ^ m₂)))]
  · apply Finset.sum_congr rfl
    intro a ha; rw [Finset.mem_range] at ha
    have hsub : 2 * r - 2 * a = 2 * (r - a) := by omega
    rw [hsub]
    have hch : (Nat.factorial (2 * r) : ℚ)
        = (Nat.choose (2 * r) (2 * a) : ℚ) * Nat.factorial (2 * a) * Nat.factorial (2 * (r - a)) := by
      have h2 : 2 * a ≤ 2 * r := by omega
      have hh := Nat.choose_mul_factorial_mul_factorial h2
      have hsub2 : 2 * r - 2 * a = 2 * (r - a) := by omega
      rw [hsub2] at hh
      have hcast : (Nat.choose (2*r) (2*a) * Nat.factorial (2*a) * Nat.factorial (2*(r-a)) : ℕ)
          = Nat.factorial (2*r) := hh
      exact_mod_cast hcast.symm
    rw [hch]; ring
  · intro i hi
    rw [coeff_I0pow_odd m₁ i hi]; ring

@[simp] theorem coeff_I0 (j : ℕ) :
    PowerSeries.coeff (R := ℚ) j I0 =
      (if j % 2 = 0 then (1 : ℚ) / (Nat.factorial (j / 2))^2 else 0) := by simp [I0]

/-- **Base case (single direction):** `besselE r 1 = C(2r,r)`, the central binomial. -/
theorem besselE_one (r : ℕ) : besselE r 1 = (Nat.centralBinom r : ℚ) := by
  unfold besselE
  rw [pow_one, coeff_I0]
  have hmod : (2 * r) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : (2 * r) / 2 = r := by omega
  rw [hdiv]
  -- (2r)! * (1/(r!)²) = (2r)!/(r!)² = C(2r,r)
  rw [Nat.centralBinom]
  have hcb : Nat.choose (2 * r) r * (Nat.factorial r * Nat.factorial r) = Nat.factorial (2 * r) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
    have he : 2 * r - r = r := by omega
    rw [he] at h
    rw [← mul_assoc]; exact h
  have hfr : (Nat.factorial r : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos r
  field_simp
  have heq : (Nat.factorial (2 * r) : ℚ) = (Nat.choose (2 * r) r) * (Nat.factorial r * Nat.factorial r) := by
    exact_mod_cast hcb.symm
  rw [heq]; ring

/-- **Base case under the Wick envelope:** `besselE r 1 ≤ wickW r 1` (slack `1/r!`, since
`C(2r,r) = (2r-1)‼·2^r/r!` and `wickW r 1 = (2r-1)‼·2^r`). -/
theorem besselE_one_le_wick (r : ℕ) : besselE r 1 ≤ wickW r 1 := by
  rw [besselE_one]
  unfold wickW
  -- C(2r,r) = (2r)!/(r!)²,  wickW r 1 = (2r-1)‼ (2)^r = (2r)!/r!.  So ratio = 1/r! ≤ 1.
  have hcb : (Nat.centralBinom r : ℚ) * Nat.factorial r = (Nat.factorial (2*r) : ℚ) / Nat.factorial r := by
    rw [Nat.centralBinom]
    have hcbN : Nat.choose (2 * r) r * (Nat.factorial r * Nat.factorial r) = Nat.factorial (2 * r) := by
      have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
      have he : 2 * r - r = r := by omega
      rw [he] at h
      rw [← mul_assoc]; exact h
    have hfr : (Nat.factorial r : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos r
    field_simp
    have heq : (Nat.factorial (2 * r) : ℚ) = (Nat.choose (2 * r) r) * (Nat.factorial r * Nat.factorial r) := by
      exact_mod_cast hcbN.symm
    rw [heq]; ring
  have hwick : (Nat.doubleFactorial (2 * r - 1) : ℚ) * ((2 * 1 : ℕ) : ℚ) ^ r
      = (Nat.factorial (2*r) : ℚ) / Nat.factorial r := by
    have hfr : (Nat.factorial r : ℚ) > 0 := by exact_mod_cast Nat.factorial_pos r
    rw [eq_div_iff (ne_of_gt hfr)]
    push_cast
    have := dfac_mul r
    -- (2r-1)‼ * (2^r * r!) = (2r)!
    calc (Nat.doubleFactorial (2 * r - 1) : ℚ) * (2:ℚ) ^ r * Nat.factorial r
        = (Nat.doubleFactorial (2 * r - 1) : ℚ) * ((2:ℚ) ^ r * Nat.factorial r) := by ring
      _ = (Nat.factorial (2 * r) : ℚ) := by exact_mod_cast this
  rw [hwick]
  -- C(2r,r) ≤ (2r)!/r! since C(2r,r) * r! = (2r)!/r! ... actually C(2r,r) = (2r)!/(r!)² ≤ (2r)!/r! iff r!≥1.
  have hfr1 : (1 : ℚ) ≤ Nat.factorial r := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hcbnn : (0 : ℚ) ≤ (Nat.centralBinom r : ℚ) := by positivity
  -- from hcb: centralBinom * r! = (2r)!/r!. Since r!≥1, centralBinom ≤ centralBinom*r! = RHS.
  calc (Nat.centralBinom r : ℚ) = (Nat.centralBinom r : ℚ) * 1 := by ring
    _ ≤ (Nat.centralBinom r : ℚ) * Nat.factorial r := by
        apply mul_le_mul_of_nonneg_left hfr1 hcbnn
    _ = (Nat.factorial (2*r) : ℚ) / Nat.factorial r := hcb

/-! ## Capstone: tower induction closes char-0 Wick a second way. -/

/-- `besselE r m ≥ 0` (energies are sums of nonneg central counts). -/
theorem besselE_nonneg (r m : ℕ) : 0 ≤ besselE r m := by
  unfold besselE
  apply mul_nonneg (by positivity)
  -- coeff of I0^m is nonneg since I0 has nonneg coeffs
  induction m generalizing r with
  | zero =>
      rcases Nat.eq_zero_or_pos (2 * r) with h | h
      · simp [pow_zero, h]
      · rw [pow_zero, PowerSeries.coeff_one]; split <;> norm_num
  | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Finset.sum_nonneg; intro p _
      apply mul_nonneg
      · -- coeff p.1 (I0^k) ≥ 0; reduce to ih by an index r' with 2 r' = p.1 OR odd ⇒ via direct
        by_cases hpar : p.1 % 2 = 0
        · have : p.1 = 2 * (p.1 / 2) := by omega
          rw [this]; have := ih (p.1 / 2); exact this
        · rw [coeff_I0pow_odd k p.1 (by omega)]
      · rw [coeff_I0]; split
        · positivity
        · rfl

/-- `wickW r m ≥ 0`. -/
theorem wickW_nonneg (r m : ℕ) : 0 ≤ wickW r m := by unfold wickW; positivity

/-- **Tower induction (capstone): the self-improving fixed point CLOSES char-0 Wick.**
`besselE r m ≤ wickW r m` for ALL `r, m`, by induction on the number of directions `m`: base case
`besselE_one_le_wick`, step via the EXACT recursion `besselE_add r m 1`, the EXACT fixed-point
`wick_convStable r m 1`, and termwise domination (each convolution summand of `besselE` is `≤` the
corresponding summand of `wickW`, all factors nonneg). This re-derives `besselWick_allR` purely
from the direction-doubling fixed point — no `exp(x²)` coefficient domination. -/
theorem besselE_le_wick (r m : ℕ) : besselE r m ≤ wickW r m := by
  induction m generalizing r with
  | zero =>
      -- besselE r 0 = (2r)! [x^{2r}] 1 = (2r)! * (1 if r=0 else 0); wickW r 0 = (2r-1)‼ * 0^r
      unfold besselE wickW
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
        have : ((2 * 0 : ℕ) : ℚ) ^ r = 0 := by
          simp only [Nat.mul_zero, Nat.cast_zero]; exact zero_pow (by omega)
        rw [this]; simp
  | succ k ih =>
      -- m = k+1 = k + 1. Use besselE_add r k 1 and wick_convStable r k 1.
      rw [show k + 1 = k + 1 from rfl, besselE_add r k 1]
      rw [← wick_convStable r k 1]
      apply Finset.sum_le_sum
      intro a ha; rw [Finset.mem_range] at ha
      -- C(2r,2a) besselE a k besselE (r-a) 1 ≤ C(2r,2a) wickW a k wickW (r-a) 1
      have hc : (0 : ℚ) ≤ (Nat.choose (2 * r) (2 * a) : ℚ) := by positivity
      have h1 : besselE a k ≤ wickW a k := ih a
      have h2 : besselE (r - a) 1 ≤ wickW (r - a) 1 := besselE_one_le_wick (r - a)
      have hb1 : 0 ≤ besselE a k := besselE_nonneg a k
      have hb2 : 0 ≤ besselE (r - a) 1 := besselE_nonneg (r - a) 1
      have hw1 : 0 ≤ wickW a k := wickW_nonneg a k
      -- C * x * y ≤ C * X * Y from 0≤x≤X, 0≤y≤Y, 0≤C
      have hxy : besselE a k * besselE (r - a) 1 ≤ wickW a k * wickW (r - a) 1 :=
        mul_le_mul h1 h2 hb2 hw1
      calc (Nat.choose (2 * r) (2 * a) : ℚ) * besselE a k * besselE (r - a) 1
          = (Nat.choose (2 * r) (2 * a) : ℚ) * (besselE a k * besselE (r - a) 1) := by ring
        _ ≤ (Nat.choose (2 * r) (2 * a) : ℚ) * (wickW a k * wickW (r - a) 1) :=
            mul_le_mul_of_nonneg_left hxy hc
        _ = (Nat.choose (2 * r) (2 * a) : ℚ) * wickW a k * wickW (r - a) 1 := by ring

/-! ## Axiom audit -/
#print axioms dfac_mul
#print axioms wickKernel
#print axioms wick_convStable
#print axioms besselE_add
#print axioms besselE_one
#print axioms besselE_one_le_wick
#print axioms besselE_le_wick

end ArkLib.ProximityGap.Frontier.SelfImproving
