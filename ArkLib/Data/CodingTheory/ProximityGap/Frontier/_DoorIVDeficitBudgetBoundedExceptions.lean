/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitBudgetSublinearFloor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Door-(iv) Lane-3: BOUNDED-EXCEPTION sharpening of the deficit-budget √-floor (#444)

`_DoorIVDeficitBudgetSublinearFloor` proved that a sub-`(log 2)/2` *average* deficit
(`S = ∑_{k<a} δ_k ≤ ε·a`, `ε < (log 2)/2`) keeps the exp-relaxed dilation budget bound
`2^a·exp(−S)·M 0` at or above the `√(2^a)·M 0` Plancherel/prize scale.

That converse charges *every* level the same average `ε`.  But the realized worst-frequency
2-dilation descent is NOT uniform: at the adversarial `b*` the coset halves are exactly same-ray
(`ρ = 1`, deficit `δ_k = 0`) on the dominant TOP levels, with only sporadic deeper levels carrying
any deficit (numerically measured `δ_k` is `0` on the top block and `< 1` on a thin deep set; see the
probe in the worker log).  The honest question this raises: can a small set of deep levels with LARGE
deficit (`δ_k` up to `1`) rescue the route while the bulk of levels stays near `δ_k = 0`?

This module answers **no, not unless the exceptional set has positive density**.  Split the `a` levels
into a *good* set (`δ_k ≤ ε`, `ε < (log 2)/2`) and an *exceptional* set of size `e` (`δ_k ≤ 1`, the
deep spikes).  Then the total budget is bounded by `S ≤ ε·a + (1−ε)·e`, and as long as the exceptional
count obeys the **positive-density floor**

> `(1 − ε)·e ≤ ((log 2)/2 − ε)·a`,  i.e.  `e ≤ ρ(ε)·a`  with  `ρ(ε) = ((log 2)/2 − ε)/(1 − ε) > 0`,

the budget bound STILL stays at/above the `√(2^a)·M 0` scale.  In particular any **sublinear**
exceptional set `e = o(a)` eventually satisfies the floor: a thin set of deep deficit spikes cannot
make the dilation route reach the `√n` prize scale.  This is the formal shadow of the measured descent:
the route needs a SUSTAINED `Ω(a)`-many levels of `Ω(1)` deficit, which the same-ray-at-`b*` geometry
does not supply.

## What this module proves (and what it does NOT)

* `sum_le_avg_exceptions` : if `δ_k ≤ ε` off an exceptional finset `E` (`|E| = e`) and `δ_k ≤ 1`
  everywhere, then `∑_{k<a} δ_k ≤ ε·a + (1−ε)·e`.
* `budget_ge_sqrt_scale_of_bounded_exceptions` : under the density floor `(1−ε)·e ≤ ((log2)/2 − ε)·a`
  (and `ε < (log 2)/2`, `M 0 ≥ 0`), the exp budget bound is `≥` the `√`-scale:
  `(√2)^a · M 0 ≤ 2^a · exp(−S) · M 0`.

It does **NOT** lower-bound the true `M(μ_n)` (the open CORE) and asserts nothing about achievability.
Lane-3 constraint lemma; CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetBoundedExceptions

open Real Finset
open ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetSublinearFloor

/-- **Total deficit split bound.**  Suppose on `Finset.range a` the per-level deficit `δ` is `≤ ε` off
an exceptional set `E ⊆ range a` and `≤ 1` on `E` (and `0 ≤ ε ≤ 1`).  Then
`∑_{k<a} δ_k ≤ ε·a + (1−ε)·|E|`.  The good levels each pay `≤ ε`, the exceptional levels each pay
`≤ 1 = ε + (1−ε)`, so the excess over the uniform `ε·a` baseline is at most `(1−ε)` per exceptional
level. -/
theorem sum_le_avg_exceptions {a : ℕ} (δ : ℕ → ℝ) (E : Finset ℕ) (ε : ℝ)
    (hE : E ⊆ Finset.range a)
    (hgood : ∀ k ∈ Finset.range a, k ∉ E → δ k ≤ ε)
    (hbad : ∀ k ∈ Finset.range a, k ∈ E → δ k ≤ 1) :
    ∑ k ∈ Finset.range a, δ k ≤ ε * a + (1 - ε) * E.card := by
  -- bound δ k ≤ ε + (if k ∈ E then (1-ε) else 0) pointwise on range a
  have hpt : ∀ k ∈ Finset.range a, δ k ≤ ε + (if k ∈ E then (1 - ε) else 0) := by
    intro k hk
    by_cases hkE : k ∈ E
    · simp only [hkE, if_true]
      have := hbad k hk hkE
      linarith
    · simp only [hkE, if_false, add_zero]
      exact hgood k hk hkE
  calc ∑ k ∈ Finset.range a, δ k
      ≤ ∑ k ∈ Finset.range a, (ε + (if k ∈ E then (1 - ε) else 0)) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ Finset.range a, ε
        + ∑ k ∈ Finset.range a, (if k ∈ E then (1 - ε) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = ε * a + (1 - ε) * E.card := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
        congr 1
        -- ∑_{k∈range a} (if k∈E then 1-ε else 0) = (1-ε)*|E|  (since E ⊆ range a)
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hE, Finset.sum_const,
          nsmul_eq_mul, mul_comm]

/-- **Bounded-exception √-floor.**  Let the `a` levels split into good levels (`δ_k ≤ ε`) and an
exceptional set `E` of size `e = |E|` with `δ_k ≤ 1`.  If `ε < (log 2)/2`, the exceptional
count respects the **positive-density floor** `(1 − ε)·e ≤ ((log 2)/2 − ε)·a`, and `M 0 ≥ 0`, then the
exp-relaxed dilation budget bound stays at or above the `√(2^a)·M 0` Plancherel/prize scale:
`(√2)^a · M 0 ≤ 2^a · exp(−S) · M 0`  for the realized total `S = ∑_{k<a} δ_k`.

So a thin (in particular sublinear) set of deep deficit spikes cannot push the dilation budget down
to the `√n` prize scale: the route needs `Ω(a)`-many `Ω(1)`-deficit levels.  Lane-3 constraint lemma;
CORE not discharged. -/
theorem budget_ge_sqrt_scale_of_bounded_exceptions {a : ℕ} {ε M0 : ℝ}
    (δ : ℕ → ℝ) (E : Finset ℕ)
    (hE : E ⊆ Finset.range a)
    (hgood : ∀ k ∈ Finset.range a, k ∉ E → δ k ≤ ε)
    (hbad : ∀ k ∈ Finset.range a, k ∈ E → δ k ≤ 1)
    (hεthr : ε < Real.log 2 / 2)
    (hdensity : (1 - ε) * (E.card : ℝ) ≤ (Real.log 2 / 2 - ε) * a)
    (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0
      ≤ 2 ^ a * Real.exp (-(∑ k ∈ Finset.range a, δ k)) * M0 := by
  set S : ℝ := ∑ k ∈ Finset.range a, δ k with hSdef
  -- split bound: S ≤ ε·a + (1-ε)·|E|
  have hsplit : S ≤ ε * a + (1 - ε) * (E.card : ℝ) :=
    sum_le_avg_exceptions δ E ε hE hgood hbad
  -- density floor ⟹ S ≤ (log2/2)·a
  have hSle : S ≤ (Real.log 2 / 2) * a := by
    have : ε * a + (1 - ε) * (E.card : ℝ) ≤ ε * a + (Real.log 2 / 2 - ε) * a := by
      linarith [hdensity]
    have hcollapse : ε * a + (Real.log 2 / 2 - ε) * a = (Real.log 2 / 2) * a := by ring
    linarith [hsplit, hcollapse ▸ this]
  -- now chain through the converse engine with ε' = (log2)/2 - (small), via direct exp bound.
  -- We have S ≤ (log2/2)*a, hence exp(-S) ≥ exp(-(log2/2)*a), and 2^a*exp(-(log2/2)*a) = (√2)^a.
  have hbudget : (Real.sqrt 2) ^ a ≤ 2 ^ a * Real.exp (-S) := by
    have hmono : Real.exp (-((Real.log 2 / 2) * a)) ≤ Real.exp (-S) :=
      Real.exp_le_exp.mpr (by linarith [hSle])
    have hkey : 2 ^ a * Real.exp (-((Real.log 2 / 2) * a)) = (Real.sqrt 2) ^ a := by
      -- exp(-(log2/2)*a) = exp(-log2 * (a/2)) = 2^(-a/2); 2^a * 2^(-a/2) = 2^(a/2) = (√2)^a
      have hsqrt2 : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
      have hsqrt2_pow : (Real.sqrt 2) ^ a = (2 : ℝ) ^ ((a : ℝ) / 2) := by
        rw [hsqrt2, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/2)) a,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1; ring
      have hexp_rw : Real.exp (-((Real.log 2 / 2) * a)) = (2 : ℝ) ^ (-((a : ℝ) / 2)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
        congr 1; ring
      have hpow_rw : (2 : ℝ) ^ a = (2 : ℝ) ^ ((a : ℝ)) := by
        rw [Real.rpow_natCast]
      rw [hexp_rw, hpow_rw, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), hsqrt2_pow]
      congr 1; ring
    calc (Real.sqrt 2) ^ a
        = 2 ^ a * Real.exp (-((Real.log 2 / 2) * a)) := hkey.symm
      _ ≤ 2 ^ a * Real.exp (-S) := by
          apply mul_le_mul_of_nonneg_left hmono
          positivity
  exact mul_le_mul_of_nonneg_right hbudget hM0

#print axioms sum_le_avg_exceptions
#print axioms budget_ge_sqrt_scale_of_bounded_exceptions

end ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetBoundedExceptions
