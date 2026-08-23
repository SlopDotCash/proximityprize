/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The `johnsonBoundReal ≤ errStar` comparison — the arithmetic core

The last numeric input of the #302 Johnson MCA chain is the closed-form comparison between
the in-tree Hab25 bound

  `johnsonBoundReal = [(2(M+½)⁵ + 3(M+½)δρ₊)/(3ρ₊^{3/2})·n + (M+½)/√ρ₊]/|F|`

and the WHIR conjecture's error (pair case, `2^{2m} = (ρn)²`)

  `errStar δ = (ρn)²/(|F|·(2·min(1−√ρ−δ, √ρ/20))⁷)`.

This file proves the **arithmetic core** of that comparison, divisions cleared and all
`rpow`s eliminated by the substitutions `s := √ρ₊`, `r := √ρ`, `u := 2μ`
(`μ := min(1−√ρ−δ, √ρ/20)`), `P := M + ½`:

* `errstar_numeric_core` — the division-free inequality

    `(2P⁵ + 3Pδs²)·n·u⁷ + 3P·s²·u⁷ ≤ 3·s³·(r²n)²`

  under `0 < r ≤ 1`, `r ≤ s`, `s² ≤ 2r²` (`ρ₊ ≤ 2ρ`), `0 < u`, `10u ≤ r`
  (`μ ≤ √ρ/20`), `1 ≤ n`, `0 ≤ δ ≤ 1`, and the `M`-ceiling fact `20·uP ≤ 27·s`
  packaged as `hPu : u·P ≤ s + (7/2)·u`;

* `johnsonBound_term_le_errStar_term` — the division form
  `(2P⁵ + 3Pδs²)/(3s³)·n + P/s ≤ (r²n)²/u⁷` — exactly the `|F|`-cleared comparison.

The margins are enormous (the three term-ratios sum to `< 0.18`), so the proof is a short
chain of product bounds. What remains for the full `hcmp` hypothesis of
`Hab25WhirBridge.lean` is pure *convention glue*: `rpow ↔ sqrt`, the ceiling bound for `M`,
and the in-tree rate identities (`Gen.rate = 2^m/n`, `ρ₊ = (2^m+1)/n`) — no analysis.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-- **The division-free arithmetic core** of `johnsonBoundReal ≤ errStar`:
`(2P⁵ + 3Pδs²)·n·u⁷ + 3P·s²·u⁷ ≤ 3·s³·(r²n)²`, with two orders of magnitude to spare. -/
theorem errstar_numeric_core
    {s r u n δ P : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrs : r ≤ s) (hs2 : s ^ 2 ≤ 2 * r ^ 2)
    (hu0 : 0 < u) (hur : 10 * u ≤ r)
    (hn : 1 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP : 7 / 2 ≤ P) (hPu : u * P ≤ s + (7 / 2) * u) :
    (2 * P ^ 5 + 3 * P * δ * s ^ 2) * n * u ^ 7 + 3 * P * s ^ 2 * u ^ 7 ≤
      3 * s ^ 3 * (r ^ 2 * n) ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le hr0 hrs
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn
  -- the master bound: `20·uP ≤ 27·s` (using `10u ≤ r ≤ s`)
  have key : 20 * (u * P) ≤ 27 * s := by
    have h10 : 10 * u ≤ s := le_trans hur hrs
    nlinarith
  have hkey0 : 0 ≤ 20 * (u * P) := by positivity
  -- powers of the master bound and of `10u ≤ r`
  have key5 : (20 * (u * P)) ^ 5 ≤ (27 * s) ^ 5 := pow_le_pow_left₀ hkey0 key 5
  have hu2 : (10 * u) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by positivity) hur 2
  have hu6 : (10 * u) ^ 6 ≤ r ^ 4 := by
    have h6 : (10 * u) ^ 6 ≤ r ^ 6 := pow_le_pow_left₀ (by positivity) hur 6
    have h64 : r ^ 6 ≤ r ^ 4 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
    exact le_trans h6 h64
  have hs5 : s ^ 5 ≤ s ^ 3 * (2 * r ^ 2) := by
    calc s ^ 5 = s ^ 3 * s ^ 2 := by ring
      _ ≤ s ^ 3 * (2 * r ^ 2) := by
          exact mul_le_mul_of_nonneg_left hs2 (by positivity)
  set X : ℝ := n * s ^ 3 * r ^ 4 with hX
  have hX0 : 0 ≤ X := by positivity
  -- term 1: `320000000·(2P⁵nu⁷) ≤ 57395628·X`
  have ht1 : 320000000 * (2 * P ^ 5 * n * u ^ 7) ≤ 57395628 * X := by
    have h1 : (20 * (u * P)) ^ 5 * (10 * u) ^ 2 ≤ (27 * s) ^ 5 * r ^ 2 :=
      mul_le_mul key5 hu2 (by positivity) (by positivity)
    calc 320000000 * (2 * P ^ 5 * n * u ^ 7)
        = 2 * n * ((20 * (u * P)) ^ 5 * (10 * u) ^ 2) := by ring
      _ ≤ 2 * n * ((27 * s) ^ 5 * r ^ 2) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * 27 ^ 5 * n * r ^ 2 * s ^ 5 := by ring
      _ ≤ 2 * 27 ^ 5 * n * r ^ 2 * (s ^ 3 * (2 * r ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hs5 (by positivity)
      _ = 57395628 * X := by rw [hX]; ring
  -- term 2: `20000000·(3Pδs²nu⁷) ≤ 81·X`
  have ht2 : 20000000 * (3 * P * δ * s ^ 2 * n * u ^ 7) ≤ 81 * X := by
    have h1 : (20 * (u * P)) * (10 * u) ^ 6 ≤ (27 * s) * r ^ 4 :=
      mul_le_mul key hu6 (by positivity) (by positivity)
    calc 20000000 * (3 * P * δ * s ^ 2 * n * u ^ 7)
        = 3 * δ * n * s ^ 2 * ((20 * (u * P)) * (10 * u) ^ 6) := by ring
      _ ≤ 3 * δ * n * s ^ 2 * ((27 * s) * r ^ 4) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 81 * δ * X := by rw [hX]; ring
      _ ≤ 81 * X := by nlinarith
  -- term 3: `20000000·(3Ps²u⁷) ≤ 81·X`
  have ht3 : 20000000 * (3 * P * s ^ 2 * u ^ 7) ≤ 81 * X := by
    have h1 : (20 * (u * P)) * (10 * u) ^ 6 ≤ (27 * s) * r ^ 4 :=
      mul_le_mul key hu6 (by positivity) (by positivity)
    calc 20000000 * (3 * P * s ^ 2 * u ^ 7)
        = 3 * s ^ 2 * ((20 * (u * P)) * (10 * u) ^ 6) := by ring
      _ ≤ 3 * s ^ 2 * ((27 * s) * r ^ 4) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 81 * (s ^ 3 * r ^ 4) := by ring
      _ ≤ 81 * X := by
          rw [hX]
          nlinarith [mul_nonneg (mul_nonneg hs0.le hs0.le) hs0.le]
  -- assemble: the right side is `3n·X`
  have hgoal : 3 * s ^ 3 * (r ^ 2 * n) ^ 2 = 3 * n * X := by rw [hX]; ring
  rw [hgoal]
  have hXn : X ≤ n * X := le_mul_of_one_le_left hX0 hn
  linarith

/-- **The division form**: `(2P⁵ + 3Pδs²)/(3s³)·n + P/s ≤ (r²n)²/u⁷` — the
`johnsonBoundReal ≤ errStar` comparison with `|F|` cleared, in the `√`-substituted
variables. -/
theorem johnsonBound_term_le_errStar_term
    {s r u n δ P : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrs : r ≤ s) (hs2 : s ^ 2 ≤ 2 * r ^ 2)
    (hu0 : 0 < u) (hur : 10 * u ≤ r)
    (hn : 1 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hP : 7 / 2 ≤ P) (hPu : u * P ≤ s + (7 / 2) * u) :
    (2 * P ^ 5 + 3 * P * δ * s ^ 2) / (3 * (s ^ 2 * s)) * n + P / s ≤
      (r ^ 2 * n) ^ 2 / u ^ 7 := by
  have hs0 : 0 < s := lt_of_lt_of_le hr0 hrs
  have hcore := errstar_numeric_core hr0 hr1 hrs hs2 hu0 hur hn hδ0 hδ1 hP hPu
  have hcombine : (2 * P ^ 5 + 3 * P * δ * s ^ 2) / (3 * (s ^ 2 * s)) * n + P / s =
      ((2 * P ^ 5 + 3 * P * δ * s ^ 2) * n + 3 * P * s ^ 2) / (3 * (s ^ 2 * s)) := by
    field_simp
  rw [hcombine, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((2 * P ^ 5 + 3 * P * δ * s ^ 2) * n + 3 * P * s ^ 2) * u ^ 7
      = (2 * P ^ 5 + 3 * P * δ * s ^ 2) * n * u ^ 7 + 3 * P * s ^ 2 * u ^ 7 := by ring
    _ ≤ 3 * s ^ 3 * (r ^ 2 * n) ^ 2 := hcore
    _ = (r ^ 2 * n) ^ 2 * (3 * (s ^ 2 * s)) := by ring

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.errstar_numeric_core
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonBound_term_le_errStar_term
