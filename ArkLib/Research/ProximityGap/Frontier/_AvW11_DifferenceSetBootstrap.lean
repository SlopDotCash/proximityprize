/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Difference-set self-bounding bootstrap on the large-period set (#444)

A direct attack on the Paley tail, attempted here and carried to where it breaks. Let
`B_T = {b ≠ 0 : ‖η_b‖² > T²}` (a union of `μ_n`-cosets by `_AvW8`). Expanding the truncated second
moment through the **difference set** of `μ_n`:

`Σ_{b∈B_T} ‖η_b‖² = Σ_{x,y∈G} \hat{1}_{B_T}(x−y) = |B_T|·n + Σ_{x≠y} \hat{1}_{B_T}(x−y)`,

and using that `G = μ_n` is **Sidon-except-negation** (each nonzero difference has multiplicity
`≤ 2`), Cauchy–Schwarz + Parseval `(Σ_t |\hat{1}_{B_T}(t)|² = p·|B_T|)` bound the off-diagonal by
`n·√(2p·|B_T|)`. Since every `b ∈ B_T` contributes `> T²`:

`|B_T|·T² ≤ |B_T|·n + n·√(2p·|B_T|)`  (the **self-bounding inequality**).

This file proves the algebraic closure: that inequality forces `|B_T| ≤ 2p·n²/(T²−n)²`. This is a
genuine, structure-using tail bound (it consumes the near-Sidon difference multiplicity, not just
abstract Markov). **But it reaches exactly the 4th-moment floor** `T^{-4}` — at `T² = Kn` it gives
`|B_T| ≤ 2p/(K−1)²`, the `_AvW10` `r=2` rung — and **no further**.

## Where the attack breaks (the honest diagnosis)
Pushing to higher order replaces the difference set by the `r`-fold difference set, whose
Cauchy–Schwarz constant is the additive energy `E_r(μ_n)`. The session's exact measurement is that
`E_r(μ_n)/Wick = K_max^r ~ n^{0.77r}` — the energy is **genuinely super-Wick**, not by a method
artifact. So the energy/moment route *cannot* reach the Gaussian (Paley) tail: it overcounts the
bulk. Yet `M` itself stays `~√(n log q)` (spectral universality, prize-consistent). Hence a Paley
proof must bound the **max directly** via the multiplicative–additive (sum–product) interaction of
`B_T` with the difference set — the BGK mechanism — whose optimal exponent is open. This brick proves
the elementary bootstrap and pins precisely that it stops at the 4th moment. NOT closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW11

/-- **Self-bounding closure (proven).** If a nonnegative quantity `x` (think `x = |B_T|`) satisfies
`x · a ≤ b · √x` with `a > 0`, `b ≥ 0`, then `x ≤ b² / a²`. (Divide by `√x` when `x > 0`; the
`x = 0` case is trivial.) This is the algebraic heart of the difference-set bootstrap: with
`a = T² − n` and `b = n·√(2p)` it yields `|B_T| ≤ 2p·n²/(T²−n)²`. -/
theorem card_le_of_selfbounding (x a b : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 ≤ b)
    (hself : x * a ≤ b * Real.sqrt x) :
    x ≤ b ^ 2 / a ^ 2 := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- x = 0
    rw [← hx0]; positivity
  · -- x > 0: √x > 0, divide
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hxeq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    -- from x·a ≤ b·√x and x = √x·√x: √x·(√x·a) ≤ √x·b ⟹ √x·a ≤ b
    have hstep : Real.sqrt x * a ≤ b := by
      have h1 : Real.sqrt x * (Real.sqrt x * a) ≤ Real.sqrt x * b := by
        rw [← mul_assoc, hxeq]; linarith [hself, mul_comm b (Real.sqrt x)]
      exact le_of_mul_le_mul_left (by linarith [h1]) hsx
    -- √x ≤ b/a, so x = (√x)² ≤ (b/a)² = b²/a²
    have hsxle : Real.sqrt x ≤ b / a := by rw [le_div_iff₀ ha]; linarith [hstep]
    have : x = Real.sqrt x ^ 2 := by rw [sq]; exact hxeq.symm
    rw [this]
    have hba : (0:ℝ) ≤ b / a := by positivity
    calc Real.sqrt x ^ 2 ≤ (b / a) ^ 2 := by gcongr
      _ = b ^ 2 / a ^ 2 := by rw [div_pow]

/-- **The difference-set tail bound (proven, from the self-bounding inequality).** Packaging: given
the self-bounding inequality `|B|·(T²−n) ≤ n·√(2p)·√|B|` produced by the difference-set expansion
(near-Sidon Cauchy–Schwarz; supplied as `hself`), with `T² > n`, the large-period set satisfies
`|B| ≤ 2p·n²/(T²−n)²`. This is the 4th-moment-floor tail in self-bounding form. -/
theorem largePeriodSet_card_le (cardB p n T2 : ℝ) (hcard : 0 ≤ cardB) (hp : 0 ≤ p) (hn : 0 ≤ n)
    (hTn : n < T2)
    (hself : cardB * (T2 - n) ≤ n * Real.sqrt (2 * p) * Real.sqrt cardB) :
    cardB ≤ 2 * p * n ^ 2 / (T2 - n) ^ 2 := by
  have ha : 0 < T2 - n := by linarith
  have hb : 0 ≤ n * Real.sqrt (2 * p) := by positivity
  have h := card_le_of_selfbounding cardB (T2 - n) (n * Real.sqrt (2 * p)) hcard ha hb hself
  -- (n·√(2p))² = n²·2p
  have hsq : (n * Real.sqrt (2 * p)) ^ 2 = n ^ 2 * (2 * p) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq] at h
  calc cardB ≤ n ^ 2 * (2 * p) / (T2 - n) ^ 2 := h
    _ = 2 * p * n ^ 2 / (T2 - n) ^ 2 := by ring_nf

end ArkLib.ProximityGap.Frontier.AvW11

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW11.card_le_of_selfbounding
#print axioms ArkLib.ProximityGap.Frontier.AvW11.largePeriodSet_card_le
