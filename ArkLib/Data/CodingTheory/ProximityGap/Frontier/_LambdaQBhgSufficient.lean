/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# A `B_h[g]` sufficient condition for the Λ(2h) face of the prize (#444)

THE OBJECT (issue #444, ABF26 ePrint 2026/680). `η : Z_p → ℂ`, `η(b) = Σ_{x∈μ_n} e_p(b·x)`, where
`μ_n` is the group of `n`-th roots of unity (`n = 2^μ`). The prize floor
`M = ‖η‖_∞ = max_{b≠0}|η(b)| ≤ C·√(n·log m)` is the **Λ(q) inequality** at `q ≈ 2 log m`. The even-`q`
case `q = 2h` is the **energy moment**
`‖η‖_{2h}^{2h} = E_h(μ_n) := #{(x,y) ∈ μ_n^h × μ_n^h : Σ xᵢ = Σ yᵢ}`, and the worst-case `M` sees the
mean-zero (DC-subtracted) object `μ_{2h} := (p·E_h − n^{2h})/(p−1)`. The prize at depth `h` is
`μ_{2h} ≤ Wick_h := (2h−1)‼·n^h`.

## The `B_h[g]` packaging (this file)

This is the **cleanest structural sufficient condition** for the even-`q` face. Write, for `s ∈ Z_p`,
the `h`-fold **representation count** `r_h(s) := #{(x₁,…,x_h) ∈ μ_n^h : x₁ + ⋯ + x_h = s}`. A set is
**`B_h[g]`** (a `B_h[g]` set, in the additive-combinatorics sense) when *every* element has at most `g`
representations as an `h`-fold sum: `r_h(s) ≤ g` for all `s`.

The energy is the sum of squared representation counts (Cauchy–Schwarz / the standard "energy = ℓ²
of the representation function" identity), with total mass `n^h`:
`E_h = Σ_s r_h(s)²`,  `Σ_s r_h(s) = n^h`.
Hence the elementary bound
`E_h = Σ_s r_h(s)² ≤ (max_s r_h(s)) · Σ_s r_h(s) ≤ g · n^h`,
i.e. **`B_h[g] ⟹ E_h ≤ g·n^h`**. Since `(2h−1)‼ ≥ 1`, this gives the prize-shaped bound
`μ_{2h} ≤ E_h ≤ g·n^h ≤ g·(2h−1)‼·n^h = g·Wick_h`.

So **`μ_n` is `B_h[g]` ⟹ `μ_{2h} ≤ g·Wick_h` ⟹ the prize-at-depth-`h` (with constant `g^{1/2h}`).**
In `L^{2h}` constant language: `‖η‖_{2h} ≤ (g·(2h−1)‼)^{1/2h}·√n`, i.e. `B_h[g]` gives the Λ(2h)
inequality with constant `≤ g^{1/2h}·(2h−1)‼^{1/2h}`.

## Status (honest) — what is proven vs. the named open residual

This file proves, **axiom-clean and abstractly** (the representation count `r` is an arbitrary
nonneg function on a `Fintype` with the two structural facts `r ≤ g` pointwise and `Σ r = n^h`):

* `energy_le_of_Bhg` — `B_h[g] ⟹ E_h := Σ r² ≤ g·n^h` (the representation-multiplicity bound bounds the
  `2h`-th moment). This is the entire content of the implication; it is unconditional.
* `mu2h_le_of_Bhg` — chaining to the DC-subtracted moment `μ_{2h} ≤ E_h ≤ g·(2h−1)‼·n^h = g·Wick_h`,
  given the (proven elsewhere, here hypothesised) DC-subtraction inequality `μ_{2h} ≤ E_h` and
  `1 ≤ (2h−1)‼`.
* `prize_at_depth_of_Bhg` — the end-to-end packaging: `μ_n` is `B_h[g]` at depth `h` with `g ≤ (2h−1)‼`
  (the *Gaussian* representation budget) ⟹ `μ_{2h} ≤ Wick_h`, the open core at depth `h`.

**The named open residual** is exactly the deep-`h` hypothesis of `prize_at_depth_of_Bhg`:
`MaxRepMultiplicityBudget` — that the maximum `h`-fold representation multiplicity `g_h(μ_n) := max_s r_h(s)`
of `μ_n` stays within the **Gaussian budget** `(2h−1)‼` for `h ≈ log m`. This is the **deep-`k` energy =
the BGK resonance**: a *random* set has `g_h ≈ (2h−1)‼` (Wick), and the question is whether the rank-1
multiplicative structure of `μ_n` deviates upward before the union-bound saddle. `μ_n` is **not** `B_h[1]`
(a Sidon/`B_h` set) — already `E_2 = 3n²−3n > n²` forces `g_2 ≥ 2` (antipodal pairs `x + (−x) = 0`), so
the all-`h` `B_h[1]` (Sidon) statement is FALSE; the live target is the *finite-`h`, bounded-`g`* version,
strictly weaker than Sidon (cf. Pisier `Λ(q) ≤ A√q` all-`q` ⟺ Sidon, arXiv:1704.02969). Naming
`g_h ≤ (2h−1)‼` is NOT discharging it — it is the BGK wall in representation-multiplicity coordinates.

Issue #444.
-/

namespace ProximityGap.Frontier.LambdaQBhg

open Finset

variable {ι : Type*} [Fintype ι]

/-- **The representation-function energy identity, as a bound.** If `r : ι → ℝ` is the `h`-fold
representation count (`r s = #{tuples summing to s}`, so `0 ≤ r`), with total mass `∑ r = N` (here
`N = n^h`, the number of `h`-tuples) and the **`B_h[g]` bound** `r s ≤ g` for every `s`, then the energy
`E := ∑ r²` satisfies `E ≤ g·N`. This is the entire content of `B_h[g] ⟹ E_h ≤ g·n^h`: the squared
representation function is dominated termwise by `g` times the representation function. -/
theorem energy_le_of_Bhg (r : ι → ℝ) (g N : ℝ)
    (hr : ∀ s, 0 ≤ r s) (hg : ∀ s, r s ≤ g) (hsum : ∑ s, r s = N) :
    ∑ s, (r s) ^ 2 ≤ g * N := by
  calc ∑ s, (r s) ^ 2 = ∑ s, r s * r s := by
        simp [sq]
    _ ≤ ∑ s, g * r s := by
        refine Finset.sum_le_sum ?_
        intro s _
        exact mul_le_mul_of_nonneg_right (hg s) (hr s)
    _ = g * ∑ s, r s := by rw [Finset.mul_sum]
    _ = g * N := by rw [hsum]

/-- **`B_h[g] ⟹ μ_{2h} ≤ g·Wick_h`.** Given the energy bound `E ≤ g·N` with `N = n^h` (from
`energy_le_of_Bhg`), the DC-subtraction inequality `μ₂ₕ ≤ E` (the mean-zero moment is bounded by the full
energy; proven in the substrate as `μ_{2h} = (p·E − n^{2h})/(p−1) ≤ E`), and `1 ≤ Wick'` where
`Wick' = (2h−1)‼` is the Gaussian double-factorial factor, we conclude the prize-shaped bound
`μ₂ₕ ≤ g·Wick'·nh` (`= g·Wick_h`, with `Wick_h = Wick'·nh = (2h−1)‼·n^h`). -/
theorem mu2h_le_of_Bhg (E mu2h g nh Wick' : ℝ)
    (hE : E ≤ g * nh) (hDC : mu2h ≤ E) (hg : 0 ≤ g) (hnh : 0 ≤ nh) (hWick : 1 ≤ Wick') :
    mu2h ≤ g * Wick' * nh := by
  have h1 : E ≤ g * Wick' * nh := by
    refine le_trans hE ?_
    have : g * nh ≤ g * Wick' * nh := by
      have hgnh : 0 ≤ g * nh := mul_nonneg hg hnh
      nlinarith [mul_le_mul_of_nonneg_left hWick hg, hnh]
    exact this
  exact le_trans hDC h1

/-- **End-to-end: `μ_n` is `B_h[g]` with Gaussian budget ⟹ the open core at depth `h`.**
Abstractly: the representation count `r` (`0 ≤ r`, total mass `∑ r = nh = n^h`) is `B_h[g]`
(`r s ≤ g`) with `g` within the **Gaussian representation budget** `g ≤ Wick'` (`= (2h−1)‼ ≥ 1`), and the
DC-subtraction `μ₂ₕ ≤ E := ∑ r²` holds. Then `μ₂ₕ ≤ Wick' · nh = Wick_h` — the open core at depth `h`,
hence (via `_LambdaQRudinEndToEnd`, the forward Λ(q) ⟹ floor direction) the prize floor at depth `h`.

This is the cleanest packaging of the even-`q` Λ(q) face: the entire prize-at-depth-`h` is the single
representation-multiplicity inequality `g_h(μ_n) ≤ (2h−1)‼` (`g_h := max_s r s`). The deep-`h` instance of
this hypothesis is the named open residual = the BGK resonance (see module docstring). -/
theorem prize_at_depth_of_Bhg (r : ι → ℝ) (mu2h g nh Wick' : ℝ)
    (hr : ∀ s, 0 ≤ r s) (hg0 : 0 ≤ g) (hgB : ∀ s, r s ≤ g)
    (hsum : ∑ s, r s = nh) (hnh : 0 ≤ nh)
    (hbudget : g ≤ Wick') (hWick : 1 ≤ Wick')
    (hDC : mu2h ≤ ∑ s, (r s) ^ 2) :
    mu2h ≤ Wick' * nh := by
  -- energy ≤ g·nh
  have hE : ∑ s, (r s) ^ 2 ≤ g * nh := energy_le_of_Bhg r g nh hr hgB hsum
  -- μ₂ₕ ≤ E ≤ g·nh ≤ Wick'·nh
  have h1 : mu2h ≤ g * nh := le_trans hDC hE
  have h2 : g * nh ≤ Wick' * nh := mul_le_mul_of_nonneg_right hbudget hnh
  exact le_trans h1 h2

/-- **The named open residual, as a `Prop`.** `MaxRepMultiplicityBudget r Wick'` says the maximum
`h`-fold representation multiplicity `g_h := max_s r s` of `μ_n` is within the Gaussian budget
`(2h−1)‼ = Wick'`. Packaged: there exists a bound `g ≤ Wick'` dominating every representation count. This
is the deep-`k` energy = the BGK resonance (open at the prize scale `n = 2^30`, `h ≈ log m`); naming it is
modularity, not a discharge (§6 honesty contract). -/
def MaxRepMultiplicityBudget (r : ι → ℝ) (Wick' : ℝ) : Prop :=
  ∃ g : ℝ, 0 ≤ g ∧ g ≤ Wick' ∧ (∀ s, r s ≤ g)

/-- The residual is exactly what `prize_at_depth_of_Bhg` consumes: `MaxRepMultiplicityBudget` (the open
deep-`h` budget) + the structural facts (nonneg representation counts, total mass `n^h`, Gaussian factor
`≥ 1`, DC-subtraction) ⟹ the open core `μ₂ₕ ≤ Wick_h`. -/
theorem prize_at_depth_of_budget (r : ι → ℝ) (mu2h nh Wick' : ℝ)
    (hr : ∀ s, 0 ≤ r s) (hsum : ∑ s, r s = nh) (hnh : 0 ≤ nh)
    (hWick : 1 ≤ Wick') (hDC : mu2h ≤ ∑ s, (r s) ^ 2)
    (hbudget : MaxRepMultiplicityBudget r Wick') :
    mu2h ≤ Wick' * nh := by
  obtain ⟨g, hg0, hgW, hgB⟩ := hbudget
  exact prize_at_depth_of_Bhg r mu2h g nh Wick' hr hg0 hgB hsum hnh hgW hWick hDC

end ProximityGap.Frontier.LambdaQBhg

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.LambdaQBhg.energy_le_of_Bhg
#print axioms ProximityGap.Frontier.LambdaQBhg.mu2h_le_of_Bhg
#print axioms ProximityGap.Frontier.LambdaQBhg.prize_at_depth_of_Bhg
#print axioms ProximityGap.Frontier.LambdaQBhg.prize_at_depth_of_budget
