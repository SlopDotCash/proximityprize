/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SparseCoeffZeros

/-!
# The PRIME side of the [349] DFT-uncertainty dichotomy: Tao's strong uncertainty → capacity (#407)

The #407 c.349 reframing (verified, mechanism Chebotarev): the far-line list-decoding radius over
`μ_n ≅ ZMod n` is `n − (min support of a (k+2)-Fourier-sparse function)`. Whether that radius lands
at **Johnson** `s* ~ √(kn)` or at **capacity** `s* = k+1` is controlled *entirely* by which discrete
uncertainty principle holds for `n`:

* **Composite `n` (incl. `n = 2^μ`) — Donoho–Stark, MULTIPLICATIVE (LANDED).**
  `|supp f| · |supp 𝓕f| ≥ n` (`_ZModDonohoStark.donoho_stark`). This is *tight for subgroups*, and
  `μ_{2^μ}` is a subgroup: a proper subgroup indicator has small physical support `|H|` and small
  Fourier support `n/|H|` (the dual subgroup), so a `t`-Fourier-sparse function can have physical
  support as small as `n/t`, i.e. as many as `n(1 − 1/t)` zeros. With `t = k+2` this is the
  Donoho–Stark list-decoding radius `≤ n(1 − 1/(k+2))`, the JOHNSON-scale bound
  (`_FourierSparseZeros.zeros_le_of_dft_sparse`, `_SparseCoeffZeros.sparse_coeff_zeros_le`).

* **Prime `p` — Tao, ADDITIVE (this file, conditional on `TaoUncertainty`).**
  `|supp f| + |supp 𝓕f| ≥ p + 1` (Tao 2005). This is STRICTLY STRONGER. A `t`-Fourier-sparse `f`
  then has physical support `≥ p + 1 − t`, i.e. **at most `t − 1` zeros**. With `t = k+2` a far line
  agrees with any codeword on `≤ k+1` points: `s* ≤ k+1`, CONSTANT in `n`, so `δ* = 1 − (k+1)/p →
  1 − ρ`, **CAPACITY**.

The gap between the two bounds — `n(1 − 1/t)` zeros (multiplicative) versus `t − 1` zeros (additive)
— **is exactly** the difference between the two uncertainty principles, hence the whole content of
the [349] Johnson-vs-capacity dichotomy.

## What is PROVEN here vs. what is the named open input

* **`TaoUncertainty p` is a NAMED `Prop`, NOT proven here.** It is Tao's additive support
  uncertainty principle:

  > **Tao (2005)**, *An uncertainty principle for cyclic groups of prime order*, Math. Res. Lett.
  > 12(1):121–127. For `p` prime and any nonzero `f : ZMod p → ℂ`,
  > `|supp f| + |supp 𝓕f| ≥ p + 1`.

  Tao's proof rests on **Chebotarev's theorem** (1926): for prime `p` *every* minor of the `p × p`
  DFT (Vandermonde-in-roots-of-unity) matrix is nonzero. That hard classical input is **not in
  Mathlib** (and is *false* for composite `n` — precisely why the bound is strong only for primes).
  Honesty contract: we never `sorry` it and never claim it proven; it is the open analytic input the
  prime-side reduction is *conditional on*.

* **`prime_capacity_of_tao` IS PROVEN here** (axiom-clean): the elementary reduction
  `TaoUncertainty p ⟹ (|supp 𝓕f| ≤ t, f ≠ 0) ⟹ |supp f| ≥ p + 1 − t`, i.e. `f` vanishes on at most
  `t − 1` points — the capacity radius. This mirrors the composite-side reduction
  `_FourierSparseZeros.zeros_le_of_dft_sparse` (which consumes `donoho_stark` the same way), so the
  two halves of the dichotomy share an identical proof shape and differ ONLY in their uncertainty
  input (`+` vs `·`).

* The optional sparse-COEFFICIENT / polynomial form `sparse_coeff_capacity_of_tao` mirrors
  `_SparseCoeffZeros.sparse_coeff_zeros_le` via the same `dft_dft` reindex.

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.SparseCoeffZeros

namespace ProximityGap.Frontier.PrimeCapacityUncertainty

/-- **Tao's additive support uncertainty principle for prime `p` (NAMED OPEN INPUT — not proven).**

> `∀ f : ZMod p → ℂ, f ≠ 0 → |supp f| + |supp 𝓕f| ≥ p + 1`.

This is the prime-order *additive* uncertainty principle of Tao (2005, MRL 12(1):121–127). It rests
on Chebotarev's theorem that every minor of the prime DFT matrix is nonzero — a hard classical fact
**not available in Mathlib**, and *false* for composite order. It is the genuine open input on which
the capacity reduction below is conditional; per the #407 honesty contract it is **never** proved or
`sorry`ed in-tree, only named and consumed. (Compare: the composite/`2^μ` side consumes the
*multiplicative* `_ZModDonohoStark.donoho_stark`, which IS proven, axiom-clean.) -/
def TaoUncertainty (p : ℕ) [NeZero p] : Prop :=
  ∀ (f : ZMod p → ℂ), f ≠ 0 → (p : ℕ) + 1 ≤ (supp f).card + (supp (𝓕 f)).card

variable {p : ℕ} [Fact p.Prime]

/-- **The capacity radius (PROVEN reduction).** Granting Tao's additive uncertainty `TaoUncertainty
p`, a nonzero `f : ZMod p → ℂ` whose DFT support has size `≤ t` has physical support `≥ p + 1 − t`,
i.e. `f` vanishes on **at most `t − 1` points**.

This is the prime/capacity counterpart of the composite-side
`_FourierSparseZeros.card_supp_ge_of_dft_sparse`: there the multiplicative `donoho_stark` gives
`|supp f| ≥ n/t`; here the *additive* Tao gives `|supp f| ≥ p + 1 − t`. With `t = k+2` (a far-line
`(k+2)`-spectrum-sparse obstruction) this is `|supp f| ≥ p − (k+1)`, i.e. `≤ k+1` zeros = capacity.

PROVEN: pure arithmetic on `TaoUncertainty` + `|supp 𝓕f| ≤ t`. Tao's principle itself is the named
open hypothesis. -/
theorem prime_capacity_of_tao (hTao : TaoUncertainty p) (f : ZMod p → ℂ) (hf : f ≠ 0)
    {t : ℕ} (ht : (supp (𝓕 f)).card ≤ t) :
    (p : ℕ) + 1 - t ≤ (supp f).card := by
  have hu : (p : ℕ) + 1 ≤ (supp f).card + (supp (𝓕 f)).card := hTao f hf
  omega

/-- **The capacity list-decoding radius (zero-count form, PROVEN reduction).** Granting
`TaoUncertainty p`, a nonzero `t`-Fourier-sparse `f : ZMod p → ℂ` vanishes on **at most `t − 1`
points**: `|{j : f j = 0}| ≤ t − 1`.

This is the constant-in-`p` capacity bound `s* ≤ k+1` (take `t = k+2`). Contrast the composite-side
`_FourierSparseZeros.zeros_le_of_dft_sparse`, whose multiplicative bound is `≤ n(1 − 1/t)` zeros
(Johnson scale). The two zero-count bounds — `t − 1` (prime/additive) versus `n(1 − 1/t)`
(composite/multiplicative) — are the two faces of the [349] dichotomy; their gap is *exactly* the
gap between the additive and multiplicative uncertainty principles. -/
theorem zeros_le_capacity_of_tao (hTao : TaoUncertainty p) (f : ZMod p → ℂ) (hf : f ≠ 0)
    {t : ℕ} (ht : (supp (𝓕 f)).card ≤ t) :
    ((univ.filter (fun j => f j = 0)).card) ≤ t - 1 := by
  -- zeros + |supp f| = p, and |supp f| ≥ p + 1 − t, so zeros ≤ t − 1.
  have hsupp : (p : ℕ) + 1 - t ≤ (supp f).card := prime_capacity_of_tao hTao f hf ht
  have hcompl : (univ.filter (fun j => f j = 0)).card + (supp f).card = p := by
    rw [supp]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ZMod p)))
      (p := fun j => f j = 0)
    simpa [ZMod.card, eq_comm, Finset.filter_not] using this
  -- the additive uncertainty gives |supp 𝓕f| ≥ 1, hence t ≥ 1, so p + 1 − t is the honest bound
  omega

/-- **Sparse-COEFFICIENT capacity form (PROVEN reduction, optional polynomial mirror).** Granting
`TaoUncertainty p`, if a coefficient signal `c : ZMod p → ℂ` is `t`-sparse (`|supp c| ≤ t`) and
nonzero, then its evaluation `𝓕 c` (the values of the corresponding degree-`< p` polynomial at the
`p`-th roots of unity) vanishes on **at most `t − 1`** of the `p` frequencies — capacity.

Mirrors `_SparseCoeffZeros.sparse_coeff_zeros_le` (Johnson/composite version) via the `dft_dft`
reindex `|supp 𝓕(𝓕 c)| = |supp c|`. With `t = k+2` (the far-line agreement polynomial) this is the
constant capacity radius `≤ k+1` on the agreement set. -/
theorem sparse_coeff_capacity_of_tao (hTao : TaoUncertainty p) (c : ZMod p → ℂ) (hc : c ≠ 0)
    {t : ℕ} (ht : (supp c).card ≤ t) :
    ((univ.filter (fun j => (𝓕 c) j = 0)).card) ≤ t - 1 := by
  -- 𝓕 c ≠ 0 (dft injective), and |supp 𝓕(𝓕 c)| = |supp c| ≤ t.
  have hFcne : 𝓕 c ≠ 0 := by
    intro h
    apply hc
    have : 𝓕 c = 𝓕 0 := by rw [h, map_zero]
    exact dft.injective this
  refine zeros_le_capacity_of_tao hTao (𝓕 c) hFcne (t := t) ?_
  rw [supp_dft_dft_card]
  exact ht

/-! ## The dichotomy, stated explicitly

The two halves sit side by side, sharing the SAME reduction shape and differing only in their
uncertainty input. For a nonzero `t`-Fourier-sparse signal on `ZMod n` (`t = k+2`):

* **composite (LANDED, any `n` incl. `2^μ`):** Donoho–Stark MULTIPLICATIVE
  `|supp f|·|supp 𝓕f| ≥ n` (PROVEN) → reduction `card_supp_ge_of_dft_sparse`
  → `≤ n(1 − 1/t)` zeros → Johnson radius `√(kn)`.
* **prime (this file, `p` prime):** Tao ADDITIVE `|supp f| + |supp 𝓕f| ≥ p+1` (NAMED OPEN)
  → reduction `prime_capacity_of_tao` → `≤ t − 1` zeros → capacity radius `k+1`.

The capacity radius is always at least as strong as (≤) the Johnson radius: the two principles agree
on direction, and the *gap* `n(1 − 1/t) − (t − 1)` is the quantitative content of the [349]
dichotomy — it is `0` at the degenerate `t = n`, and `Θ(n)` for `t = O(1)` (the prize regime). We
record the direct zero-count comparison `capacity_le_johnson_radius` (unconditional, no
`TaoUncertainty` needed). -/

/-- **The dichotomy is one-directional: capacity ≤ Johnson.** For `1 ≤ t ≤ n`, the prime/additive
zero-count bound `t − 1` is at most the composite/multiplicative bound `n(1 − 1/t)`. So the capacity
radius (prime side) is always at least as strong as (≤) the Johnson radius (composite side): the two
principles agree on direction, and the gap `n(1−1/t) − (t−1)` is the quantitative content of the
[349] dichotomy (`0` at the degenerate `t = n`, `Θ(n)` for `t = O(1)`, the prize regime). PROVEN
(real arithmetic, unconditional — no `TaoUncertainty` needed). -/
theorem capacity_le_johnson_radius {n t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) :
    ((t : ℝ) - 1) ≤ (n : ℝ) * (1 - 1 / t) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have htnR : (t : ℝ) ≤ n := by exact_mod_cast htn
  have ht1R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  -- n(1 − 1/t) = n − n/t.  The bound (t − 1) ≤ n − n/t is equivalent (×t > 0) to
  -- (t − 1)·t ≤ (n − n/t)·t = n·t − n = n·(t − 1), i.e. t ≤ n (since t − 1 ≥ 0).
  have hinv : (n : ℝ) * (1 - 1 / (t : ℝ)) = (n : ℝ) - (n : ℝ) / (t : ℝ) := by
    rw [mul_sub, mul_one, mul_one_div]
  rw [hinv]
  -- `n/t ≥ 1` since `n ≥ t > 0`; and `(t − 1)·t ≤ n·t − n` i.e. `t² ≤ n·t` from `t ≤ n`.
  have hdiv : (n : ℝ) / (t : ℝ) * (t : ℝ) = (n : ℝ) := div_mul_cancel₀ _ (ne_of_gt htpos)
  have hdivpos : (0 : ℝ) ≤ (n : ℝ) / (t : ℝ) := div_nonneg (by positivity) (le_of_lt htpos)
  nlinarith [htnR, htpos, ht1R, hdiv, hdivpos,
    mul_nonneg (sub_nonneg.mpr htnR) (le_of_lt htpos), mul_pos htpos htpos]

end ProximityGap.Frontier.PrimeCapacityUncertainty

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`).
`TaoUncertainty` is a `def … : Prop` (a named hypothesis), so it carries no axioms; the PROVEN
reductions below consume it as an argument. -/
#print axioms ProximityGap.Frontier.PrimeCapacityUncertainty.prime_capacity_of_tao
#print axioms ProximityGap.Frontier.PrimeCapacityUncertainty.zeros_le_capacity_of_tao
#print axioms ProximityGap.Frontier.PrimeCapacityUncertainty.sparse_coeff_capacity_of_tao
#print axioms ProximityGap.Frontier.PrimeCapacityUncertainty.capacity_le_johnson_radius
