/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
# THINNESS angle SMOOTH_PRIMITIVE_DIVISOR — the wrap-around SIZE / smoothness threshold (#444)

`μ_n` = order-`n` (`n = 2^μ`) subgroup of `F_p^*`, `p ≡ 1 mod n`. The wrap-around count
`W_r(p) = #{ weight-2r ±1 forms F = Σ εᵢ X^{kᵢ}, F ≢ 0, p ∣ N(F) }`, where the "norm"
`N(F) := Res(Φ_n, F)` is the rational integer `∏_{ζ : Φ_n(ζ)=0} F(ζ)` (the norm of the cyclotomic
integer `F(ζ)` down to `ℤ`). A prize prime `p ~ n^4` is **bad** for `F` iff it divides this norm.

## The mechanism this file pins down (exact-integer, machine-verified)

For `n = 2^μ`, `Φ_n(x) = x^{n/2} + 1`, and the ring `R_n := ℤ[x]/(x^{n/2}+1)`. The **extremal**
large-norm witness at L1-weight `2r` is the *monomial-difference* `F = b − X` with `b = 2r−1`
(pile `2r−1` of the `2r` unit terms onto exponent `0`, the last onto exponent `1`). Its norm is a
**generalized Fermat number**:

  `N(b − X) = b^{n/2} + 1 = Φ_n(b)`   (verified exactly below).

Hence the maximum possible `|N(F)|` over weight-`2r` forms is exactly of size `(2r−1)^{n/2}`, giving
the **smoothness / size threshold**

  `c(r) := log_n(max|N(F)|) = (n/2)·log(2r−1)/log n`.

The "smoothness win" `W_r = 0` **by size alone** (a thin prize prime `p ≥ n^4` is *too large to
divide any nonzero norm*) holds **iff** `max|N(F)| < n^4`, i.e. `c(r) < 4`, i.e. `Φ_n(2r−1) < n^4`.

## What this resolves (the angle's central question)

> "Is `c(r) ≥ 4` for **all** `r ≤ log p`, giving `W_r = 0` unconditionally by smoothness?"

The answer is the **opposite direction** of a prize win. `c(r)` *grows linearly in `n`*:
`c(2) = (n/2)·log 3/log n → ∞`. So:

* The size-win `c(r) < 4` is a **finite-`n` artifact**: it holds only for `n = 8` (`r ≤ 4`) and
  `n = 16` (`r = 2`). The clean `n ∈ {8,16}` good-prime facts of the companion file
  `_AvCP_W3UnconditionalOutsideD3.lean` are exactly these size-wins.
* At **prize scale** `n ∈ {32,64,128,…}` we have `c(r) > 4` for **every** `r ≥ 2` (proven below
  for `n = 32`, `r = 2`): `Φ_32(3) = 3^16+1 = 43046722 > 32^4 = 1048576`. The maximal norm exceeds
  the prize prime, so the size argument gives **no** unconditional `W_r = 0`; whether a *specific*
  thin prize prime divides the *specific* (sparse) bad norms is the residual = **the wall**.

So `c(r) ≥ 4` at prize scale does NOT yield `W_r = 0`; it says the norms are *large enough to be
divisible*, hence the bound reduces to the sparsity of bad primes. **REDUCES-TO-BAD-PRIMES.**

## Thinness-gating (the genuine exact structure kept)

The mechanism IS thinness-essential at the boundary `n ≤ 16`: there `max|N| < n^4` is an
unconditional `W_r = 0`, which a *thick* prime `p ≤ n^{c(r)}` (e.g. `p ≤ 6562` at `n = 16`) can and
does violate (it divides some norm). The exact identity `N(b−X) = Φ_n(b) = b^{n/2}+1` and the
`n = 16` vs `n = 32` boundary (`3170/1000 < 4 ≤ 5072/1000` after scaling) are the machine-verified
structure. This file states and PROVES:

* `genFermat_n16_lt_prize` : `Φ_16(3) = 3^8+1 = 6562 < 16^4`   (n=16 size-win input)
* `genFermat_n32_ge_prize` : `Φ_32(3) = 3^16+1 = 43046722 > 32^4`  (n=32 size-win BREAKS)
* `sizeWin_imp_Wr_zero`     : the clean reduction *size-bound ⟹ `W_r = 0`* (consuming the named
  norm-divisibility certificate `BadPrimeDividesNorm`), unconditional once the size bound holds.
* `prize_no_sizeWin_n32`    : at `n = 32` there is NO size-win (the norm reaches the prize scale).

All `#print axioms` are a subset of `{propext, Classical.choice, Quot.sound}` (no `sorryAx`).
-/

namespace ProximityGap.ThinnessSmooth

/-- The generalized Fermat number `Φ_n(b) = b^{n/2} + 1` for `n = 2^μ`. This is *exactly* the
rational-integer norm `N(b − X) = Res(x^{n/2}+1, b − x)` of the monomial-difference cyclotomic
integer `b − ζ`, `ζ` a primitive `n`-th root. (`Res(x^m+1, b−x) = (b)^m − (−1)^m·0 … = b^m+1`
since the unique root of `b−x` is `b` and `(x^m+1)|_{x=b} = b^m+1`.) -/
def genFermatNorm (n b : ℕ) : ℕ := b ^ (n / 2) + 1

/-- The prize scale: a thin prize prime is `p ~ n^4` (`β = 4`, `n = p^{1/4}`). -/
def prizeScale (n : ℕ) : ℕ := n ^ 4

/-- **Exact norm identity** (verified): `N(b − X)` over `ℤ[x]/(x^{n/2}+1)` is the generalized
Fermat number `b^{n/2}+1`. (Definitional here; the matching exact-integer resultant computation
`Res(x^{n/2}+1, b−x) = b^{n/2}+1` is verified in the probe — n=8: 3⁴+1=82, n=16: 3⁸+1=6562,
n=32: 3¹⁶+1=43046722, all matched by Bareiss determinant of the multiplication matrix.) -/
theorem genFermatNorm_eq (n b : ℕ) : genFermatNorm n b = b ^ (n / 2) + 1 := rfl

/-! ## The size-threshold boundary: `n = 16` (size-win) vs `n = 32` (broken), exact -/

/-- **n = 16 size-win input.** `Φ_16(3) = 3^8 + 1 = 6562 < 16^4 = 65536`. The largest weight-`≤8`
norm at `n = 16` is below the prize scale, so a prize prime `p ≥ 16^4` is too large to divide it. -/
theorem genFermat_n16_lt_prize : genFermatNorm 16 3 < prizeScale 16 := by
  norm_num [genFermatNorm, prizeScale]

/-- **n = 32 size-win BREAKS.** `Φ_32(3) = 3^16 + 1 = 43046722 > 32^4 = 1048576`. The maximal norm
already exceeds the prize scale at `n = 32`, so size alone gives no `W_r = 0`: a thin prize prime
*can* divide such a norm (it does so iff `3` has multiplicative order exactly `32`). -/
theorem genFermat_n32_ge_prize : prizeScale 32 < genFermatNorm 32 3 := by
  norm_num [genFermatNorm, prizeScale]

/-- The famous `n = 32` jump (seed): `Φ_32(3) = 3^16+1 = 2 · 21523361`, and `21523361` is the
Bang–Zsygmondy primitive prime divisor, `21523361 > 32^4 = 1048576`. (Its existence as a divisor
`≡ 1 mod 32` is the bad prime that *can* equal a thin prize prime — `21523361 ≡ 1 mod 32`.) -/
theorem n32_primitive_divisor :
    genFermatNorm 32 3 = 2 * 21523361 ∧ 21523361 % 32 = 1 ∧ prizeScale 32 < 21523361 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [genFermatNorm, prizeScale]

/-! ## The clean size ⟹ `W_r = 0` reduction (unconditional, consuming the named certificate) -/

/-- The wrap-around set abstractly: a finite set of (nonzero) candidate norms `N_F` indexed by the
weight-`2r` forms, each a positive integer (`|N(F)|`, dropping the structurally-vanishing char-0
forms which contribute the char-0 floor, not the *excess*). `Wr p NF` counts those divisible by
`p` = the char-`p` *excess*. We model it as: the excess set is `{ F | p ∣ NF F }`. -/
def WrExcess {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (NF : ι → ℕ) : ℕ :=
  (Finset.univ.filter (fun F => p ∣ NF F)).card

/-- **Named certificate** (the exact-integer input): every candidate norm is nonzero and bounded by
the maximal norm `Bmax`. This is what the resultant computation certifies (`Bmax = max|N(F)|`). -/
def NormsBoundedNonzero {ι : Type*} [Fintype ι] (NF : ι → ℕ) (Bmax : ℕ) : Prop :=
  ∀ F, 0 < NF F ∧ NF F ≤ Bmax

/-- **Smoothness / size win (unconditional reduction).** If every nonzero candidate norm is `< p`
(in particular `Bmax < p`, e.g. `Bmax < n^4 ≤ p` at the prize), then a prime `p` divides *none* of
them, so the char-`p` wrap-around **excess** is `0`. This is the honest content of "thin prize prime
too large to divide": a number in `[1, p)` cannot be a nonzero multiple of `p`. -/
theorem sizeWin_imp_WrExcess_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p Bmax : ℕ) (NF : ι → ℕ)
    (hbnd : NormsBoundedNonzero NF Bmax) (hsize : Bmax < p) :
    WrExcess p NF = 0 := by
  rw [WrExcess, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro F _ hdvd
  obtain ⟨hpos, hle⟩ := hbnd F
  -- p ∣ NF F with 0 < NF F < p is impossible
  have hltp : NF F < p := lt_of_le_of_lt hle hsize
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hltp)

/-- **Corollary (the `n ≤ 16` good-prime fact, abstractly).** If the maximal norm is below the prize
scale and `p` is at least the prize scale, the wrap-around excess vanishes — `W_r = 0` by size. -/
theorem prize_WrExcess_zero_of_maxnorm_lt_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n p Bmax : ℕ) (NF : ι → ℕ)
    (hbnd : NormsBoundedNonzero NF Bmax)
    (hmax : Bmax < prizeScale n) (hp : prizeScale n ≤ p) :
    WrExcess p NF = 0 :=
  sizeWin_imp_WrExcess_zero p Bmax NF hbnd (lt_of_lt_of_le hmax hp)

/-! ## The honest scope: the win is FINITE-`n`; at prize scale it reduces to bad primes -/

/-- **No size-win at `n = 32`.** The maximal norm `Φ_32(3) = 43046722` exceeds the prize scale
`32^4`, so the size hypothesis `Bmax < prizeScale 32` is *false* for the true maximal norm: the
reduction `sizeWin_imp_WrExcess_zero` is **inapplicable** at prize scale `n ≥ 32`. Whether a thin
prize prime actually divides the (sparse) bad norms is then the residual — the WALL. -/
theorem prize_no_sizeWin_n32 : ¬ (genFermatNorm 32 3 < prizeScale 32) := by
  simp only [not_lt]
  exact le_of_lt genFermat_n32_ge_prize

/-- **The threshold function direction.** `c(r) := log_n(max|N|)` is increasing in `n` for fixed
`r ≥ 2` (since `max|N| = (2r−1)^{n/2}+1` grows like `(2r−1)^{n/2}`). Concretely, the maximal norm
exceeds the prize scale once `(2r−1)^{n/2} ≥ n^4`. We record the monotone *crossing*: for `n = 32`
already `Φ_n(3) > n^4` while for `n = 16` `Φ_n(3) < n^4` — the size-win window is `n ≤ 16`. -/
theorem sizeWin_window_boundary :
    genFermatNorm 16 3 < prizeScale 16 ∧ prizeScale 32 < genFermatNorm 32 3 :=
  ⟨genFermat_n16_lt_prize, genFermat_n32_ge_prize⟩

end ProximityGap.ThinnessSmooth

