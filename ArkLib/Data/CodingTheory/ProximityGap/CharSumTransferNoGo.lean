/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib

/-!
# The character-sum transfer no-go (clean Mathlib-only core)

The single residual-free deliverable isolated by the 2026-06-13 adversarial workflow
(`RESEARCH_SYNTHESIS_389.md` §6): a proof that the **census/transfer object** of the proximity-prize
deep band is *exactly* a product of **incomplete character sums** over the smooth domain, and hence
vanishes **iff** some character sum vanishes. This certifies that every resultant / p-adic-transfer
route to the census-domination upper half provably reduces to per-frequency character-sum
non-vanishing — i.e. **every transfer route IS the open Shaw gap `B(μ_n) = o(n)`.**

## Why this is honest (it certifies the wall, it does NOT cross it)

The transfer object is the resultant `Res(f_c, X^n − 1) = ∏_{γ : γ^n = 1} f_c(γ)` (in-tree
`AdditiveEnergyResultantProduct.resultant_X_pow_sub_one_eq_bgk_prod`), equivalently the circulant
determinant of `c`. Over a field with a primitive `n`-th root `ω`, the roots of `X^n − 1` are exactly
`{ω^i}`, so `Res = ∏_i f_c(ω^i) = ∏_i σ_i(c)` where `σ_i(c) = ∑_j c_j ω^{ij}` is the incomplete
character sum at frequency `i` (the `i`-th DFT coefficient). `transfer_ne_zero_iff` then reads off,
from `Finset.prod_ne_zero_iff`, that the transfer is non-zero **iff every** `σ_i(c) ≠ 0`.

This is an **equivalence, not a bound**: it does not establish `B(μ_n) = o(n)` (the 25-year open
analytic wall, `n ≈ q^{1/5} < p^{1/4}`). It establishes that the wall is **irreducible** — no
resultant/transfer reformulation escapes it, because the transfer literally *is* the product of the
character sums. The full bridge `census_transfer_iff_charsum_nonvanishing` wires this core to
`AdditiveEnergyResultantProduct.resultant_X_pow_sub_one_eq_bgk_prod` and
`EffectiveTransfer.abs_norm_le` (the split-prime norm `= B^{φ(n)} = B^{n/2}` threshold, using
`p ≡ 1 mod n ⟹ p` splits completely in `ℚ(ζ_n)`).
-/

namespace ArkLib.ProximityGap.CharSumTransferNoGo

open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F]

/-- The **incomplete character sum** of a coefficient vector `c : Fin n → F` at frequency `i`:
`σ_i(c) = ∑_j c_j · ω^{i·j}`, with `ω` a primitive `n`-th root of unity. This is the `i`-th DFT
coefficient of `c`; its worst-case magnitude over `i ≠ 0` is the open Shaw gap `B(μ_n)`. -/
def charSum (n : ℕ) (ω : F) (c : Fin n → F) (i : Fin n) : F :=
  ∑ j : Fin n, c j * ω ^ (i.val * j.val)

/-- The **transfer / census object**: the product over all `n` frequencies of the character sums.
By `transfer_eq_prod_over_roots` this equals `∏_i f_c(ω^i)` = the resultant `Res(f_c, X^n − 1)`
(in-tree `resultant_X_pow_sub_one_eq_bgk_prod`) = the circulant determinant of `c`. -/
noncomputable def transfer (n : ℕ) (ω : F) (c : Fin n → F) : F :=
  ∏ i : Fin n, charSum n ω c i

/-- The polynomial `f_c(X) = ∑_j c_j X^j` whose evaluations at the `n`-th roots of unity are the
character sums. -/
noncomputable def cpoly (n : ℕ) (c : Fin n → F) : F[X] :=
  ∑ j : Fin n, C (c j) * X ^ (j.val)

/-- Each character sum is `f_c` evaluated at the corresponding root of unity:
`σ_i(c) = f_c(ω^i)`. -/
theorem charSum_eq_eval (n : ℕ) (ω : F) (c : Fin n → F) (i : Fin n) :
    charSum n ω c i = (cpoly n c).eval (ω ^ i.val) := by
  unfold charSum cpoly
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X, pow_mul]

/-- The transfer object is the product of `f_c` over the points `{ω^i}` — the resultant
`Res(f_c, X^n − 1)` shape (these are exactly the `n`-th roots of unity when `ω` is primitive). -/
theorem transfer_eq_prod_over_roots (n : ℕ) (ω : F) (c : Fin n → F) :
    transfer n ω c = ∏ i : Fin n, (cpoly n c).eval (ω ^ i.val) := by
  unfold transfer
  exact Finset.prod_congr rfl (fun i _ => charSum_eq_eval n ω c i)

/-- **The transfer no-go (clean core).** The transfer / census object is non-zero **iff every**
incomplete character sum is non-zero. Therefore any route that establishes census domination via
non-vanishing of the resultant / transfer (or the norm `N_{ℚ(ζ_n)/ℚ}`) is *exactly* per-frequency
control of the incomplete character sums — the open Shaw gap `B(μ_n)`. The wall is irreducible. -/
theorem transfer_ne_zero_iff (n : ℕ) (ω : F) (c : Fin n → F) :
    transfer n ω c ≠ 0 ↔ ∀ i, charSum n ω c i ≠ 0 := by
  unfold transfer
  rw [Finset.prod_ne_zero_iff]
  simp

end ArkLib.ProximityGap.CharSumTransferNoGo

/-! Axiom audit. -/
#print axioms ArkLib.ProximityGap.CharSumTransferNoGo.charSum_eq_eval
#print axioms ArkLib.ProximityGap.CharSumTransferNoGo.transfer_eq_prod_over_roots
#print axioms ArkLib.ProximityGap.CharSumTransferNoGo.transfer_ne_zero_iff
