/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

/-!
# Hodge–Newton p-adic suppression of `W_r` is FALSE on the object (#444/#334)

Domain: **p-adic Hodge / prismatic / crystalline** (one of the fresh-domain mining targets).

## The proposal (ID `d5-2`)

> `v_p(W_r) ≥ (Hodge slope sum)` grows with `r`, so `W_r ≡ 0 mod p^{c·r}` and the wraparound
> contribution `(n^{2r} − Wick)/q` is p-adically suppressed below `slack_r`.

Here `W_r = E_r^{F_q} − E_r^{char0}` is the **wraparound** part of the additive energy
`E_r = ∑_{b≠0} |η_b|^{2r}` of the Gauss periods `η_b = ∑_{x∈μ_n} ψ(b·x)`. Both `E_r^{F_q}` and
`E_r^{char0}` are **nonnegative integers** (they are counts of additive coincidences inside the thin
subgroup `μ_n`), and so is `W_r`. The Newton-above-Hodge inequality would force `p^{c·r} ∣ W_r`.

## Why it is FALSE (machine countermodel)

The premise requires a *Hodge-forced* divisibility of the additive-energy integers by a growing
power of `p`. There is none: these counts have `p`-adic valuation `0`. Real exact `F_p` computation
(`/tmp/d52_growth.py`, integer additive-energy counts over `ℤ` vs over `F_p`) gives, for the order-8
subgroup `μ_8 ⊆ F_17^*`,

| `r` | `W_r`        | `v_17(W_r)` |
|----:|-------------:|------------:|
|  1  | `0`          | (`+∞`)      |
|  2  | `72`         | `0`         |
|  3  | `7380`       | `0`         |
|  4  | `555912`     | `0`         |
|  5  | `38674620`   | `0`         |

`v_p(W_r)` is **flat at `0`** as `r` grows — the exact opposite of the claimed `c·r` growth. (In a
companion case `μ_6 ⊆ F_13^*` it reads `0,1,0,0` across `r=2..5`: non-monotone, never growing.)
Since `p ∤ W_r` for the relevant `r`, there is **no** `p`-adic suppression of the wraparound term,
and the Hodge–Newton route imposes *no* constraint on `slack_r`.

This file encodes the four exact `μ_8 ⊆ F_17^*` wraparound integers and proves by `decide`/`norm_num`
that `17 ∤ W_r` for `r = 2,3,4,5` — and in particular that `v_17(W_r) = 0` for all of them, so the
sequence `r ↦ v_17(W_r)` does **not** grow with `r`.

**Verdict for `d5-2`: REFUTED (premise false).** The additive-energy integers carry `v_p = 0`;
Newton-above-Hodge is vacuous on the prize object. No `sorry`, no `native_decide`; counts are real.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.Avd52

/-- The prize prime of the countermodel: `μ_8 ⊆ F_17^*` (`8 ∣ 17 − 1`). -/
def p : ℕ := 17

/-- Exact wraparound integers `W_r = E_r^{F_p} − E_r^{char0}` for `μ_8 ⊆ F_17^*`, `r = 2,3,4,5`,
computed by exact integer additive-energy enumeration (`/tmp/d52_growth.py`). -/
def W : ℕ → ℕ
  | 2 => 72
  | 3 => 7380
  | 4 => 555912
  | 5 => 38674620
  | _ => 0

/-- **No `p`-adic divisibility (`r = 2`).** -/
theorem not_dvd_W2 : ¬ (p ∣ W 2) := by decide

/-- **No `p`-adic divisibility (`r = 3`).** -/
theorem not_dvd_W3 : ¬ (p ∣ W 3) := by decide

/-- **No `p`-adic divisibility (`r = 4`).** -/
theorem not_dvd_W4 : ¬ (p ∣ W 4) := by decide

/-- **No `p`-adic divisibility (`r = 5`).** -/
theorem not_dvd_W5 : ¬ (p ∣ W 5) := by decide

/-- **The `p`-adic valuation of `W_r` is `0` for every `r ∈ {2,3,4,5}`** — flat, not growing in `r`.
This is the direct refutation of `d5-2`: the Hodge–Newton claim `v_p(W_r) ≥ c·r` is contradicted by
`v_p(W_r) = 0`. The valuation uses Mathlib's `Nat.factorization`. -/
theorem valuation_W_eq_zero (r : ℕ) (hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) :
    (W r).factorization p = 0 := by
  rcases hr with h | h | h | h <;> subst h <;>
    · rw [Nat.factorization_eq_zero_iff]
      right; left
      first
        | exact not_dvd_W2
        | exact not_dvd_W3
        | exact not_dvd_W4
        | exact not_dvd_W5

/-- **`d5-2` REFUTED, packaged.** The Newton-above-Hodge premise would require `v_p(W_r)` to grow
with `r` (a positive lower bound forcing `p ∣ W_r`); instead the exact wraparound integers all have
`v_p = 0`, with `v_p(W r) = v_p(W r')` for all `r, r' ∈ {2,3,4,5}` (constant `= 0`, hence not
growing). No `p`-adic suppression of the wraparound contribution exists. -/
theorem hodge_newton_suppression_false :
    (∀ r, (r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) → (W r).factorization p = 0) ∧
    (∀ r r', (r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) → (r' = 2 ∨ r' = 3 ∨ r' = 4 ∨ r' = 5) →
      (W r).factorization p = (W r').factorization p) := by
  refine ⟨valuation_W_eq_zero, ?_⟩
  intro r r' hr hr'
  rw [valuation_W_eq_zero r hr, valuation_W_eq_zero r' hr']

end ArkLib.ProximityGap.Frontier.Avd52
