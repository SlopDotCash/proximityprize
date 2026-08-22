/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BGKMultiplicativeInput

/-!
# All-orders multiplicative doubling of `μ_n`: `(μ_n)^k = μ_n` and `σₘ^{(k)} = 1` (#444)

`BGKMultiplicativeInput.lean` proves the **second-order** multiplicative doubling for the in-tree
carrier `μ_n = RepCountCurve.muN F n`: `μ_n · μ_n = μ_n` (`muN_mul_self_eq`),
`#(μ_n · μ_n) = #μ_n` (`card_muN_mul_self_eq`), and the doubling constant `σₘ[μ_n] = 1`
(`muN_doubling_eq_one`). The BGK sum–product route, however, consumes the doubling at **all** orders
(Plünnecke–Ruzsa-style `#(A^k) ≤ K^{k-1}·#A`): one needs every iterated product set `(μ_n)^k` to stay
the size of `μ_n`, not just the square.

This file lands the all-orders version directly at the field level (where `(μ_n)^k` is the pointwise
`Finset` power in the monoid `(F, ·)` — `F` is not a group under `·`, but it is a monoid, so the
pointwise power is well-defined). The proof is a one-line induction off `muN_mul_self_eq` plus the
identity `1 ∈ μ_n`, so it EXTENDS the proven second-order brick rather than restating it.

## What is proven (NON-MOMENT, sign-free, EXTEND-proven on `muN_mul_self_eq`)

* `muN_pow_eq` — `(μ_n)^k = μ_n` for every `k ≥ 1`: the iterated pointwise product set is `μ_n`
  itself (multiplicative closure + identity, by induction on `k`).
* `card_muN_pow_eq` — `#((μ_n)^k) = #μ_n` for `k ≥ 1`: the all-orders cardinality doubling.
* `muN_doubling_pow_eq_one` — `(#((μ_n)^k) : ℚ) / #μ_n = 1` for `k ≥ 1` (with `μ_n` nonempty): the
  all-orders doubling constant `σₘ^{(k)}[μ_n] = 1` written explicitly, the higher-order analogue of
  `muN_doubling_eq_one`.

## Why this matters (honest scope)

This is still the **easy** (multiplicative) half of the BGK dichotomy — `μ_n` is literally a
subgroup, so every order is rigid. It supplies the all-orders input the Plünnecke–Ruzsa / sum–product
machine consumes, complementing the additive half already in-tree (`SumsetLowerBoundMuN`:
`#(μ_n + μ_n) > n²/3`). The genuinely hard, multi-month half — a sum–product contradiction from
`σₘ = 1` against the additive spread — is **untouched** (no formalised `𝔽_p` sum–product estimate
exists in Mathlib). The multiplicative doubling is field- and thickness-BLIND (a subgroup is a
subgroup in any field, thin or thick) ⟹ by the §3 meta-thm and rule 3 it is **not** thinness-
essential and CANNOT prove CORE; it is the sign-free shadow whose contrast with additive Sidon-ness
is the *configuration* of the wall, not a route around it.

`CORE M(μ_n) ≤ C·√(n·log(q/n))` with absolute `C` remains **OPEN**. No char-`p` transfer, no
capacity, no beyond-Johnson `√(log)` saving, no growth-law, nothing about the cliff-at-`n/2`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`/`axiom`/`native_decide`. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open scoped Pointwise

namespace ArkLib.ProximityGap.MuNIteratedDoubling

open ArkLib.ProximityGap (muN)
open ArkLib.ProximityGap.BGKMultiplicativeInput (muN_mul_self_eq)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **All-orders multiplicative closure: `(μ_n)^k = μ_n` for `k ≥ 1`.** The iterated pointwise
product of the `n`-th roots of unity is `μ_n` itself. Induction on `k`: the base `k = 1` is
`pow_one`; the step uses `μ_n · μ_n = μ_n` (`muN_mul_self_eq`). -/
theorem muN_pow_eq {n : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    (muN F n) ^ k = muN F n := by
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp
    · rw [pow_succ, ih hj, muN_mul_self_eq]

/-- **All-orders cardinality doubling: `#((μ_n)^k) = #μ_n` for `k ≥ 1`.** Immediate from
`muN_pow_eq`. This is the `σₘ^{(k)} = 1` input the Plünnecke–Ruzsa / sum–product machine consumes. -/
theorem card_muN_pow_eq {n : ℕ} {k : ℕ} (hk : 1 ≤ k) :
    ((muN F n) ^ k).card = (muN F n).card := by
  rw [muN_pow_eq hk]

/-- **The all-orders doubling constant `σₘ^{(k)}[μ_n] = 1`, written explicitly** (for `k ≥ 1` and
`μ_n` nonempty). The higher-order analogue of `BGKMultiplicativeInput.muN_doubling_eq_one`. -/
theorem muN_doubling_pow_eq_one {n : ℕ} {k : ℕ} (hk : 1 ≤ k)
    (hne : (muN F n).Nonempty) :
    (((muN F n) ^ k).card : ℚ) / (muN F n).card = 1 := by
  rw [card_muN_pow_eq hk, div_self]
  exact_mod_cast (Finset.card_pos.mpr hne).ne'

end ArkLib.ProximityGap.MuNIteratedDoubling

/-! ## Axiom audit — expected `propext`, `Classical.choice`, `Quot.sound` only. -/
open ArkLib.ProximityGap.MuNIteratedDoubling in
#print axioms muN_pow_eq
open ArkLib.ProximityGap.MuNIteratedDoubling in
#print axioms card_muN_pow_eq
open ArkLib.ProximityGap.MuNIteratedDoubling in
#print axioms muN_doubling_pow_eq_one
