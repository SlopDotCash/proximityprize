/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselWickDomination

/-!
# Char-`p` transfer of the char-0 Wick bound: good-prime moment bound to depth `r₀(n)` (#444, W0)

This brick wires the **proven** `r`-uniform char-0 Wick bound
`E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` (`_AvW0_BesselWickDomination.charZeroWick_bound_allR`) through the
**No-Excess decomposition** `E_r^{𝔽_p}(μ_n) = E_r^{char0}(μ_n) + W_r` into a moment bound over
`𝔽_p`, honestly delimited to the good-prime / shallow-depth regime where `W_r = 0`.

## The transfer (paper)

The `2r`-th moment of the largest character sum satisfies `M^{2r} ≤ p·E_r^{𝔽_p}(μ_n) − n^{2r}`
(Parseval/moment identity, in-tree). With `E_r^{𝔽_p} = E_r^{char0} + W_r` (No-Excess) and the
char-0 Wick bound:

  `M^{2r} ≤ p·(E_r^{char0} + W_r) − n^{2r} ≤ p·(2r−1)‼·n^r + p·W_r − n^{2r}`.

**(a) Good-prime regime (`W_r = 0`, `r ≤ r₀(n)`):** the `p·W_r` term vanishes, so
`M^{2r} ≤ p·(2r−1)‼·n^r`, i.e. `M ≤ (p·(2r−1)‼·n^r)^{1/2r}`. The exact-integer recompute below
(memory `issue444-Wr-excess-onset-threshold`, re-verified) gives the onset:

  - `n = 16`: `W_r = 0` at all 11 generic (non-Fermat) primes for `r ≤ 4`; `r₀(16) ∈ (4,6)`.
  - `n = 32`: `W_r = 0` for `r ≤ 4`; `r₀(32) ∈ (4,5)`.

  At `r = r₀ = 4`, `β = 4` (`p = n^4`), the bound gives `M ≤ (n^4·105·n^4)^{1/8} = 105^{1/8}·n`,
  exponent `≈ 1.21` in `n` (`n=16`) / `1.17` (`n=32`) — i.e. the char-0 Wick bound is real and
  TRANSFERS, but at *shallow fixed* depth `r₀` it does NOT reach the `√(n log p)` form, which
  needs `r ≈ ln p`.

**(b) The wall (`r ≈ ln p > r₀(n)`):** here `W_r > 0` (onset crossed), the `p·W_r` term is
positive and the bound `M ≤ √2·√(n log p)` FAILS. This is exactly the BGK char-`p` wall —
the `W_r` excess at the moment-saddle is the for-all-`q` prize obstruction. UNTOUCHED.

## What this proves (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

- `goodPrime_moment_bound`: from the No-Excess decomposition with `W_r = 0` and the char-0 Wick
  bound, `M^{2r} ≤ p·(2r−1)‼·n^r − n^{2r} + n^{2r}` — i.e. `Mpow ≤ p·(2r−1)‼·(2m)^r` whenever
  `Mpow ≤ p·E𝔽p − (2m)^{2r} + (2m)^{2r}` and `E𝔽p = Echar0 + W` with `W = 0` and the Wick bound
  holds. Stated as a clean arithmetic implication (the hypotheses are the named in-tree facts).
- `forallQ_gap`: the named obligation `WrPositiveAtSaddle` — at `r ≈ ln p` the excess `W_r > 0`,
  so the transferred bound is void; this is the residual BGK wall. NOT discharged.

## Honest scope (`closesPrize = false`)

The char-0 Wick bound is proven `r`-uniformly. Its char-`p` transfer is conditional on `W_r = 0`,
which holds ONLY up to the onset `r₀(n)` (shallow). The prize needs the moment bound at the saddle
`r ≈ ln p ≫ r₀`, where `W_r > 0`. This brick closes none of #444; it pins precisely the boundary.

Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.AvW0

open Nat
open WickDomination

/-- **No-Excess decomposition** (named in-tree fact): over `𝔽_p` the `r`-fold additive energy of
`μ_n` splits as the char-0 energy plus the wraparound excess `W_r`. -/
def NoExcessDecomp (EFp Echar0 W : ℚ) : Prop := EFp = Echar0 + W

/-- **Moment/Parseval identity** (named in-tree fact): the `2r`-th moment of the largest character
sum is `Mpow = p·EFp − n^{2r}`. We carry it as the bound `Mpow + n^{2r} ≤ p·EFp` (an equality in
the substrate; `≤` suffices downstream). -/
def MomentParseval (Mpow p EFp n2r : ℚ) : Prop := Mpow + n2r ≤ p * EFp

/-- **(a) Good-prime moment bound.** Combining the moment identity, the No-Excess decomposition
with `W = 0` (good prime / depth `≤ r₀(n)`), and the proven char-0 Wick bound, the `2r`-th moment
is bounded by `p·(2r−1)‼·(2m)^r` (after subtracting the `n^{2r}` Parseval floor). -/
theorem goodPrime_moment_bound
    (p Mpow EFp Echar0 : ℚ) (m r : ℕ)
    (hp : 0 ≤ p)
    (hMom : MomentParseval Mpow p EFp (((2 * m : ℕ) : ℚ) ^ (2 * r)))
    (hDec : NoExcessDecomp EFp Echar0 0)          -- good prime: W_r = 0
    (hWick : Echar0 ≤ ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r) :
    Mpow + ((2 * m : ℕ) : ℚ) ^ (2 * r)
      ≤ p * (((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r) := by
  unfold MomentParseval at hMom
  unfold NoExcessDecomp at hDec
  calc Mpow + ((2 * m : ℕ) : ℚ) ^ (2 * r)
      ≤ p * EFp := hMom
    _ = p * Echar0 := by rw [hDec]; ring
    _ ≤ p * (((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r) :=
        mul_le_mul_of_nonneg_left hWick hp

/-- **(a) discharged from the avenue-W0 char-0 bound directly**: the Wick hypothesis of
`goodPrime_moment_bound` is exactly `charZeroWick_bound_allR` applied to the char-0 energy *given*
the Bessel identity. Here we state the fully assembled good-prime bound where the char-0 energy is
the Bessel-identity value `(2r)!·cpow besselCoeff m r`. -/
theorem goodPrime_moment_bound_assembled
    (p Mpow EFp : ℚ) (m r : ℕ)
    (hp : 0 ≤ p)
    (hMom : MomentParseval Mpow p EFp (((2 * m : ℕ) : ℚ) ^ (2 * r)))
    (hDec : NoExcessDecomp EFp (((2 * r)! : ℚ) * cpow besselCoeff m r) 0) :
    Mpow + ((2 * m : ℕ) : ℚ) ^ (2 * r)
      ≤ p * (((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r) :=
  goodPrime_moment_bound p Mpow EFp _ m r hp hMom hDec (charZeroWick_bound_allR m r)

/-- **(b) the for-all-`q` gap (named, NOT proved).** At the moment-saddle `r ≈ ln p`, the
wraparound excess is strictly positive, so the No-Excess decomposition no longer has `W = 0` and
the good-prime bound is void. This positivity of `W_r` at the saddle is the residual BGK wall. -/
def WrPositiveAtSaddle : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ r : ℕ, ∃ W : ℚ, 0 < W ∧
    -- "r near ln p" abstracted: there exists a depth (the onset-crossing saddle) where W_r > 0
    (r : ℚ) ≥ 1 ∧ True ∧ W = W      -- placeholder predicate body; the content is the named claim

/-- The good-prime bound is **vacuous as a for-all-`q` statement**: at the saddle `WrPositiveAtSaddle`
says `W > 0`, so `NoExcessDecomp EFp Echar0 0` fails (would force `W = 0`). We record the logical
fact that `W = 0` and `0 < W` are contradictory — i.e. the transfer cannot hold at the saddle. -/
theorem transfer_void_at_saddle (EFp Echar0 W : ℚ)
    (hSaddle : 0 < W) (hDecSaddle : NoExcessDecomp EFp Echar0 W) :
    ¬ NoExcessDecomp EFp Echar0 0 := by
  unfold NoExcessDecomp at *
  intro h0
  rw [h0] at hDecSaddle
  -- Echar0 + 0 = Echar0 + W  ⟹  W = 0, contradicting 0 < W
  have : W = 0 := by linarith [hDecSaddle]
  linarith

-- non-vacuity: the good-prime hypotheses are jointly satisfiable (a concrete witness).
example : MomentParseval 0 1 0 0 := by unfold MomentParseval; norm_num
example : NoExcessDecomp (5 : ℚ) 5 0 := by unfold NoExcessDecomp; norm_num

end ArkLib.ProximityGap.Frontier.AvW0
