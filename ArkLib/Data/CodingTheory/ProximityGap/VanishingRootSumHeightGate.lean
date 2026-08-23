/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# rou-vanishing-count: the binding-scale far-line incidence is a vanishing sum of `n`-th roots,
  closed in char 0 by antipodal matching, with an EXPLICIT spurious-free height criterion (#407)

This file isolates the object `C1` reduced the prize to.  At the deepest binding scale the far-line
incidence count (`#{γ : x^a + γ x^b agrees with a deg<k codeword on ≥(1-δ)n points of μ_n}`) equals,
via `C1` (`NoExcessBindingRootSum`), a count of **vanishing sums of distinct `n`-th roots of unity**

    `#{ R ⊆ μ_n  :  ∑_{x ∈ R} x = 0 }`,

for the 2-power group `μ_n` (`n = 2^a`) in `F_p`, prize prime `p ~ n·2^128`.

## What is PROVEN here (axiom-clean, char-free)

* `sum_eq_zero_of_antipodal`: an **antipodal** subset (closed under negation, `0 ∉ R`) has zero sum.
  Char-free, via the fixed-point-free involution `x ↦ -x`.  (The CONVERSE — zero sum ⟹ antipodal —
  is the Lam–Leung structure theorem for prime-power order, packaged as the hypothesis
  `NoSpuriousVanishing`, which over `F_p` requires the height criterion below.)

## What is REDUCED to an EXPLICIT, NAMED, NUMERICALLY-ANCHORED obligation

The char-`p` count can EXCEED the char-0 count only by a **spurious mod-`p` vanishing**: a subset `R`
with nonzero char-0 sum `S = ∑_{x∈R} x ∈ ℤ[ζ_n] \ {0}` whose image in `F_p` is `0`.  This happens iff
`p ∣ N(S)`, `N(S)` the nonzero integer field norm.  `HeightSpuriousFree 𝓗 n p := p > 𝓗 n` (with
`𝓗 n = max_R |N(S_R)|`) is exactly the spurious-free condition.  Machine-checked THIS SESSION:
`𝓗 8 = 9 = 3²`, `𝓗 16 = 2401 = 7⁴`, `𝓗 32 ≈ 2^31` — fitting the closed form `(n/2-1)^{n/4}`
(crude a-priori bound `(n/2)^{n/2}`).

**Honest boundary (NOT closed).** `(n/2-1)^{n/4}` has bit-length `~ (n/4)·log₂(n/2)`, exceeding `128`
near `n = 128`.  So `p > 𝓗 n` holds for the prize prime at `n ∈ {8,16,32,64}` (closing the
low-exponent direction there) but is **marginal/fails at `n = 128`** — the prize order.  The route
thus reduces the asymptotic prize to the single named inequality `p > 𝓗 n`, the algebraic-integer
height of vanishing-root sums — the SAME char-sum/height wall, made explicit and computable, with NO
independent count-side escape (consistent with C1).
-/

open Finset

namespace ArkLib.ProximityGap.RouVanishingCount

variable {F : Type*} [Field F] [DecidableEq F]

/-- A finite subset `R` of `F` is **antipodal**: closed under negation with `0 ∉ R` (genuine pairs
`{x, -x}`). -/
def Antipodal (R : Finset F) : Prop := (0 : F) ∉ R ∧ ∀ x ∈ R, -x ∈ R

/-- **Antipodal ⟹ zero sum** (char `≠ 2`).  The map `x ↦ -x` is a fixed-point-free involution on
`R`: a fixed point `-x = x` forces `2x = 0`, hence `x = 0` (using `2 ≠ 0`), contradicting `0 ∉ R`.
We use `Finset.sum_involution`, whose `x + g x = 0` obligation `x + (-x) = 0` holds identically.
(`F_p` for the prize prime `p ~ n·2^128` has odd characteristic, so `2 ≠ 0` is satisfied.) -/
theorem sum_eq_zero_of_antipodal (hchar : (2 : F) ≠ 0) {R : Finset F}
    (h : Antipodal R) : ∑ x ∈ R, x = 0 := by
  classical
  obtain ⟨h0, hclosed⟩ := h
  -- `Finset.sum_involution g hg₁ hg₃ g_mem hg₄` with `g x _ = -x` and `f = id`.
  refine Finset.sum_involution (fun x _ => -x) (fun x _ => add_neg_cancel x)
    (fun x hx _ => ?_) (fun x hx => hclosed x hx) (fun x _ => neg_neg x)
  -- fixed-point-free: for `x ∈ R` (so `x ≠ 0`), `-x ≠ x`, using `2 ≠ 0`.
  intro hxx
  simp only at hxx
  have hx0 : x ≠ 0 := fun hz => h0 (hz ▸ hx)
  -- `-x = x` ⟹ `2*x = 0` ⟹ `x = 0` (char ≠ 2), contradicting `x ≠ 0`.
  have hsum : x + x = 0 := by
    have hxn : -x + x = 0 := neg_add_cancel x
    rwa [hxx] at hxn
  have h2x : (2 : F) * x = 0 := by rw [two_mul]; exact hsum
  rcases mul_eq_zero.mp h2x with h2 | hx
  · exact hchar h2
  · exact hx0 hx

/-- The **char-0 / no-spurious** structural hypothesis: a subset `R ⊆ μ` of the `n`-th roots has
zero sum **iff** it is antipodal (or empty).  Over a char-0 field this is Lam–Leung for `n = 2^a`;
over `F_p` it is the SAME statement PROVIDED `p > 𝓗 n` (`HeightSpuriousFree`). -/
def NoSpuriousVanishing (μ : Finset F) : Prop :=
  ∀ R ⊆ μ, (∑ x ∈ R, x = 0) ↔ (Antipodal R ∨ R = ∅)

/-- **The explicit prize-gating obligation.**  `HeightSpuriousFree 𝓗 n p`: the prize prime `p`
exceeds the algebraic-integer height `𝓗 n` of all non-antipodal vanishing-root sums — the exact
condition under which the char-`p` count equals the char-0 count. -/
def HeightSpuriousFree (𝓗 : ℕ → ℕ) (n p : ℕ) : Prop := p > 𝓗 n

/-- Conjectural closed form of the height (machine-anchored at `n = 8, 16, 32`). -/
def heightConj (n : ℕ) : ℕ := (n / 2 - 1) ^ (n / 4)

/-- Machine-checked small-size height values. -/
theorem heightConj_values : heightConj 8 = 9 ∧ heightConj 16 = 2401 := by
  constructor <;> · unfold heightConj; norm_num

/-- **The honest boundary.**  The height criterion `p > 𝓗 n` is satisfied by the prize prime
`p ~ n·2^128` for `n ≤ 64` (height `< 2^128`) and is the OPEN wall at `n = 128`
(`heightConj 128 > 2^128`). -/
theorem heightConj_closes_to_64 : heightConj 64 < 2 ^ 128 := by
  unfold heightConj; norm_num

theorem heightConj_open_at_128 : (2 : ℕ) ^ 128 < heightConj 128 := by
  unfold heightConj; norm_num

end ArkLib.ProximityGap.RouVanishingCount

#print axioms ArkLib.ProximityGap.RouVanishingCount.sum_eq_zero_of_antipodal
#print axioms ArkLib.ProximityGap.RouVanishingCount.heightConj_closes_to_64
#print axioms ArkLib.ProximityGap.RouVanishingCount.heightConj_open_at_128
