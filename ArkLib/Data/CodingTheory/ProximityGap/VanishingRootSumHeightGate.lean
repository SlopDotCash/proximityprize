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
  closed in char 0 by antipodal matching, with a CONJECTURAL sufficient height heuristic (#407)

This file isolates the object `C1` reduced the prize to.  At the deepest binding scale the far-line
incidence count (`#{γ : x^a + γ x^b agrees with a deg<k codeword on ≥(1-δ)n points of μ_n}`) equals,
via `C1` (`NoExcessBindingRootSum`), a count of **vanishing sums of distinct `n`-th roots of unity**

    `#{ R ⊆ μ_n  :  ∑_{x ∈ R} x = 0 }`,

for the 2-power group `μ_n` (`n = 2^a`) in `F_p`, prize prime `p ~ n·2^128`.

## What is PROVEN here (axiom-clean, char-free)

* `sum_eq_zero_of_antipodal`: an **antipodal** subset (closed under negation, `0 ∉ R`) has zero sum.
  Char-free, via the fixed-point-free involution `x ↦ -x`.  (The CONVERSE — zero sum ⟹ antipodal —
  is the Lam–Leung structure theorem for prime-power order, packaged as the hypothesis
  `NoSpuriousVanishing`; its char-0, `n = 2^a` case is proved in `ConverseLamLeung2Power.lean`.
  Over `F_p` it needs an additional arithmetic input — see the heuristic and the guarded route
  below; nothing here proves it over `F_p`.)

## A CONJECTURAL height heuristic (NOT a certified criterion)

**Correction (audit 2026-10-28, PG-111).** An earlier version of this section said spurious
reduction happens *iff* `p ∣ N(S)`, called `p > 𝓗 n` *exactly* the spurious-free condition, and
claimed small-`n` closures from computed heights. Those statements overclaim; the accurate picture:

* The char-`p` count can exceed the char-0 count only by a **spurious mod-`p` vanishing**: a subset
  `R` with nonzero char-0 sum `S = ∑_{x∈R} x ∈ ℤ[ζ_n] \ {0}` whose image under the *fixed* reduction
  `ℤ[ζ_n] → F_p` used by the evaluation (the one sending `ζ_n` to the chosen root) is `0`.
* Such a vanishing implies `p ∣ N(S)` (one direction only). The converse fails in general:
  `p ∣ N(S)` says `S` vanishes at **some** prime above `p`, not necessarily the fixed one.
* Consequently `p > max_R |N(S_R)|` is a **sufficient** condition for spurious-freeness, not a
  necessary one: many smaller primes avoid every relevant norm.

**What is (and is not) formalized here.** In this file `HeightSpuriousFree 𝓗 n p := p > 𝓗 n` is
plain arithmetic for an *arbitrary* function `𝓗 : ℕ → ℕ`, and `heightConj n := (n/2-1)^{n/4}` is a
conjectural closed form fitted to off-tree computations (reported values `𝓗 8 = 9`, `𝓗 16 = 2401`,
`𝓗 32 ≈ 2^31`). There is **no** algebraic integer, norm census, proof that `𝓗 = heightConj`, or
proof that `HeightSpuriousFree → NoSpuriousVanishing` in this file. The numeric theorems
`heightConj_values`, `heightConj_closes_to_64`, `heightConj_open_at_128` only evaluate that formula.
So any height-to-transfer or small-`n` "closure" read off from them is **conditional** on those
missing bridges.

**The guarded in-tree route.** The actual proved `F_p`-to-norm direction and height gate are
`FpVanishingBridge.spurious_Fp_vanish_imp_antipodal` (and its `_prize` form, `p > n^{n/2}`), via
`HeightGateNormBound.gate_2power_antipodal`. They keep the reduction hom `r : 𝓞_K →+* ZMod p`
(`r ζ = ω`) as an explicit hypothesis and use the crude proved bound `(S.card)^{[K:ℚ]} < p`, not
`heightConj`.

**Boundary of the heuristic.** `(n/2-1)^{n/4}` has bit-length `~ (n/4)·log₂(n/2)`, exceeding `128`
near `n = 128`. If the conjectural height were established, the sufficient condition `p > 𝓗 n`
would hold for the prize prime at `n ∈ {8,16,32,64}` and would fail at `n = 128`; failure of this
sufficient condition does not by itself produce a spurious vanishing.
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
zero sum **iff** it is antipodal (or empty).  Over a char-0 field this is Lam–Leung for `n = 2^a`.
Over `F_p` it is expected to hold when `p` exceeds the norms of all relevant non-antipodal sums (a
sufficient, not necessary, condition), but no implication from `HeightSpuriousFree` to this `Prop`
is proved here; see `FpVanishingBridge.spurious_Fp_vanish_imp_antipodal` for the guarded route. -/
def NoSpuriousVanishing (μ : Finset F) : Prop :=
  ∀ R ⊆ μ, (∑ x ∈ R, x = 0) ↔ (Antipodal R ∨ R = ∅)

/-- **A height comparison (arithmetic only).**  `HeightSpuriousFree 𝓗 n p` is `p > 𝓗 n` for an
arbitrary function `𝓗`.  When `𝓗 n` is the maximum absolute norm of all non-antipodal root sums,
this is a **sufficient** (not necessary) condition for the char-`p` count to equal the char-0 count;
neither that interpretation of `𝓗` nor the implication to `NoSpuriousVanishing` is proved here
(PG-111). -/
def HeightSpuriousFree (𝓗 : ℕ → ℕ) (n p : ℕ) : Prop := p > 𝓗 n

/-- Conjectural closed form of the height, fitted to off-tree computations at `n = 8, 16, 32`.
No proof that it equals the maximum norm is given. -/
def heightConj (n : ℕ) : ℕ := (n / 2 - 1) ^ (n / 4)

/-- Evaluation of the conjectural formula at `n = 8, 16` (this checks the formula, not the
underlying norm census). -/
theorem heightConj_values : heightConj 8 = 9 ∧ heightConj 16 = 2401 := by
  constructor <;> · unfold heightConj; norm_num

/-- **Arithmetic boundary of the heuristic.**  The conjectural formula satisfies
`heightConj 64 < 2^128` and `heightConj 128 > 2^128`.  Only if `heightConj` were proved to bound
the relevant norms would this give the sufficient condition `p > 𝓗 n` for the prize prime
`p ~ n·2^128` at `n ≤ 64`; at `n = 128` the sufficient condition fails, which is not a proof that
spurious vanishing occurs. -/
theorem heightConj_closes_to_64 : heightConj 64 < 2 ^ 128 := by
  unfold heightConj; norm_num

theorem heightConj_open_at_128 : (2 : ℕ) ^ 128 < heightConj 128 := by
  unfold heightConj; norm_num

end ArkLib.ProximityGap.RouVanishingCount

#print axioms ArkLib.ProximityGap.RouVanishingCount.sum_eq_zero_of_antipodal
#print axioms ArkLib.ProximityGap.RouVanishingCount.heightConj_closes_to_64
#print axioms ArkLib.ProximityGap.RouVanishingCount.heightConj_open_at_128
