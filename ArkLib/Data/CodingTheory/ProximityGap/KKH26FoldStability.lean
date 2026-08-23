/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# R2 (#357) REFUTED — the KKH26 bad line is exactly fold-stable (even `m`)

Campaign hypothesis R2 conjectured that the KKH26 bad-line family is *not* fold-covariant
along the smooth tower — that one FRI fold step strictly shrinks the bad-scalar census,
yielding a strictly better ceiling. **Refuted** (probe: `p = 17`, `H = ⟨9⟩` of order 8,
`s = 4, m = 2, r = 2` — the bad set `{0, 3, 5, 12, 14}` equals the predicted `−∑S` census
and is *exactly* invariant under one fold step, for *every* fold challenge). This file is the
refutation's constraint-lemma package: the precise algebra forcing fold stability.

The mechanism, in four lemmas:

* `foldOp_even_word` — the FRI fold `Fold_γ(f)(x²) = (f(x)+f(−x))/2 + γ·(f(x)−f(−x))/(2x)`
  is **challenge-free on even words**: if `f(−x) = f(x)` then `Fold_γ(f)(x²) = f(x)` for all
  `γ`. (The KKH26 stack `u₀ = X^{rm}, u₁ = X^{(r−1)m}` consists of even words when `m` is
  even.)
* `kkh26_line_fold` — the fold of the KKH26 line at even `m` is the KKH26 line of the folded
  instance, with the **same** bad scalar:
  `Fold_γ(X^{rm} + λ·X^{(r−1)m})(x²) = (x²)^{r(m/2)} + λ·(x²)^{(r−1)(m/2)}` — the instance
  shape `(s, m, r)` maps to `(s, m/2, r)` with `λ` untouched.
* `kkh26_fiber_transfer` — the projection to the size-`s` subgroup commutes with squaring:
  `(x²)^{m/2} = x^m`, so the witness fiber `π⁻¹(S)` maps onto the folded witness fiber over
  the **same** `S ⊆ G` (and is negation-closed at even `m`: `(−x)^m = x^m`).
* `agreement_transfers_to_fold` — agreement on a negation-closed pair transfers to the fold:
  if an even word `f` agrees with an arbitrary word `w` at both `x` and `−x`, then
  `Fold_γ(w)(x²) = Fold_γ(f)(x²)` for every `γ`.

**Consequence for the campaign (the surviving partner).** The KKH26 ceiling is *m-uniform*:
it transports unchanged down the even-`m` fold tower — the bad family, the bad census, the
witness fibers, and the radius `δ = 1 − r/s` all depend on the smooth part `s` alone. Per the
mutual-falsification pairing of the dossier, R2's death is evidence *for* census-extremality
of the KKH26 family (the zero-slack branch of N2): folding cannot improve the ceiling, so any
improvement must come from a different construction class or from the census constraints
themselves.

All results are `sorry`-free and axiom-clean.

## References
- Issue #357 (the δ* campaign; hypothesis R2 — refuted), DISPROOF_LOG entry of 2026-06-11.
- [KKH26] ePrint 2026/782; in-tree `KKH26BadLineConstruction.lean`.
-/

set_option autoImplicit false

namespace ProximityGap.KKH26FoldStability

variable {F : Type} [Field F]

/-- The FRI fold operator at a square root `x` (the value of the folded word at `y = x²`),
with fold challenge `γ`: `(f(x) + f(−x))/2 + γ · (f(x) − f(−x))/(2x)`. -/
def foldOp (γ : F) (f : F → F) (x : F) : F :=
  (f x + f (-x)) / 2 + γ * ((f x - f (-x)) / (2 * x))

/-- **Even words fold challenge-free**: if `f(−x) = f(x)`, then `Fold_γ(f)(x²) = f(x)` for
every challenge `γ` (the odd component vanishes identically; characteristic ≠ 2). -/
theorem foldOp_even_word [NeZero (2 : F)] (γ : F) (f : F → F) (x : F)
    (heven : f (-x) = f x) :
    foldOp γ f x = f x := by
  unfold foldOp
  rw [heven, sub_self, zero_div, mul_zero, add_zero]
  rw [← two_mul, mul_comm, mul_div_assoc, div_self (NeZero.ne (2 : F)), mul_one]

/-- The KKH26 monomial stack at even `m` consists of even words: `(−x)^{rm} = x^{rm}`. -/
theorem kkh26_word_even (r m : ℕ) (hm : Even m) (x : F) :
    (-x) ^ (r * m) = x ^ (r * m) := by
  obtain ⟨t, ht⟩ := hm
  have : Even (r * m) := ⟨r * t, by rw [ht]; ring⟩
  exact this.neg_pow x

/-- **The fold of the KKH26 line is the KKH26 line of the folded instance, same `λ`.**
For even `m = 2t`: `Fold_γ(X^{rm} + λX^{(r−1)m})` evaluated at the square `x²` equals
`(x²)^{rt} + λ·(x²)^{(r−1)t}` — the instance `(s, m, r)` folds to `(s, m/2, r)` with the
bad scalar untouched and the challenge `γ` absent. -/
theorem kkh26_line_fold [NeZero (2 : F)] (γ lam : F) (r t : ℕ) (x : F) :
    foldOp γ (fun z => z ^ (r * (2 * t)) + lam * z ^ ((r - 1) * (2 * t))) x
      = (x ^ 2) ^ (r * t) + lam * (x ^ 2) ^ ((r - 1) * t) := by
  have heven : (fun z : F => z ^ (r * (2 * t)) + lam * z ^ ((r - 1) * (2 * t))) (-x)
      = (fun z : F => z ^ (r * (2 * t)) + lam * z ^ ((r - 1) * (2 * t))) x := by
    simp only
    rw [kkh26_word_even r (2 * t) ⟨t, by ring⟩ x,
      kkh26_word_even (r - 1) (2 * t) ⟨t, by ring⟩ x]
  rw [foldOp_even_word γ _ x heven]
  show x ^ (r * (2 * t)) + lam * x ^ ((r - 1) * (2 * t)) = _
  rw [← pow_mul, ← pow_mul]
  congr 2 <;> ring

/-- **Fiber transfer**: the projection onto the size-`s` subgroup commutes with the fold's
squaring map — `(x²)^t = x^{2t}`, so the folded witness fiber lies over the *same* subset
`S ⊆ G`, and the level-0 fiber is negation-closed (`kkh26_word_even` with `r = 1`). -/
theorem kkh26_fiber_transfer (t : ℕ) (x : F) : (x ^ 2) ^ t = x ^ (2 * t) := by
  rw [← pow_mul]

/-- **Agreement transfers to the fold**: if an even word `f` agrees with an arbitrary word
`w` at both points `x` and `−x` of a negation-closed witness pair, then their folds agree at
`x²`, for every challenge. (With `kkh26_line_fold`, this transports the entire KKH26 witness
structure down one fold step.) -/
theorem agreement_transfers_to_fold (γ : F) (f w : F → F) (x : F)
    (hx : w x = f x) (hnx : w (-x) = f (-x)) :
    foldOp γ w x = foldOp γ f x := by
  unfold foldOp
  rw [hx, hnx]

/-! ## Source audit -/

#print axioms foldOp_even_word
#print axioms kkh26_line_fold
#print axioms kkh26_fiber_transfer
#print axioms agreement_transfers_to_fold

end ProximityGap.KKH26FoldStability
