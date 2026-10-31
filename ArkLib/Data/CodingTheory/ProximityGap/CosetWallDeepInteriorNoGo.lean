/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Round8CosetWall
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Round 9 (Issue #232, ABF26) — the coset route's deep-interior NO-GO, as one explicit theorem.

Rounds 5–8 produced the *unconditional* and the *q-independent* interior list lower bounds via the
coset / vanishing-power-sum construction: a union of `r` cosets of an order-`N` subgroup of the smooth
`2^k`-evaluation domain (`|domain| = n`, rate `ρ = k/n`) kills the top `N − 1` power sums, hence gives
a degree-drop family at agreement `a = r·N`, with count `C(M, r)` (`M = n/N` cosets). Round 8's
`Round8CosetWall.budget_forces_r_le_one` showed that *deep* in the interior (`t ≥ k`, where the
agreement `a = k + t ≥ 2k`, i.e. the radius `δ = 1 − a/n ≤ 1 − 2ρ` is a constant fraction below
capacity) the budget forces `r ≤ 1`.

This file welds that into **one explicit count inequality**: when `t ≥ k` (agreement `a ≥ 2k`,
i.e. radius `δ ≤ 1 − 2ρ`), the coset construction's list count is at most `M ≤ n` — *linear* in
`n`, not super-polynomial. Given the additional hypothesis that this linear count is at most the
prize budget `ε*·q` (`hThresh` below), the coset / vanishing-power-sum construction stays within
the prize budget in that radius range.

**Scope: which part of the beyond-Johnson window this covers.** The radius range reached here is
`δ ≤ 1 − 2ρ`, while the open beyond-Johnson window is `1 − √ρ < δ < 1 − ρ`. These intersect in
`1 − √ρ < δ ≤ 1 − 2ρ`, which is nonempty only when `2ρ < √ρ`, i.e. `ρ < 1/4`. For rates
`ρ ≥ 1/4` one has `1 − 2ρ ≤ 1 − √ρ`, so the "deep interior" of this file lies at or below the
Johnson radius (at `ρ = 1/2` it is `δ ≤ 0`) and says **nothing** about the beyond-Johnson window.
So this does not close the coset attack family uniformly across the prize rates: for `ρ < 1/4` it
constrains the sub-window `(1 − √ρ, 1 − 2ρ]`, and for `ρ ≥ 1/4` it constrains no beyond-Johnson
radius. The construction's super-polynomial count `C(M,r)` near capacity (`2^r ≤ C(M,r)`) is
contrasted below with the linear bound at `δ ≤ 1 − 2ρ`; the window `(max(1 − √ρ, 1 − 2ρ), 1 − ρ)`
is not addressed by this file.

All results are `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.CosetWallDeepInteriorNoGo

open ArkLib.ProximityGap.Round8CosetWall

/-- **The coset count collapses to linear at deep interior.** If the coset size kills the required `t`
power sums (`N ≥ t + 1`), the union size equals the agreement (`r·N = a = k + t`), and we are at
constant-fraction-or-deeper interior (`t ≥ k`), then the number of coset-unions `C(M, r)` is at most
`M` — linear in the number of cosets. (Proof: `budget_forces_r_le_one` gives `r ≤ 1`, and
`C(M, r) ≤ C(M, 1) = M` for `r ≤ 1`.) -/
theorem coset_count_le_card_of_deep_interior
    {M N t a k r : ℕ} (hM : 1 ≤ M) (hN : t + 1 ≤ N) (hrN : r * N = a) (ha : a = k + t)
    (htk : k ≤ t) :
    M.choose r ≤ M := by
  have hr1 : r ≤ 1 := budget_forces_r_le_one hN hrN ha htk
  interval_cases r
  · rw [Nat.choose_zero_right]; exact hM
  · rw [Nat.choose_one_right]

/-- **The coset count is at most `n` at deep interior.** With `M = n / N ≤ n` cosets, the deep-interior
coset count is `≤ n`. -/
theorem coset_count_le_n_of_deep_interior
    {n N t a k r : ℕ} (hM : 1 ≤ n / N) (hMle : n / N ≤ n) (hN : t + 1 ≤ N) (hrN : r * N = a)
    (ha : a = k + t) (htk : k ≤ t) :
    (n / N).choose r ≤ n :=
  le_trans (coset_count_le_card_of_deep_interior hM hN hrN ha htk) hMle

/-- **The deep-interior coset no-go, in prize coordinates.** The prize tolerates a list bound
`|Λ| ≤ ε*·q`. If at constant-fraction-or-deeper interior the coset construction's list count `L` is
`≤ M` (linear; `coset_count_le_card_of_deep_interior`), and the field is large enough that the prize
threshold dominates the linear count (`M ≤ thresh`, the prize's `ε*·q` budget), then the coset
construction stays **within** the prize: `L ≤ thresh`. So, under `hThresh`, no coset /
vanishing-power-sum construction exceeds the budget at radii `δ ≤ 1 − 2ρ`. This range meets the
beyond-Johnson window only when `ρ < 1/4` (see the module docstring). -/
theorem coset_within_prize_of_deep_interior
    {M N t a k r L thresh : ℕ} (hM : 1 ≤ M) (hN : t + 1 ≤ N) (hrN : r * N = a) (ha : a = k + t)
    (htk : k ≤ t) (hL : L ≤ M.choose r) (hThresh : M ≤ thresh) :
    L ≤ thresh :=
  le_trans hL (le_trans (coset_count_le_card_of_deep_interior hM hN hrN ha htk) hThresh)

/-- **Non-vacuity / the contrast is real.** The hypotheses are satisfiable by genuine deep-interior
parameters: `k = 50`, `t = 60` (so `t ≥ k`, deep), `N = 61 ≥ t + 1`, `r = 1`, `a = r·N = 61 = ?`.
We instead exhibit the cleanest witness `k = 1, t = 1, N = 2, r = 1, a = 2`: `r·N = 2 = k + t`,
`N = 2 ≥ t + 1 = 2`, `t = 1 ≥ k = 1`, and the conclusion `C(M, 1) = M ≤ M` holds. The point is the
*budget* `r ≤ 1`: deep interior genuinely forbids `r ≥ 2`, which is where super-polynomiality lived. -/
theorem deep_interior_witness :
    (1 : ℕ) * 2 = 1 + 1 ∧ (1 : ℕ) + 1 ≤ 2 ∧ (1 : ℕ) ≤ 1 := by
  refine ⟨by norm_num, by norm_num, le_refl 1⟩

/-- **The near-capacity contrast (why the no-go is non-trivial).** Near capacity (`t` small, so `r` can
be large with `2r ≤ M`), the same coset count is `≥ 2^r` — super-polynomial. So the deep-interior
collapse to `≤ M` is a genuine phase transition in the construction's power, not a vacuous bound.
(Re-exported from `Round8CosetWall.two_pow_le_choose_count`.) -/
theorem near_capacity_superpoly (M r : ℕ) (h : 2 * r ≤ M) : 2 ^ r ≤ M.choose r :=
  two_pow_le_choose_count M r h

end ArkLib.ProximityGap.CosetWallDeepInteriorNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_count_le_card_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_count_le_n_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.coset_within_prize_of_deep_interior
#print axioms ArkLib.ProximityGap.CosetWallDeepInteriorNoGo.near_capacity_superpoly
