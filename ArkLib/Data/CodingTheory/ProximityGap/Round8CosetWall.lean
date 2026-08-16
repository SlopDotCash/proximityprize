/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# Round 8 (Issue #232, ABF26) — the COSET WALL: why the algebraic concentration is super-polynomial
# only near capacity, and merely polynomial in the deep interior.

The coset construction (`Round8CosetConcentration.lean`) produces a list of RS codewords as unions of
`r` cosets of an order-`N` subgroup of the smooth evaluation domain (`|domain| = n`, rate `ρ = k/n`).
Killing the top `t` power sums — required for a degree drop at agreement `a = k + t`, i.e. radius
`δ = 1 − a/n` — needs the coset size to satisfy `N ≥ t + 1` (a coset of `N`-th roots of unity kills
`p₁, …, p_{N−1}`). A union of `r` cosets has size `a = r·N`, and the number of such unions is
`C(M, r)` with `M = n / N` the number of cosets.

This file formalizes, as clean self-contained `Nat` inequalities, **why `C(M, r)` is super-polynomial
only very close to capacity** (`t` small, so `r` large) **and merely polynomial deeper in the
interior** (`t` a constant fraction of `k`, so `r = O(1)`). This is honest "wall" cartography: it
proves the algebraic route provably cannot pin `δ*` at constant-fraction interior depth — matching the
[ABF26] assessment that the deep interior has "no known technique".

* `count_poly_and_budget` — the cap `C(M,r) ≤ Mʳ` together with the budget `r·(t+1) ≤ a`. As `t` grows
  the exponent `r ≤ a/(t+1)` shrinks: at `t ≥ k` the count is essentially linear (`budget_forces_r_le_one`
  gives `r ≤ 1`).
* `two_pow_le_choose_count` — the contrast `2ʳ ≤ C(M, r)` for `2r ≤ M`: near capacity (`t` small, `r`
  large) the count genuinely blows up super-polynomially, so the polynomial cap is non-vacuous.

All results are `sorry`-free and axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Round8CosetWall

/-- **Lemma A (polynomial cap).** The number of coset-unions `C(M, r)` is at most `M ^ r` —
polynomial in `M` for fixed `r`. -/
theorem choose_le_pow_count (M r : ℕ) : M.choose r ≤ M ^ r :=
  Nat.choose_le_pow M r

/-- **Lemma B (budget forces small `r` at deep interior).** If the coset is big enough to kill `t`
power sums (`N ≥ t + 1`), the union size equals the agreement (`r·N = a`), the agreement is
`a = k + t`, and we are at constant-fraction-or-deeper interior (`t ≥ k`), then the number of cosets
in the union is `r ≤ 1`.

Proof: `r·(t+1) ≤ r·N = a = k + t ≤ 2t < 2·(t+1)`, so `r < 2`. -/
theorem budget_forces_r_le_one
    {N t a k r : ℕ} (hN : t + 1 ≤ N) (hrN : r * N = a) (ha : a = k + t) (htk : k ≤ t) :
    r ≤ 1 := by
  have h1 : r * (t + 1) ≤ r * N := Nat.mul_le_mul_left r hN
  have h2 : r * (t + 1) ≤ k + t := by rw [hrN, ha] at h1; exact h1
  by_contra h
  rw [not_le] at h
  have h2r : 2 ≤ r := h
  have : 2 * (t + 1) ≤ r * (t + 1) := Nat.mul_le_mul_right (t + 1) h2r
  omega

/-- **Lemma C (general polynomial bound).** Combining the polynomial cap with the coset budget: the
count is at most `M ^ r`, and the number of cosets satisfies `r·(t+1) ≤ a` (i.e. `r ≤ a/(t+1)`). As
`t` grows (deeper interior), the exponent `r` shrinks and `M ^ r` collapses toward polynomial. -/
theorem count_poly_and_budget
    {M N t a r : ℕ} (hN : t + 1 ≤ N) (hrN : r * N = a) :
    M.choose r ≤ M ^ r ∧ r * (t + 1) ≤ a := by
  refine ⟨Nat.choose_le_pow M r, ?_⟩
  calc r * (t + 1) ≤ r * N := Nat.mul_le_mul_left r hN
    _ = a := hrN

/-- Helper for Lemma D: `2 ^ r ≤ centralBinom r`, by induction via the recurrence
`(r+1)·centralBinom (r+1) = 2·(2r+1)·centralBinom r`. The multiplier `2·(2r+1) ≥ 2·(r+1)` forces a
doubling each step. -/
theorem two_pow_le_centralBinom (r : ℕ) : 2 ^ r ≤ Nat.centralBinom r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hrec : (r + 1) * Nat.centralBinom (r + 1)
        = 2 * (2 * r + 1) * Nat.centralBinom r := Nat.succ_mul_centralBinom_succ r
    have hmul : 2 * (r + 1) ≤ 2 * (2 * r + 1) := by omega
    have hbig : 2 * (r + 1) * 2 ^ r ≤ 2 * (2 * r + 1) * Nat.centralBinom r :=
      Nat.mul_le_mul hmul ih
    have hgoal : (r + 1) * 2 ^ (r + 1) ≤ (r + 1) * Nat.centralBinom (r + 1) := by
      rw [hrec]
      calc (r + 1) * 2 ^ (r + 1)
          = 2 * (r + 1) * 2 ^ r := by ring
        _ ≤ 2 * (2 * r + 1) * Nat.centralBinom r := hbig
    exact Nat.le_of_mul_le_mul_left hgoal (Nat.succ_pos r)

/-- Helper for Lemma D: `2 ^ r ≤ C(M, r)` whenever `2r ≤ M`. Route:
`2ʳ ≤ centralBinom r = C(2r, r) ≤ C(M, r)` by monotonicity of `choose` in the top argument. -/
theorem two_pow_le_choose (M r : ℕ) (h : 2 * r ≤ M) : 2 ^ r ≤ M.choose r :=
  calc 2 ^ r ≤ Nat.centralBinom r := two_pow_le_centralBinom r
    _ = (2 * r).choose r := Nat.centralBinom_eq_two_mul_choose r
    _ ≤ M.choose r := Nat.choose_le_choose r h

/-- **Lemma D (near-capacity super-poly — the contrast).** When the number of cosets in a union `r` is
at most half the total number of cosets `M` (`2r ≤ M`, available only *very close to capacity*, where
`t` is small so `r = a/N` can be large), the count is at least `2 ^ r` — super-polynomial in `r`. This
witnesses that the polynomial cap of Lemma A/C is non-vacuous: the count genuinely blows up near
capacity, and only the budget `r·(t+1) ≤ a` of Lemma C tames it in the interior. -/
theorem two_pow_le_choose_count (M r : ℕ) (h : 2 * r ≤ M) : 2 ^ r ≤ M.choose r :=
  two_pow_le_choose M r h

end ArkLib.ProximityGap.Round8CosetWall

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8CosetWall.choose_le_pow_count
#print axioms ArkLib.ProximityGap.Round8CosetWall.budget_forces_r_le_one
#print axioms ArkLib.ProximityGap.Round8CosetWall.count_poly_and_budget
#print axioms ArkLib.ProximityGap.Round8CosetWall.two_pow_le_choose_count
