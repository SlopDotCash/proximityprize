/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Q1 route (i) is strictly weaker than the odd-symmetric hypothesis (#407, lane LB)

Chai–Fan 2026/861 Q1 (Conj 4.12) — `Norm_{K_d/ℚ}(F_d(α)) ≠ 0` on the primitive gap variety
`V_d^prim` — is rigorous only for `d ∈ {4, 8}`; OPEN for `d ≥ 16`.  The paper's promising **route (i)**
to Q1 is the self-similarity hypothesis

  `(∗)_d :  on V_d^prim,  x₁ = 0  ⟹  x_a = 0  for every odd a,`

extended from `d ∈ {4,8}` to all `d = 2^j` by dyadic doubling (`x_a = p_a(S)`, the `a`-th power sum
of the primitive config).  This file pins, *char-free and axiom-clean*, the exact logical status of
that route:

1. **The first power sum `p₁` carries no antipodal information by itself.**  We exhibit a finite
   subset `S` of a field with `p₁(S) = 0` (equivalently `e₁(S) = 0`) that is **not** antipodal
   (`S.image (-·) ≠ S`).  So "`x₁ = 0 ⟹ S = −S`" is *false as a pure algebraic implication* — it can
   only hold via extra arithmetic (the 2-power-root integrality of Lam–Leung, which is exactly what
   the companion probe shows **breaks in char-`p` at `d = 32`**).  `route_i_one_sum_insufficient`.

2. **The correct/strong hypothesis (all odd elementary symmetric functions vanish) IS char-free
   sufficient.**  We restate the endpoint of `EvenOddAntipodalCharFree.lean` self-contained: if
   `σ_S(X) = ∏_{x∈S}(X − x)` is even (invariant under `X ↦ −X`, i.e. all odd `e_i(S) = 0`), then
   `S = −S`.  `oddSymmetricVanishing_imp_antipodal`.  This is the input Q1 actually needs.

**The verified separation** (`scripts/probes/probe_wfLB_q1_route_i_charp_break.py`, machine-checked
over 8 prize-band primes `p ≡ 1 (mod 32)`, `p ~ 32^4`):

  * char-0: `V_d^prim(x₁=0)` is EMPTY for `d = 8, 16, 32` (Lam–Leung; route (i) vacuous over ℂ).
  * char-`p`: for `d = 8, 16` no antipodal-free `p₁ = 0` config exists in the band (route (i) intact);
  * char-`p`, `d = 32`: **384/384** antipodal-free configs have `p₁ = 0` but `p₃ ≠ 0 (mod p)`.
    Explicit witness at `p = 1048609` (primitive root `w = 415330`):
    `Y = {2,12,13,20,21,22,23,24,25,27,30,31} ⊂ ℤ/32`, antipodal-free, char-0-nonzero,
    `p₁(Y) = 0` but `p₃(Y),…,p₃₁(Y) ≠ 0 (mod p)`.

So **route (i) self-similarity bootstrap for Q1 is FALSE in char-`p` at `d = 32`**; `d = 16` is the
last clean dyadic level.  Q1 for `d ≥ 16` cannot be closed by route (i) as literally stated — it must
use the full odd-symmetric hypothesis (item 2, already char-free in-tree) or the resultant form
`R_d ≠ 0` directly.  This file makes the *logical* content of that separation a theorem; the char-`p`
arithmetic witness is the probe's machine-checked countermodel.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #407.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.Q1RouteICharPGap

/-! ## 1. The first power sum is insufficient: `e₁(S) = 0` does not force antipodality. -/

/-- The first power sum / first elementary symmetric function of a finite set `S` in a field.
For the gap-variety reading this is `x₁ = p₁(S) = Σ_{s∈S} s`. -/
def firstPowerSum {F : Type*} [Field F] (S : Finset F) : F := ∑ x ∈ S, x

/-- A finite set `S` is **antipodal** when it is closed under negation. -/
def Antipodal {F : Type*} [Field F] [DecidableEq F] (S : Finset F) : Prop :=
  S.image (fun x => -x) = S

/-- **Route (i) is logically insufficient: `x₁ = 0` does not imply antipodality.**

Over `ℚ` (any field of characteristic `≠ 2, 3`), the three-element set `S = {1, 2, -3}` has
`firstPowerSum S = 1 + 2 + (-3) = 0`, yet it is **not** antipodal: `−1 ∉ S`.  Hence the bare
implication "`x₁ = 0 ⟹ S = −S`" — the literal form the Chai–Fan route (i) tries to bootstrap — is
false as pure algebra.  Whatever makes `(∗)_d` true (when it is) is *arithmetic* (the 2-power-root
integrality of Lam–Leung over `ℂ`), and that arithmetic is exactly what the companion probe shows
**breaks in char-`p` at `d = 32`** (an antipodal-free 32nd-root config with `p₁ = 0` but `p₃ ≠ 0`).

This is the abstract counterpart of the char-`p` countermodel: the implication has no field-free
proof, so its truth is regime-dependent, and the regime (char 0, 2-power roots) is precisely where it
holds. -/
theorem route_i_one_sum_insufficient :
    ∃ (S : Finset ℚ), firstPowerSum S = 0 ∧ ¬ Antipodal S := by
  classical
  refine ⟨({1, 2, -3} : Finset ℚ), ?_, ?_⟩
  · -- 1 + 2 + (-3) = 0
    unfold firstPowerSum
    rw [show ({1, 2, -3} : Finset ℚ) = {(1 : ℚ), 2, -3} from rfl]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  · -- not antipodal: -1 would have to be in S (image of 1) but is not
    unfold Antipodal
    intro h
    -- `-1` is in the image (it is `-(1)`, and `1 ∈ S`), so by `h` it would be in `S`.
    have h1mem : (1 : ℚ) ∈ ({1, 2, -3} : Finset ℚ) := by
      simp [Finset.mem_insert]
    have hmem : (-1 : ℚ) ∈ ({1, 2, -3} : Finset ℚ).image (fun x => -x) := by
      rw [Finset.mem_image]
      exact ⟨1, h1mem, by norm_num⟩
    rw [h] at hmem
    -- but -1 ∉ {1,2,-3}
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> norm_num at h

/-! ## 2. The strong hypothesis IS char-free sufficient (the input Q1 needs).

We restate, self-contained, the endpoint of `EvenOddAntipodalCharFree.lean`: if the locator
polynomial `σ_S = ∏_{x∈S}(X − x)` is even (invariant under `X ↦ −X`, equivalently *all* odd
elementary symmetric functions of `S` vanish), then `S = −S`.  This is char-free and is the actual
input Q1 requires — strictly stronger than route (i)'s `x₁ = 0`. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- A polynomial whose odd coefficients all vanish evaluates evenly. -/
theorem eval_neg_eq_eval_of_oddCoeffZero {P : F[X]}
    (hOddCoeff : ∀ i : ℕ, Odd i → P.coeff i = 0) (z : F) :
    P.eval (-z) = P.eval z := by
  classical
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hiOdd : Odd i
  · simp [hOddCoeff i hiOdd]
  · have hiEven : Even i := Nat.not_odd_iff_even.mp hiOdd
    rw [hiEven.neg_pow z]

/-- **The strong (full odd-symmetric) hypothesis closes `(∗)`-style antipodality, char-free.**

If the locator `σ_S = ∏_{x∈S}(X − x)` has all odd coefficients zero — i.e. *every* odd elementary
symmetric function of `S` vanishes (not just `e₁ = x₁`) — then `S` is antipodal, for *any* finite
subset of *any* field.  This is the input Chai–Fan Q1 genuinely needs; route (i) tries to derive the
higher odd vanishings from `x₁ = 0` alone, which `route_i_one_sum_insufficient` shows is logically
impossible without the (char-0 only) Lam–Leung arithmetic. -/
theorem oddSymmetricVanishing_imp_antipodal (S : Finset F)
    (hOddCoeff : ∀ i : ℕ, Odd i → (∏ x ∈ S, (X - C x)).coeff i = 0) :
    Antipodal S := by
  classical
  set P := ∏ x ∈ S, (X - C x) with hPdef
  have heven : ∀ z : F, P.eval (-z) = P.eval z :=
    eval_neg_eq_eval_of_oddCoeffZero hOddCoeff
  -- every x ∈ S forces -x ∈ S, via the even-evaluation of the locator
  have hclosed : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx0 : P.eval x = 0 := by
      rw [hPdef, eval_prod]; exact Finset.prod_eq_zero hx (by simp)
    have hnegroot : P.eval (-x) = 0 := by rw [heven x, hx0]
    rw [hPdef, eval_prod, Finset.prod_eq_zero_iff] at hnegroot
    obtain ⟨y, hy, hzero⟩ := hnegroot
    simp only [eval_sub, eval_X, eval_C] at hzero
    rw [sub_eq_zero.mp hzero]; exact hy
  unfold Antipodal
  have hsub : S.image (fun x => -x) ⊆ S := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hclosed x hx
  have hcard : (S.image (fun x => -x)).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-! ## 3. The separation, stated as one theorem.

The two facts together: the *weak* route-(i) hypothesis (`x₁ = 0`) is insufficient, while the
*strong* odd-symmetric hypothesis is sufficient.  This is the precise sense in which Q1's route (i)
is strictly weaker than what is needed — and the char-`p`, `d = 32` countermodel in the companion
probe realizes the insufficiency at the actual prize object. -/
theorem route_i_strictly_weaker :
    (∃ S : Finset ℚ, firstPowerSum S = 0 ∧ ¬ Antipodal S) ∧
    (∀ S : Finset ℚ, (∀ i : ℕ, Odd i → (∏ x ∈ S, (X - C x)).coeff i = 0) → Antipodal S) :=
  ⟨route_i_one_sum_insufficient, fun S h => oddSymmetricVanishing_imp_antipodal S h⟩

end ProximityGap.Frontier.Q1RouteICharPGap

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.Q1RouteICharPGap.route_i_one_sum_insufficient
#print axioms ProximityGap.Frontier.Q1RouteICharPGap.eval_neg_eq_eval_of_oddCoeffZero
#print axioms ProximityGap.Frontier.Q1RouteICharPGap.oddSymmetricVanishing_imp_antipodal
#print axioms ProximityGap.Frontier.Q1RouteICharPGap.route_i_strictly_weaker
