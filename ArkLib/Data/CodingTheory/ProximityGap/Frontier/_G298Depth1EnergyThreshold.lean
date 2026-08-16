/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# G298: the depth-1 CORE covariance is a subgroup additive-energy threshold, and its sign is
NOT fixed by thinness

## Statement of record

Continue the CORE covariance framing of G295/G296. With the sponsor gate
`W_G(x) = #{(y,z) ∈ G² : 2y - z = x}` and the adjacent-rank row
`R_r = dp_r ⋆ dp_{r-1}`, the centered covariance is
`A_r = p · ∑_x W_G(x) R_r(x) - (∑ W_G)(∑ R_r)`.

At depth `r = 1` the row degenerates: `dp_1 = 1_G` and `dp_0 = 1_{0}`, so `R_1 = dp_1 ⋆ dp_0 = 1_G`.
Hence the **boundary covariance has an exact closed form as a subgroup additive count**:

```text
A_1 = p · ∑_{x ∈ G} W_G(x) - (∑ W_G)(∑ 1_G) = p · T₃(G) - n³,
```

where `T₃(G) = #{(y,z) ∈ G² : 2y - z ∈ G} = #{(y,z,w) ∈ G³ : 2y = z + w}` is the number of
3-term arithmetic progressions with midpoint in `G` (the additive-energy-adjacent structural count
of the multiplicative subgroup), and `∑ W_G = n²`, `∑ 1_G = n`.

So `A_1 = p · T₃(G) - n³ = n² · (p · T₃/n² - n)`, i.e. `sign A_1 = sign(T₃/n² - n/p)`: the depth-1
CORE covariance is exactly the **additive-3AP density of the thin subgroup measured against the
random density `n/p`**. This is the BGK/Paley object at depth one, not a rank-blind feature.

## The no-go: the sign is not a function of thinness

`sign A_1` is NOT determined by `n` (thinness) alone. For the SAME subgroup order `n = 8` and even
the SAME additive count `T₃ = 24`, the sign flips as the prime crosses the threshold
`n³ / T₃ = 512 / 24 ≈ 21.3`:

* `p = 17`, `G = ⟨9⟩ ≤ F₁₇^*`: `T₃ = 24`, `A_1 = 17·24 - 8³ = 408 - 512 = -104 < 0`.
* `p = 41`, `G = ⟨3⟩ ≤ F₄₁^*`: `T₃ = 24`, `A_1 = 41·24 - 8³ = 984 - 512 = +472 > 0`.

Both cells are `n = 8` sponsor cells with identical `T₃`; only the scale `p` differs. Therefore no
depth-1 (rank-1) energy functional of the fixed shape `p·T₃ - n³` can certify a fixed sign of the
CORE covariance across sponsor primes: the simplest possible certificate — the boundary covariance
itself — is sign-indeterminate. A surviving certificate must use the rank-labelled row at genuine
depth, not the depth-1 boundary energy.

This is orthogonal to G289/G291 (dimension-forced canonical-feature no-gos), G293 (rank-blind
ordered label list), and G295/G296 (the rank palindrome and its census collapse): those constrain
the *rank structure*; this pins the *depth-1 boundary value* to a subgroup additive energy and shows
its sign is a prime-scale threshold, not a thinness invariant.

## Formal payload

* `centeredCov p W R` : the exact centered covariance pairing (matches G295).
* `centeredCov_indicator` : the depth-1 reduction to `p · ∑_{x ∈ S} W x - (∑ W)(|S|)` for an
  indicator row.
* Exact `ZMod 17` witness `A17_neg : centeredCov 17 W17 ind17 = -104` (`< 0`).
* Exact `ZMod 41` witness `A41_pos : centeredCov 41 W41 ind41 = 472` (`> 0`).
* `depth1_sign_indeterminate` : the depth-1 CORE covariance takes both signs on `n = 8` sponsor
  cells with identical `T₃`, so its sign is not a function of the thinness `n`.

Axioms are exactly `propext, Classical.choice, Quot.sound`; no `sorry`/`sorryAx`/custom axioms,
no `native_decide`. This file does NOT claim the production δ* statement (CORE OPEN / ON-BGK, #466).
-/

namespace ArkLib.ProximityGap.G298

open Finset

/-- The centered covariance pairing of a gate `W` against a row `R` over `ZMod p`
(matching the G295 `centeredCov`): `p · ∑ₓ W x · R x - (∑ W)(∑ R)`, as an integer. -/
def centeredCov (p : ℕ) [NeZero p] (W R : ZMod p → ℤ) : ℤ :=
  (p : ℤ) * ∑ x : ZMod p, W x * R x
    - (∑ x : ZMod p, W x) * (∑ x : ZMod p, R x)

/-- When the row `R` is the `{0,1}`-indicator of a finite set `S ⊆ ZMod p`, the centered covariance
collapses to `p · ∑_{x ∈ S} W x - (∑ W)(|S|)`. This is the depth-1 specialization: `R_1 = 1_G`. -/
theorem centeredCov_indicator {p : ℕ} [NeZero p] (W : ZMod p → ℤ) (S : Finset (ZMod p)) :
    centeredCov p W (fun x => if x ∈ S then 1 else 0)
      = (p : ℤ) * (∑ x ∈ S, W x) - (∑ x : ZMod p, W x) * (S.card : ℤ) := by
  unfold centeredCov
  have h1 : (∑ x : ZMod p, W x * (if x ∈ S then (1 : ℤ) else 0)) = ∑ x ∈ S, W x := by
    rw [Finset.sum_congr rfl (g := fun x => if x ∈ S then W x else 0)]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
    · intro x _; by_cases hx : x ∈ S <;> simp [hx]
  have h2 : (∑ x : ZMod p, (if x ∈ S then (1 : ℤ) else 0)) = (S.card : ℤ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1, h2]

/-! ### Exact `ZMod 17` sponsor witness `n = 8`, `A_1 = -104 < 0` -/

/-- `W_G` for `G = ⟨9⟩ ≤ F₁₇^*` (order 8), `W_G(x) = #{(y,z) ∈ G² : 2y - z = x}`, tabulated over
`ZMod 17` by residue. -/
def W17 : ZMod 17 → ℤ := fun x =>
  ((([8, 3, 3, 4, 3, 4, 4, 4, 3, 3, 4, 4, 4, 3, 4, 3, 3] : List ℤ)).getD x.val 0)

/-- The order-8 subgroup `G = ⟨9⟩ = {1,2,4,8,9,13,15,16} ≤ F₁₇^*`. -/
def G17 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- Depth-1 row indicator `1_{G17}`. -/
def ind17 : ZMod 17 → ℤ := fun x => if x ∈ G17 then 1 else 0

theorem card_G17 : G17.card = 8 := by decide

theorem sumW17 : (∑ x : ZMod 17, W17 x) = 64 := by decide

/-- `∑_{x ∈ G17} W17 x = T₃ = 24`: the exact 3-AP count of the subgroup. -/
theorem T3_17 : (∑ x ∈ G17, W17 x) = 24 := by decide

/-- Exact negative witness: the depth-1 CORE covariance at `(p,n) = (17,8)` is `-104 < 0`.
`A_1 = p·T₃ - n³ = 17·24 - 512 = -104`. -/
theorem A17_neg : centeredCov 17 W17 ind17 = -104 := by
  have h := centeredCov_indicator W17 G17
  rw [show ind17 = (fun x => if x ∈ G17 then (1:ℤ) else 0) from rfl, h, sumW17, T3_17, card_G17]
  norm_num

theorem A17_lt_zero : centeredCov 17 W17 ind17 < 0 := by rw [A17_neg]; norm_num

/-! ### Exact `ZMod 41` sponsor witness `n = 8`, `A_1 = +472 > 0` (same `n`, same `T₃`) -/

/-- `W_G` for `G = ⟨3⟩ ≤ F₄₁^*` (order 8), tabulated over `ZMod 41` by residue. -/
def W41 : ZMod 41 → ℤ := fun x =>
  ((([0,3,0,3,2,2,0,2,1,3,1,1,2,0,3,2,2,1,0,2,2,2,2,0,1,2,2,3,0,2,1,1,3,1,2,0,2,2,3,0,3]
      : List ℤ)).getD x.val 0)

/-- The order-8 subgroup `G = ⟨3⟩ = {1,3,9,14,27,32,38,40} ≤ F₄₁^*`. -/
def G41 : Finset (ZMod 41) := {1, 3, 9, 14, 27, 32, 38, 40}

/-- Depth-1 row indicator `1_{G41}`. -/
def ind41 : ZMod 41 → ℤ := fun x => if x ∈ G41 then 1 else 0

theorem card_G41 : G41.card = 8 := by decide

theorem sumW41 : (∑ x : ZMod 41, W41 x) = 64 := by decide

/-- `∑_{x ∈ G41} W41 x = T₃ = 24`: the SAME additive 3-AP count as the `p = 17` cell. -/
theorem T3_41 : (∑ x ∈ G41, W41 x) = 24 := by decide

/-- Exact positive witness: the depth-1 CORE covariance at `(p,n) = (41,8)` is `+472 > 0`.
`A_1 = p·T₃ - n³ = 41·24 - 512 = +472`. Same `n`, same `T₃`; only the prime scale changed. -/
theorem A41_pos : centeredCov 41 W41 ind41 = 472 := by
  have h := centeredCov_indicator W41 G41
  rw [show ind41 = (fun x => if x ∈ G41 then (1:ℤ) else 0) from rfl, h, sumW41, T3_41, card_G41]
  norm_num

theorem A41_gt_zero : centeredCov 41 W41 ind41 > 0 := by rw [A41_pos]; norm_num

/-! ### The sign no-go -/

/-- **The depth-1 CORE covariance sign is not fixed by thinness.** There is an `n = 8` sponsor cell
with strictly negative depth-1 covariance and another `n = 8` sponsor cell with strictly positive
depth-1 covariance. Both have the identical additive count `T₃ = 24`; only the prime scale differs
(the threshold `n³/T₃ = 512/24 ≈ 21.3` sits between `p = 17` and `p = 41`). Hence no depth-1
energy functional of the fixed shape `p·T₃ - n³` can certify a fixed CORE covariance sign across
sponsor primes. -/
theorem depth1_sign_indeterminate :
    (centeredCov 17 W17 ind17 < 0) ∧ (centeredCov 41 W41 ind41 > 0)
      ∧ (∑ x ∈ G17, W17 x) = (∑ x ∈ G41, W41 x) := by
  refine ⟨A17_lt_zero, A41_gt_zero, ?_⟩
  rw [T3_17, T3_41]

end ArkLib.ProximityGap.G298
