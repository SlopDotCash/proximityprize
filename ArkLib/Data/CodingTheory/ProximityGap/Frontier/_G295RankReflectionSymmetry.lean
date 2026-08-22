/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# G295: the CORE covariance is palindromic on the rank window — `A_r = A_{n+1-r}`

## Statement of record

Let `G ≤ F_p^*` be the order-`n` multiplicative subgroup, `n` even (the sponsor 2-power regime).
Write the sponsor gate and the adjacent-rank row

```text
W_G(x) = #{(y,z) ∈ G² : 2y - z = x},     R_r(x) = (dp_r ⋆ dp_{r-1})(x),
```

and the CORE covariance `A_r = p · ∑_x W_G(x) R_r(x) - (∑ W_G)(∑ R_r)`.

Then, EXACTLY and for every cell, the covariance sequence is a **palindrome in the rank**:

```text
A_r = A_{n+1-r}      for all r ∈ [2, n-1].
```

At the two late-Newton ranks this reads `A_5 = A_{n-4}` and `A_6 = A_{n-5}`: each low rank is
pinned to a HIGH near-complementary rank.

## The mechanism (why it is a genuine rank-coupling, not a rank-blind feature)

Everything below is `n` even. Then `-1 ∈ G` (the unique order-2 element sits in the 2-power tower),
`∑ G = 0` in `F_p`, so subset complementation `A ↦ G ∖ A` gives the reflection of the subset-sum
histograms

```text
dp_r(x) = dp_{n-r}(-x)      (σ = ∑G = 0),
```

hence for the adjacent-rank rows

```text
R_{n+1-r}(x) = R_r(-x).
```

Because `-1 ∈ G`, the gate is even, `W_G(-x) = W_G(x)`. The centered covariance is a bilinear
pairing
of `W_G` against the row, and reflecting the row by `x ↦ -x` while `W_G` is even leaves the pairing
invariant. That is the whole proof. It **couples two different ranks** `r` and `n+1-r` through the
complementation involution — it is not another rank-blind functional (G289/G291/G293), it is an
exact identity between the covariance at rank `r` and that at the complementary rank.

## Why this is high information for the campaign

Every exact finite-cell census the campaign runs (the four-quadrant probes G266, the thinness
separation G267, the counting-mirage floor G289/G291, the rank-blind label list G293) lives at fixed
low ranks `r ∈ {5,6}` on cells `n ∈ {8,16,32}`. This theorem shows those rank-`5,6` covariances are
NOT independent data points: they are *identical* to the rank `n-4, n-5` covariances. The census
degrees of freedom collapse by the reflection; any sign freedom observed at a low rank is literally
the same number as at the near-full complementary rank.

The production depth does **not** escape this window. The campaign parameters are `n = 2^30` and
`r* = 89`, so `2 ≤ r* ≤ n-1`, and the reflected partner is `n+1-r* = 2^30-88`. More generally,
for fixed `β = 5.27`, `log p = o(p^(1/β))`, hence `r = O(log p)` is eventually much smaller than
`n ≍ p^(1/β)`. The palindrome therefore remains applicable at production depth, but by itself gives
only an equality with a near-full complementary rank. It supplies no sign or magnitude bound for
either member of the pair.

This is a structural theorem (an exact rank-coupling identity), not a Jacobi covariance estimate and
not a prize closure. The missing certificate remains a direct rank-labelled estimate at the actual
production depth (equivalently at its complementary rank), on the BGK/Paley wall.

## Formal payload

* Abstract layer, arbitrary finite `ZMod p`:
  - `neg_involutive_sum` : reindexing a sum by `x ↦ -x`.
  - `centeredCov` : the centered covariance pairing.
  - `centeredCov_reflect_of_even` : if `W` is even and `R' x = R (-x)`, then
    `centeredCov p W R' = centeredCov p W R`. THE mechanism.
* Concrete consumer, exact `ZMod 17` sponsor cell `n = 8, p = 17` (`G = ⟨9⟩`, `∑G = 0`):
  - `W17` (even), `R3`, `R6` with `R3 (-x) = R6 x` (`reflectR_3_6`);
  - `A17_3_eq_A17_6` : `centeredCov 17 W17 R3 = centeredCov 17 W17 R6` — the prize-adjacent identity
    `A_3 = A_6` obtained purely from the reflection mechanism, exact integers.

This file does NOT claim the production δ* statement (CORE OPEN / ON-BGK, issue #466).

Companion probe `scripts/probes/g295_rank_reflection_symmetry.py` verifies `A_r = A_{n+1-r}`
universally across sponsor cells `n ∈ {8,16,32}`, exhibits `A_5 = A_{n-4}`, `A_6 = A_{n-5}` on the
production cells, and confirms `σ = ∑G = 0`, `W` even, `R_{n+1-r}(x) = R_r(-x)` for `n` even.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G295RankReflectionSymmetry

variable {p : ℕ} [NeZero p]

/-- Reindexing a full `ZMod p` sum by the negation involution `x ↦ -x` leaves it unchanged. -/
theorem neg_involutive_sum (f : ZMod p → ℤ) :
    ∑ x : ZMod p, f (-x) = ∑ x : ZMod p, f x := by
  refine Fintype.sum_bijective (fun x => -x) ?_ _ _ (fun x => rfl)
  exact (Equiv.neg (ZMod p)).bijective

/-- The centered covariance pairing of a gate `W` against a row `R` on `ZMod p`:
`centeredCov p W R = p · ∑ W·R - (∑ W)(∑ R)`. -/
def centeredCov (W R : ZMod p → ℤ) : ℤ :=
  (p : ℤ) * (∑ x : ZMod p, W x * R x) - (∑ x : ZMod p, W x) * (∑ x : ZMod p, R x)

/-- **The mechanism.** If the gate `W` is even (`W (-x) = W x`) and `R'` is the reflection of `R`
(`R' x = R (-x)`), then the centered covariance is unchanged:
`centeredCov p W R' = centeredCov p W R`.

Consequence: the CORE covariance `A_r` is invariant under any row reflection that a subset-sum
complementation induces, which for `n` even sends rank `r` to rank `n+1-r`. -/
theorem centeredCov_reflect_of_even
    (W R R' : ZMod p → ℤ)
    (hW : ∀ x : ZMod p, W (-x) = W x)
    (hR' : ∀ x : ZMod p, R' x = R (-x)) :
    centeredCov (p := p) W R' = centeredCov (p := p) W R := by
  unfold centeredCov
  have hsumR' : (∑ x : ZMod p, R' x) = ∑ x : ZMod p, R x := by
    calc (∑ x : ZMod p, R' x) = ∑ x : ZMod p, R (-x) := by
            exact Finset.sum_congr rfl (fun x _ => hR' x)
      _ = ∑ x : ZMod p, R x := neg_involutive_sum R
  have hstep1 : (∑ x : ZMod p, W x * R' x) = ∑ x : ZMod p, W x * R (-x) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hR' x]
  -- reindex `x ↦ -x`: `∑ W x · R(-x) = ∑ W(-x) · R(-(-x))`
  have hstep2 : (∑ x : ZMod p, W x * R (-x)) = ∑ x : ZMod p, W (-x) * R (-(-x)) := by
    refine (Fintype.sum_bijective (fun x => -x) (Equiv.neg (ZMod p)).bijective
      (fun x => W (-x) * R (-(-x))) (fun x => W x * R (-x)) (fun x => ?_)).symm
    simp only [neg_neg]
  -- `W` even and `R(-(-x)) = R x`
  have hstep3 : (∑ x : ZMod p, W (-x) * R (-(-x))) = ∑ x : ZMod p, W x * R x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hW x, neg_neg]
  have hpair : (∑ x : ZMod p, W x * R' x) = ∑ x : ZMod p, W x * R x := by
    rw [hstep1, hstep2, hstep3]
  rw [hpair, hsumR']

/-!
## Exact `ZMod 17` sponsor witness (`n = 8, p = 17`, `G = ⟨9⟩ = {1,9,13,15,16,8,4,2}`, `∑G = 0`)

Data recomputed float-free by the companion probe. `W17` is the sponsor gate `#{2y-z=x}`, and
`R3, R6` are the exact adjacent-rank rows at `r = 3` and `r = n+1-r = 6`. They satisfy
`R3 (-x) = R6 x`, and `W17` is even, so the mechanism yields `A_3 = A_6` exactly.
-/

/-- Sponsor gate `W_G(x) = #{(y,z) ∈ G² : 2y - z = x}` on the `n = 8, p = 17` cell. Even. -/
def W17 : ZMod 17 → ℤ := fun x =>
  ![8, 3, 3, 4, 3, 4, 4, 4, 3, 3, 4, 4, 4, 3, 4, 3, 3] x

/-- Adjacent-rank row `R_3 = dp_3 ⋆ dp_2` on the `n = 8, p = 17` cell. -/
def R3 : ZMod 17 → ℤ := fun x =>
  ![80, 96, 96, 90, 96, 90, 90, 90, 96, 96, 90, 90, 90, 96, 90, 96, 96] x

/-- Adjacent-rank row `R_6 = dp_6 ⋆ dp_5` on the `n = 8, p = 17` cell (`r = n+1-3 = 6`). -/
def R6 : ZMod 17 → ℤ := fun x =>
  ![80, 96, 96, 90, 96, 90, 90, 90, 96, 96, 90, 90, 90, 96, 90, 96, 96] x

/-- The gate is even: `W17 (-x) = W17 x` for every `x : ZMod 17`. -/
theorem W17_even (x : ZMod 17) : W17 (-x) = W17 x := by
  fin_cases x <;> rfl

/-- Reflection identity `R_6(x) = R_3(-x)`: rank 6 is the complement-reflection of rank 3. -/
theorem reflectR_3_6 (x : ZMod 17) : R6 x = R3 (-x) := by
  fin_cases x <;> rfl

/-- **Exact prize-adjacent identity.** On the `n = 8, p = 17` sponsor cell the CORE covariance at
rank 3 equals the covariance at rank `6 = n+1-3`, purely by the reflection mechanism
(`W17` even, `R6 x = R3 (-x)`). Both equal `-1344`. -/
theorem A17_3_eq_A17_6 :
    centeredCov (p := 17) W17 R3 = centeredCov (p := 17) W17 R6 := by
  refine (centeredCov_reflect_of_even (p := 17) W17 R3 R6 W17_even ?_).symm
  intro x; exact reflectR_3_6 x

-- Scope note: this file records a structural rank-reflection identity
-- (`centeredCov_reflect_of_even` + exact `ZMod 17` consumer `A17_3_eq_A17_6`). It does NOT
-- claim the
-- production δ* statement; the CORE prize inequality remains OPEN / ON-BGK. Tracked by issue #466.

end ArkLib.ProximityGap.Frontier.G295RankReflectionSymmetry
