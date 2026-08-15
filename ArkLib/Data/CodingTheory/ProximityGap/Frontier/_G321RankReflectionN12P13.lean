/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Contributor: Shane Coy - github.com/shane9coy - shanec.dev@gmail.com
-/
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # G321: the rank-reflection palindrome at the (n=12, p=13) sponsor cell

## Statement of record

The CORE covariance `A_r = p · ∑_x W_G(x) R_r(x) - (∑ W_G)(∑ R_r)` is a **palindrome in the
rank** for even `n`:

```text
A_r = A_{n+1-r}      for all r ∈ [2, n-1].
```

G295 proved this structurally (`centeredCov_reflect_of_even`) and exhibited the ZMod 17
witness at `(n=8, p=17)`: `A_3 = A_6 = -1344`.

This file extends the witness to a SECOND clean cell `(n=12, p=13)`, where `G = F_13^*` is the
FULL multiplicative group (`12 | 12`). On this cell the late-Newton ranks 5 and 8 satisfy

```text
A_5 = A_8 = -12.
```

The integer `-12` is much smaller than the G295 cell's `-1344`, which makes this witness
easier to audit by hand: `W13` is almost-constant (`W13[0] = 12`, `W13[x ≠ 0] = 11`),
`R_5` and `R_8` are also almost-constant (`30156` at 0, `30157` elsewhere), and the
centred-covariance subtraction lands at `-12` because the rank rows carry `30157 - 30156 = 1`
of "rank mass" into the gate that the centering removes.

THINNESS-ESSENTIAL. The palindrome mechanism (G295's `centeredCov_reflect_of_even`) requires
*only* the even-`n` hypothesis (`σ = ∑G = 0`, `-1 ∈ G`, `W_G` even). It does **not** require
any bound on the cap, the partition profile, or the depth. This file is a structural identity
between two ranks at one cell, not a magnitude estimate and not a prize closure.

SCOPE / no prize claim. As with G295, the palindrome is a rank-coupling identity, not a
prize-relevant estimate. The CORE prize inequality remains OPEN / ON-BGK. This file
records a clean secondary witness `(n=12, p=13)` with `A_5 = A_8 = -12`, useful for the
probing pattern's two-cell coverage.

KERNEL SCOPE. This file pins the witness integers (gate, two rank rows, the `A_5 = A_8`
palindrome) using `decide` (kernel-blessed for `ℤ` literal equality) and `rfl` after
`fin_cases` on `ZMod 13`. No `native_decide` / `bv_decide` (campaign gate rejects), no
`sorry`, no general theorem (unverifiable here without `elan`/`lake`). The reflection
identity `R_5(x) = R_8(-x)` is a direct `fin_cases` verification; the palindrome
`A_5 = A_8` is the abstract mechanism from G295 instantiated at `ZMod 13`; the shared
value `-12` is a `decide` reduction of the closed integer expression.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G321RankReflectionN12P13

/-! ## Abstract mechanism (re-imported from G295)

We restate the centered-covariance reflection identity for completeness. This is the
self-contained kernel proof; the broader machinery (sum_G = 0, the G295 evidence at
ZMod 17) lives in `_G295RankReflectionSymmetry.lean`. -/

variable {p : ℕ} [NeZero p]

/-- The centered covariance pairing of a gate `W` against a row `R` on `ZMod p`:
`centeredCov p W R = p · ∑ W·R - (∑ W)(∑ R)`. -/
def centeredCov (W R : ZMod p → ℤ) : ℤ :=
  (p : ℤ) * (∑ x : ZMod p, W x * R x) - (∑ x : ZMod p, W x) * (∑ x : ZMod p, R x)

/-- Reindexing a full `ZMod p` sum by the negation involution `x ↦ -x` leaves it unchanged. -/
theorem neg_involutive_sum (f : ZMod p → ℤ) :
    ∑ x : ZMod p, f (-x) = ∑ x : ZMod p, f x := by
  refine Fintype.sum_bijective (fun x => -x) ?_ _ _ (fun x => rfl)
  exact (Equiv.neg (ZMod p)).bijective

/-- The mechanism: if the gate `W` is even (`W (-x) = W x`) and `R'` is the reflection of `R`
(`R' x = R (-x)`), then the centered covariance is unchanged:
`centeredCov p W R' = centeredCov p W R`. (G295, restated here for self-containment.) -/
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
  have hstep2 : (∑ x : ZMod p, W x * R (-x)) = ∑ x : ZMod p, W (-x) * R (-(-x)) := by
    refine (Fintype.sum_bijective (fun x => -x) (Equiv.neg (ZMod p)).bijective
      (fun x => W (-x) * R (-(-x))) (fun x => W x * R (-x)) (fun x => ?_)).symm
    simp only [neg_neg]
  have hstep3 : (∑ x : ZMod p, W (-x) * R (-(-x))) = ∑ x : ZMod p, W x * R x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hW x, neg_neg]
  have hpair : (∑ x : ZMod p, W x * R' x) = ∑ x : ZMod p, W x * R x := by
    rw [hstep1, hstep2, hstep3]
  rw [hpair, hsumR']

/-! ## Exact `ZMod 13` sponsor witness (`n = 12, p = 13`, `G = F_13^* = {1,2,...,12}`,
`∑G = 0`, `-1 = 12 ∈ G`, `W13` even, `R_5(x) = R_8(-x)`, `A_5 = A_8 = -12`). -/

/-- Sponsor gate `W_G(x) = #{(y,z) ∈ G² : 2y - z = x}` on the `n = 12, p = 13` cell.
`G = F_13^*` is the full multiplicative group, so `W13[0] = 12` (the diagonal `y = z` maps
to `2y - y = y`, hitting every element once; the row `z = 2y` is the 12-element kernel
of the map `y ↦ 2y - z` at `x = 0`); for `x ≠ 0`, exactly one of the 12 `y`-values forces
`z = 0` (excluded), so `W13[x ≠ 0] = 11`. Even. -/
def W13 : ZMod 13 → ℤ := fun x =>
  ![12, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] x

/-- Adjacent-rank row `R_5 = dp_5 ⋆ dp_4` on the `n = 12, p = 13` cell. -/
def R5 : ZMod 13 → ℤ := fun x =>
  ![30156, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157] x

/-- Adjacent-rank row `R_8 = dp_8 ⋆ dp_7` on the `n = 12, p = 13` cell (`8 = n + 1 - 5`). -/
def R8 : ZMod 13 → ℤ := fun x =>
  ![30156, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157, 30157] x

/-- The gate is even: `W13 (-x) = W13 x` for every `x : ZMod 13`. -/
theorem W13_even (x : ZMod 13) : W13 (-x) = W13 x := by
  fin_cases x <;> rfl

/-- Reflection identity `R_5(x) = R_8(-x)`: rank 5 is the complement-reflection of rank 8. -/
theorem reflectR_5_8 (x : ZMod 13) : R5 x = R8 (-x) := by
  fin_cases x <;> rfl

/-- **Exact palindrome at (n=12, p=13).** `centeredCov 13 W13 R5 = centeredCov 13 W13 R8` —
the CORE covariance at rank 5 equals that at the complementary rank `8 = n+1-5`, purely
by the reflection mechanism (`W13` even, `R_5(x) = R_8(-x)`). Both equal `-12`. -/
theorem A13_5_eq_A13_8 :
    centeredCov (p := 13) W13 R5 = centeredCov (p := 13) W13 R8 := by
  refine (centeredCov_reflect_of_even (p := 13) W13 R5 R8 W13_even ?_).symm
  intro x; have h := (reflectR_5_8 (-x)).symm; rwa [neg_neg] at h

/-- The shared value, pinned: `A_5 = A_8 = -12` at the `(n=12, p=13)` sponsor cell.

Proof: the closed integer expression `centeredCov 13 W13 R5` unfolds to
`13 * 4342596 - 144 * 392040 = 56453748 - 56453760 = -12`, which is decidable
via `Int.decEq`. (Computed in `scripts/probes/g321_rank_reflection_n12_p13.py`.) -/
theorem A13_5_eq_neg_12 : centeredCov (p := 13) W13 R5 = -12 := by
  decide

end ArkLib.ProximityGap.Frontier.G321RankReflectionN12P13
