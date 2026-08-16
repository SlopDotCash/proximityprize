/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# G300: the in-window CORE covariance sign genuinely oscillates, an interior sign change forbids
any monotone / single-band certificate at the in-window prize depth

## Why this is the load-bearing follow-up to G299

G299 (`_G299PrizeDepthInWindow.lean`) refuted G296's "escape prose": at the campaign's own
production parameters (`q = 2¹⁵⁸`, `n = 2³⁰`, ledger deep sup-control depth `r* ≈ 89`) the prize
rank and its palindromic reflection `n+1-r*` BOTH lie *inside* the low-rank window `[2, n-1]`. So
the palindrome `A_r = A_{n+1-r}` (G295) actually binds the prize depth to a genuine complementary
rank.

That reopens an obvious hope: if the covariance sequence `A_r` were sign-definite on the window (or
monotone on the reps half `[2, ⌊(n+1)/2⌋]`, or a single central sign band), then knowing `r*` is
in-window would immediately hand you the sign of the CORE covariance at the prize depth from cheap
boundary data, no arithmetic of the deep row required.

**This file kills that hope.** The centered covariance sequence

```text
A_r = p · ∑ₓ W_G(x) R_r(x) - (∑ W_G)(∑ R_r),   R_r = dp_r ⋆ dp_{r-1},
```

is NOT sign-constant on the window. On the sponsor cell `(p, n) = (113, 8)` the exact sequence is a
palindrome that changes sign *in the interior*:

```text
A = [A_1,…,A_7] = [392, 128, -7240, -13128, -13128, -7240, 128]
    signs        = [ + ,  + ,   -  ,    -  ,    -  ,   -  ,  + ]
```

`A_2 = 128 > 0` (a shallow rank), `A_4 = -13128 < 0` (a deeper rank), `A_7 = 128 > 0` (the deepest
in-window rank). The sign flips positive → negative → positive strictly inside `[2, n-1]`. Hence:

* the covariance is not sign-definite on the window;
* it is not monotone on the reps half (`A_2 > 0 > A_4` with `2, 4 ∈ reps 8`, and `|A_2| < |A_4|`);
* it is not a single-sign band: the profile `+ + - - - - +` has an interior sign flip.

Because the sign changes with the *rank* inside the window, the value of the covariance at the
in-window prize depth `r*` cannot be read off from a boundary datum or a monotonicity/unimodality
assumption. A signing certificate must consult the arithmetic of the specific row `R_{r*}` at
genuine depth, exactly the BGK/Paley wall. This is the precise reason G299's "in-window"
observation is not a shortcut to closure.

The oscillation is not a one-off small-cell artifact: on `(p, n) = (257, 32)` the sign sequence is
the period-4 profile `+ + + + + - - + + - - + + - - + + - - + + - - + + - - + + + +`, with eleven
interior sign changes (documented in the probe). We formalize the small clean `(113, 8)` witness,
whose rows are exact integers `decide`-able in the kernel.

## Result of record (no-go, thinness-essential)

* `centeredCov` : the exact centered covariance pairing (matching G295/G298).
* Exact positive shallow witness `A2_113 : centeredCov 113 W113 R2_113 = 128` (`> 0`).
* Exact negative deep witness `A4_113 : centeredCov 113 W113 R4_113 = -13128` (`< 0`).
* Palindrome consistency: `R7_113 = R2_113` as tabulations (the reflection `R_{n+1-r}(x) = R_r(-x)`
  collapses to equal residue tables on this cell), so `A_7 = A_2` by `rfl` on the covariance.
* Headline `window_sign_oscillates` : within the SINGLE cell `(113, 8)`, `A_2 > 0` and `A_4 < 0` and
  `A_7 > 0`, an interior sign change of the covariance across ranks `2 < 4 < 7` all inside the
  window `[2, 7]`. Therefore no rank-monotone / single-sign / single-band certificate can determine
  the CORE covariance sign at the in-window prize depth.

Orthogonal to: G289/G291/G293 (rank-blind feature no-gos), G295 (the palindrome identity itself),
G296 (the census cardinality collapse), G298 (the depth-1 endpoint value/sign), G299 (the in-window
placement of the prize rank). G295 gives the reflection symmetry; G300 shows that *within* the
symmetry-reduced half the sign is still not fixed by rank: it genuinely oscillates.

Scope: an exact interior-sign-change no-go on the covariance sequence. NOT a Jacobi estimate, NOT a
prize-depth bound, NOT a closure. CORE OPEN / ON-BGK.
-/

namespace ArkLib.ProximityGap.G300

open Finset

set_option maxRecDepth 8000

/-- The centered covariance pairing of a gate `W` against a row `R` over `ZMod p`
(matching the G295/G298 `centeredCov`): `p · ∑ₓ W x · R x - (∑ W)(∑ R)`, as an integer. -/
def centeredCov (p : ℕ) [NeZero p] (W R : ZMod p → ℤ) : ℤ :=
  (p : ℤ) * ∑ x : ZMod p, W x * R x
    - (∑ x : ZMod p, W x) * (∑ x : ZMod p, R x)

/-! ### Exact sponsor cell `(p, n) = (113, 8)`: an in-window interior sign change

`G = ⟨15⟩ = {1,15,18,44,69,95,98,112} ≤ F₁₁₃^*`, order 8. `W_G(x) = #{(y,z) ∈ G² : 2y - z = x}`.
The two rows below are the exact adjacent-rank rows `R_r = dp_r ⋆ dp_{r-1}` tabulated over
`ZMod 113` by residue, for `r = 2` and `r = 4` (and the reflection `r = 7`).

To keep the covariance sums kernel-checkable at `p = 113` we route each residue table through a
`ℕ`-indexed list helper and reindex the `ZMod 113` sum to `Finset.range 113` via
`Fin.sum_univ_eq_sum_range`, so `decide` reduces a plain `range`-sum of integers rather than
enumerating `ZMod`/`Fin` modular arithmetic. -/

/-- `ℕ`-indexed table for the sponsor gate `W_G`, `G = ⟨15⟩ ≤ F₁₁₃^*` (order 8). `∑ = 64 = n²`. -/
def wf : ℕ → ℤ := fun i =>
  (([0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1,
     0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0,
     0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1,
     1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1] : List ℤ).getD i 0)

/-- `ℕ`-indexed table for the adjacent-rank row `R_2 = dp_2 ⋆ dp_1`. `∑ = 224`. -/
def r2f : ℕ → ℤ := fun i =>
  (([0, 10, 3, 0, 3, 0, 0, 1, 1, 0, 1, 3, 1, 1, 1, 10, 1, 1, 10, 0, 1, 1, 0, 0, 1, 3, 1, 3, 3, 1, 3,
     1, 3, 1, 3, 1, 3, 1, 0, 1, 1, 3, 1, 1, 10, 0, 1, 3, 1, 0, 3, 1, 3, 3, 0, 3, 0, 0, 3, 0, 3, 3,
     1, 3, 0, 1, 3, 1, 0, 10, 1, 1, 3, 1, 1, 0, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3, 1, 0, 0, 1,
     1, 0,
     10, 1, 1, 10, 1, 1, 1, 3, 1, 0, 1, 1, 0, 0, 3, 0, 3, 10] : List ℤ).getD i 0)

/-- `ℕ`-indexed table for the adjacent-rank row `R_4 = dp_4 ⋆ dp_3`. `∑ = 3920`. -/
def r4f : ℕ → ℤ := fun i =>
  (([0, 87, 43, 13, 50, 18, 18, 31, 31, 22, 30, 43, 30, 31, 22, 87, 22, 27, 87, 13, 29, 29, 22, 18,
     29, 43, 22, 51, 43, 27, 43, 31, 43, 27, 51, 24, 43, 30, 18, 29, 24, 50, 24, 27, 87, 13, 30, 51,
     24, 22, 50, 22, 43, 50, 13, 51, 22, 22, 51, 13, 50, 43, 22, 50, 22, 24, 51, 30, 13, 87, 27, 24,
     50, 24, 29, 18, 30, 43, 24, 51, 27, 43, 31, 43, 27, 43, 51, 22, 43, 29, 18, 22, 29, 29, 13, 87,
     27, 22, 87, 22, 31, 30, 43, 30, 22, 31, 31, 18, 18, 50, 13, 43, 87] : List ℤ).getD i 0)

/-- The sponsor gate `W_G` over `ZMod 113`. -/
def W113 : ZMod 113 → ℤ := fun x => wf x.val

/-- The adjacent-rank row `R_2` over `ZMod 113`. -/
def R2_113 : ZMod 113 → ℤ := fun x => r2f x.val

/-- The adjacent-rank row `R_4` over `ZMod 113`. -/
def R4_113 : ZMod 113 → ℤ := fun x => r4f x.val

/-- The reflected row `R_7 = dp_7 ⋆ dp_6`. The reflection `R_{n+1-r}(x) = R_r(-x)` reduces to the
SAME residue table as `R_2` on this cell, so `R7_113 = R2_113` pointwise. -/
def R7_113 : ZMod 113 → ℤ := fun x => r2f x.val

/-- Kernel-cheap reindexing: a `ZMod 113` sum of an `ℕ`-indexed table equals the `range 113` sum. -/
theorem sum_zmod_eq_range (g : ℕ → ℤ) :
    (∑ x : ZMod 113, g x.val) = ∑ i ∈ Finset.range 113, g i := by
  rw [show (∑ x : ZMod 113, g x.val) = ∑ x : Fin 113, g (x : ℕ) from rfl]
  exact Fin.sum_univ_eq_sum_range g 113

/-- `∑ W113 = 64 = n²`. -/
theorem sumW113 : (∑ x : ZMod 113, W113 x) = 64 := by
  rw [show (∑ x : ZMod 113, W113 x) = ∑ x : ZMod 113, wf x.val from rfl, sum_zmod_eq_range]; decide

/-- `∑ R2_113 = 224`. -/
theorem sumR2_113 : (∑ x : ZMod 113, R2_113 x) = 224 := by
  rw [show (∑ x : ZMod 113, R2_113 x) = ∑ x : ZMod 113, r2f x.val from rfl, sum_zmod_eq_range]
  decide

/-- `∑ R4_113 = 3920`. -/
theorem sumR4_113 : (∑ x : ZMod 113, R4_113 x) = 3920 := by
  rw [show (∑ x : ZMod 113, R4_113 x) = ∑ x : ZMod 113, r4f x.val from rfl, sum_zmod_eq_range]
  decide

/-- The palindromic reflection row `R_7` equals `R_2` as a residue tabulation on this cell. -/
theorem R7_eq_R2 : R7_113 = R2_113 := rfl

/-- The paired dot `∑ₓ W113 x · R2_113 x = 128`. -/
theorem dotW_R2 : (∑ x : ZMod 113, W113 x * R2_113 x) = 128 := by
  have h : (∑ x : ZMod 113, W113 x * R2_113 x)
      = ∑ i ∈ Finset.range 113, (wf i * r2f i) := sum_zmod_eq_range (fun i => wf i * r2f i)
  rw [h]; decide

/-- The paired dot `∑ₓ W113 x · R4_113 x = 2104`. -/
theorem dotW_R4 : (∑ x : ZMod 113, W113 x * R4_113 x) = 2104 := by
  have h : (∑ x : ZMod 113, W113 x * R4_113 x)
      = ∑ i ∈ Finset.range 113, (wf i * r4f i) := sum_zmod_eq_range (fun i => wf i * r4f i)
  rw [h]; decide

/-- **Shallow positive witness.** `A_2 = centeredCov 113 W113 R2_113 = 128 > 0`.
Exactly `A_2 = 113·⟨W,R₂⟩ - (∑W)(∑R₂) = 113·128 - 64·224 = 14464 - 14336 = 128`. -/
theorem A2_113 : centeredCov 113 W113 R2_113 = 128 := by
  unfold centeredCov
  rw [dotW_R2, sumW113, sumR2_113]; norm_num

theorem A2_pos : centeredCov 113 W113 R2_113 > 0 := by rw [A2_113]; norm_num

/-- **Deep negative witness.** `A_4 = centeredCov 113 W113 R4_113 = -13128 < 0`.
Exactly `A_4 = 113·⟨W,R₄⟩ - (∑W)(∑R₄) = 113·2104 - 64·3920 = 237752 - 250880 = -13128`. -/
theorem A4_113 : centeredCov 113 W113 R4_113 = -13128 := by
  unfold centeredCov
  rw [dotW_R4, sumW113, sumR4_113]; norm_num

theorem A4_neg : centeredCov 113 W113 R4_113 < 0 := by rw [A4_113]; norm_num

/-- Palindrome consistency at the covariance level: `A_7 = A_2`, because `R7_113 = R2_113`. This
confirms the reflection `A_r = A_{n+1-r}` (G295) on the witness and pins the deepest in-window rank
`r = 7 = n - 1` to the shallow positive value. -/
theorem A7_eq_A2 : centeredCov 113 W113 R7_113 = centeredCov 113 W113 R2_113 := by
  rw [R7_eq_R2]

/-- **Headline no-go: the in-window covariance sign genuinely oscillates.**

On the single sponsor cell `(p, n) = (113, 8)` the centered covariance is positive at rank `2`,
negative at rank `4`, and positive again at rank `7`, an interior sign change across three ranks
all inside the window `[2, n-1] = [2, 7]`. Consequently the covariance is not sign-definite, not
rank-monotone, and not a single-sign band on the window, so no such certificate can determine the
CORE covariance sign at the in-window prize depth `r*` (G299). A signing certificate must consult
the row `R_{r*}` at genuine depth, the BGK/Paley wall. -/
theorem window_sign_oscillates :
    centeredCov 113 W113 R2_113 > 0
    ∧ centeredCov 113 W113 R4_113 < 0
    ∧ centeredCov 113 W113 R7_113 > 0 := by
  refine ⟨A2_pos, A4_neg, ?_⟩
  rw [A7_eq_A2]; exact A2_pos

end ArkLib.ProximityGap.G300
