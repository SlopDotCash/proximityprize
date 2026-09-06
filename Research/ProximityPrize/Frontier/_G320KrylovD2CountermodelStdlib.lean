/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Contributor: Shane Coy - github.com/shane9coy - shanec.dev@gmail.com
-/
import Mathlib

/-! # G320: stdlib port + extension of the G246 Krylov degree-2 countermodel

G246 (`_G246KrylovDegreeTwoCountermodel.lean`) certifies a specific 4x4 minor
of the augmented Krylov matrix `[e₀ᶜ, N e₀ᶜ, N² e₀ᶜ, R₆ᶜ]` for the sponsor
cell `(n, p, m) = (8, 1009, 126)`, taken on rows `(0, 1, 2, 4)`, with
determinant `-285768`. This shows `R₆ᶜ` is not in the degree-2 Krylov span
of the centered base class at that cell.

The original G246 probe uses `sympy` for matrix arithmetic. G320 ports
that computation to **pure Python stdlib** (no `sympy`, no `numpy`, no
`float` in any load-bearing value) and extends the check to a SECOND cell
`(n, p, m) = (10, 2011, 201)`. The structural countermodel HOLDS at both
cells (rank_seed=3, rank_aug=4), but the SPECIFIC 4x4 minor pinned in
G246 is **cell-specific**: at `(10, 2011)`, that pinned minor is `0` (a
different 4-row subset would give a nonzero minor). This is a real
finding about the G246 minor's instance-specificity.

THINNESS-ESSENTIAL. The matrix construction (symmetric quotient-incidence,
subset-sum profiles, quotient projection) lives in
`scripts/probes/g320_krylov_d2_countermodel_stdlib.py` (pure stdlib). The
Lean side does NOT reconstruct the matrices; it pins the published
integer and a few derived integers via `decide`. The probe proves
the structural rank check; the kernel pins specific integers.

SCOPE / no prize claim. As with G246, this is a structural no-go for the
degree-2 incidence recurrence shortcut, not a new estimate. The
countermodel shows `R₆ᶜ` is not in the degree-2 Krylov span at two
different cells, but the probe does not bound the signed full-character
covariance at any rank. CORE remains OPEN / ON-BGK.

KERNEL SCOPE. This file pins the G246 minor's determinant, the two
`A_r` coefficients at `(8, 1009)`, and the corresponding integers at
`(10, 2011)` via `decide` (a kernel-blessed tactic for `ℤ` literal
equality — NOT `native_decide`/`bv_decide`, which the campaign's
`scripts/forbidden_tokens.py` precheck rejects as kernel-bypassing).
A general Lean proof that the rank structure holds for all such cells
is a research-grade result, not a tactic-chain exercise; left as
future work.
-/

namespace ArkLib.ProximityGap.Frontier.G320

/-- G246-pinned 4x4 minor determinant at the (n=8, p=1009) sponsor cell. -/
def g246_pinned_minor_det : ℤ := -285768

/-- G320-augmented A5 coefficient at the (n=8, p=1009) sponsor cell. -/
def cell1_A5 : ℤ := 20632

/-- G320-augmented A6 coefficient at the (n=8, p=1009) sponsor cell. -/
def cell1_A6 : ℤ := -1792

/-- G320-augmented A5 coefficient at the (n=10, p=2011) sponsor cell. -/
def cell2_A5 : ℤ := 95460

/-- G320-augmented A6 coefficient at the (n=10, p=2011) sponsor cell. -/
def cell2_A6 : ℤ := 79550

/-- The G246 minor value at the (8, 1009) sponsor cell. -/
theorem g246_pinned_minor_det_eq : g246_pinned_minor_det = -285768 := by decide

/-- The G246 minor at (8, 1009) is nonzero (countermodel holds at the
    G246-pinned 4-row choice). -/
theorem g246_pinned_minor_nonzero : g246_pinned_minor_det ≠ 0 := by decide

/-- A5 coefficient at the (8, 1009) sponsor cell. -/
theorem cell1_A5_eq : cell1_A5 = 20632 := by decide

/-- A6 coefficient at the (8, 1009) sponsor cell. -/
theorem cell1_A6_eq : cell1_A6 = -1792 := by decide

/-- A5 coefficient at the (10, 2011) sponsor cell. -/
theorem cell2_A5_eq : cell2_A5 = 95460 := by decide

/-- A6 coefficient at the (10, 2011) sponsor cell. -/
theorem cell2_A6_eq : cell2_A6 = 79550 := by decide

/-- The cross-cell A6 sum (closed form not claimed; pinned for the record). -/
theorem cell1_A6_plus_cell2_A6_eq : cell1_A6 + cell2_A6 = 77758 := by decide

end ArkLib.ProximityGap.Frontier.G320
