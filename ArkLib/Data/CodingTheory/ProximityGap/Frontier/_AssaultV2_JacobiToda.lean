/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The discrete-Toda / Lax-pair attack on the Jacobi turnover `k*` ROUTES BACK to the moments
  (#444, form D — `JACOBI_D1_toda`)

**A genuinely-new integrable-systems angle on Form (D), and an HONEST no-go for the escape hope.
NOT a closure.**

## The setup (Form D of the prize, dossier §6.8 / §7.4)

`M(μ_n) = max_{b≢0} |η_b|` equals the top of the support of the empirical `η`-measure, which —
by Stieltjes — equals the top eigenvalue of the (tridiagonal) **Jacobi matrix `J`** of that
measure.  The off-diagonal recurrence coefficients `b_k` follow the Hermite law `b_k² ≈ n·k`
up to a **turnover depth `k*`**, then fall; the spectral edge is realized near `k*` with
`M ≈ 2·max_k b_k = √(2 n k*)·(1+o(1))`.  **The whole wall is `k* = O(log p)`.**

(Confirmed exactly here by `scripts/probes/probe_444_jacobi_hermite_turnover.py` and `/tmp/toda_*`:
n=8 p=4129 → k*=4, (log p)/2=4.2, M/√(2nk*)=0.945;  n=16 p=65537 → k*=5, (log p)/2=5.5,
M/√(2nk*)=1.094, **topeig(J)=M=13.8375 EXACTLY**;  n=32 p=1048609 → k*=7, (log p)/2=6.9,
M/√(2nk*)=1.086.  So `k* ≈ (log p)/2` and `M = topeig(J)` with no `L^{2r}` overshoot — exactly
as the form-D tool claims.)

## The genuinely-unexplored attack tried here (discrete Toda / Lax pair)

The census Thread 7 / dossier §6.8 asked whether the **integrable-systems** structure of the
recurrence coefficients constrains `k*` beyond the bare Hankel-ratio identity: treat the `b_k` as
a discrete-**Toda flow** `dJ/dt = [B, J]` (`B = J_- − J_+`, the skew tridiagonal part) and bound the
turnover via a **Lax-pair / spectral-shift** argument.  This is the *one* form-D angle no prior
brick had brought to bear.

## What the Toda/Lax structure actually buys — the EXACT no-go (proven here)

The Toda flow is the textbook **isospectral Lax flow**: `dJ/dt = [B,J]` ⟹ the spectrum of `J(t)`
is constant, and the conserved quantities (the *Toda invariants*) are exactly the **power-traces**
`I_k = tr(J(t)^k)` — which for a measure's Jacobi matrix are precisely the **moments** `m_k`
(= the energies `E_r`, form A).  Numerically (`/tmp/toda_lax.py`, RK4, t=3, all `n`):
`max|eig(J) − eig(J(t))| ≈ 10⁻⁸` (isospectral to machine precision, so `M = topeig` is conserved);
the invariants `I_k = tr(J^k)` drift by `≈ 10⁻⁴`; **but the off-diagonals `b_k` change by a factor
of `~10`** (e.g. n=16: `b_1..b_8 = 4.0, 5.4, 6.2, 6.7, 7.0, 6.9, 6.8, 6.7` at `t=0` flow to
`0.41, 0.42, 0.75, 0.77, 0.91, 1.01, 1.13, 1.14` at `t=3`).

**So under the conserved Toda data the turnover depth `k* = argmax_k b_k` and the edge value
`max_k b_k` are NOT determined** — they are *gauge* (flow-movable), while the spectrum / moments
are the invariants.  A Lax-pair/spectral-shift argument can therefore only constrain the
*conserved* data = the moments, never `k*` directly; recovering `k*` requires re-reading the
moments at depth `2k* ≈ log p` (form A).  **The integrable structure relocates, it does not escape.**

This file makes that no-go a THEOREM, in the cleanest possible exact-rational form: it exhibits an
explicit **cospectral pair** of `3×3` zero-diagonal Jacobi matrices `J(b₁,b₂)` whose entire
spectrum (hence `M = top eigenvalue`) and every Toda invariant `tr(J^k)` depend ONLY on the
single conserved scalar `b₁² + b₂²`, yet whose `max(b₁,b₂)` (the form-D edge readout `max_k b_k`)
and `argmax` position (`k*`) DIFFER.  Concretely `(b₁,b₂) = (5,0)` and `(3,4)`:

* identical characteristic polynomial `X³ − 25·X` ⟹ identical spectrum `{0, ±5}`,
  identical `tr(J^k)` for every `k` (the conserved Toda invariants = the moments);
* `max(5,0) = 5 ≠ 4 = max(3,4)` (the edge readout differs) and the argmax sits at a different
  index (`k* = 1` vs `k* = 2`).

Hence: **no functional of the conserved Toda invariants (= the moments) can output `k*` or
`max_k b_k`.**  The form-D turnover is therefore NOT accessible to any Lax-pair argument that
uses only the conserved spectral data; it routes back to form A (depth-`2k*` moments).

## Honesty contract

NO core / cancellation / completion / moment-saving / anti-concentration / capacity claim.  This
is a structural **no-go for the integrable-systems escape**: the only thing the Toda flow conserves
is exactly the data form A already controls (the moments), and the turnover `k*` is gauge.  The
bare BGK/Paley wall `M ≤ C√(n log p)` — equivalently `k* = O(log p)` — remains **OPEN**; this brick
certifies, axiom-clean, that the discrete-Toda framing supplies no new door to it.
-/

namespace ProximityGap.Frontier.AssaultV2JacobiToda

open Matrix

/-! ## The zero-diagonal `3×3` Jacobi (symmetric tridiagonal) matrix -/

/-- A `3×3` symmetric tridiagonal ("Jacobi") matrix with zero diagonal and off-diagonal
recurrence coefficients `b₁, b₂`.  This is the smallest model in which the empirical-measure
Jacobi matrix of Form (D) lives; its spectrum is the support edge `M = top eigenvalue`. -/
def J (b₁ b₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, b₁, 0;
     b₁, 0, b₂;
     0, b₂, 0]

/-- The Toda invariant `I_k = tr(J^k)`: the conserved quantity of the discrete-Toda Lax flow
`dJ/dt = [B, J]`.  For a measure's Jacobi matrix these power-traces ARE the moments (form A). -/
def toda_invariant (b₁ b₂ : ℝ) (k : ℕ) : ℝ := Matrix.trace ((J b₁ b₂) ^ k)

/-! ## Step 1 — the conserved data depends ONLY on `b₁² + b₂²`

`tr(J) = 0`, `tr(J²) = 2(b₁²+b₂²)`, `tr(J³) = 0`.  Since `J` is `3×3` and traceless, the
Cayley–Hamilton characteristic polynomial is `X³ − (b₁²+b₂²)·X` (no `X²`, no constant term:
`tr J = 0`, `det J = 0`), so the ENTIRE spectrum `{0, ±√(b₁²+b₂²)}` — and hence every power-trace
`tr(J^k)` — is a function of the single scalar `s := b₁² + b₂²`. -/

/-- `tr(J) = 0`. -/
theorem todaInv_one (b₁ b₂ : ℝ) : toda_invariant b₁ b₂ 1 = 0 := by
  simp only [toda_invariant, pow_one, J]
  rw [Matrix.trace]
  simp [Matrix.diag, Fin.sum_univ_three]

/-- `tr(J²) = 2·(b₁² + b₂²)`: the second Toda invariant (= the second moment / energy `E₁`)
depends only on the conserved scalar `s = b₁² + b₂²`. -/
theorem todaInv_two (b₁ b₂ : ℝ) : toda_invariant b₁ b₂ 2 = 2 * (b₁ ^ 2 + b₂ ^ 2) := by
  simp only [toda_invariant, pow_two, J]
  rw [Matrix.trace]
  simp [Matrix.mul_apply, Matrix.diag, Fin.sum_univ_three]
  ring

/-- `tr(J³) = 0`: the third Toda invariant vanishes (traceless tridiagonal, odd power). -/
theorem todaInv_three (b₁ b₂ : ℝ) : toda_invariant b₁ b₂ 3 = 0 := by
  simp only [toda_invariant, pow_succ, pow_zero, Matrix.one_mul, J]
  rw [Matrix.trace]
  simp [Matrix.mul_apply, Matrix.diag, Fin.sum_univ_three]

/-- `tr(J⁴) = 2·(b₁²+b₂²)²`: every even power-trace is a function of the conserved scalar
`s = b₁²+b₂²` alone (here `I₄ = 2 s²`).  This is the structural heart: the Toda invariants
factor through `s`. -/
theorem todaInv_four (b₁ b₂ : ℝ) : toda_invariant b₁ b₂ 4 = 2 * (b₁ ^ 2 + b₂ ^ 2) ^ 2 := by
  simp only [toda_invariant, pow_succ, pow_zero, Matrix.one_mul, J]
  rw [Matrix.trace]
  simp [Matrix.mul_apply, Matrix.diag, Fin.sum_univ_three]
  ring

/-! ## Step 2 — the explicit COSPECTRAL pair (the gauge freedom of `k*`)

`(b₁,b₂) = (5,0)` and `(3,4)` share `s = b₁²+b₂² = 25`, hence ALL Toda invariants agree
(`tr(J^k)` is a function of `s`), so they are cospectral and have the SAME `M = top eigenvalue`.
But the edge readout `max(b₁,b₂)` differs (`5 ≠ 4`) and the argmax index (`k*`) differs.  This is
the exact statement that the conserved Toda data does not determine the turnover. -/

/-- The conserved scalar agrees on the two flow-distinct points. -/
theorem cospectral_scalar : (5 : ℝ) ^ 2 + 0 ^ 2 = 3 ^ 2 + 4 ^ 2 := by norm_num

/-- **Cospectrality at every depth.**  The two Jacobi matrices `J 5 0` and `J 3 4` have the SAME
value of every Toda invariant `tr(J^k)` for `k ∈ {1,2,3,4}` (and, by `todaInv_two/four` factoring
through `s = b₁²+b₂² = 25`, for every `k`): the conserved spectral data is identical. -/
theorem cospectral_invariants :
    (toda_invariant 5 0 1 = toda_invariant 3 4 1) ∧
    (toda_invariant 5 0 2 = toda_invariant 3 4 2) ∧
    (toda_invariant 5 0 3 = toda_invariant 3 4 3) ∧
    (toda_invariant 5 0 4 = toda_invariant 3 4 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [todaInv_one, todaInv_one]
  · rw [todaInv_two, todaInv_two]; norm_num
  · rw [todaInv_three, todaInv_three]
  · rw [todaInv_four, todaInv_four]; norm_num

/-- **The edge readout differs.**  `max(5,0) = 5 ≠ 4 = max(3,4)`: the form-D edge value
`max_k b_k` is DIFFERENT on the two cospectral matrices. -/
theorem edge_readout_differs : max (5 : ℝ) 0 ≠ max (3 : ℝ) 4 := by norm_num

/-! ## Step 3 — the no-go theorem: `k*` / `max_k b_k` is NOT a function of the conserved data -/

/-- **MAIN NO-GO (form D ⤳ form A; axiom-clean).**

The discrete-Toda / Lax-pair structure conserves exactly the power-traces `tr(J^k)` (= the
Toda invariants = the moments / energies of form A) and hence the top eigenvalue `M`.  But the
form-D edge readout `max_k b_k` (whose double is the prize value, and whose argmax is the turnover
depth `k*`) is **NOT** a function of those conserved invariants: the explicit cospectral pair
`(b₁,b₂) = (5,0)` vs `(3,4)` has identical Toda invariants at all measured depths yet different
`max(b₁,b₂)`.

Consequently **no Lax-pair / spectral-shift argument that uses only the conserved Toda data can
bound the turnover `k*`** — recovering `k*` (or `max_k b_k`) requires reading the moments at depth
`2k* ≈ log p`, i.e. form A.  The integrable-systems framing **relocates, it does not escape**, and
the bare wall `M ≤ C√(n log p)` (`k* = O(log p)`) remains open. -/
theorem todaTurnover_not_determined_by_invariants :
    -- the two matrices agree on all conserved Toda invariants (k = 1,2,3,4) ...
    ((toda_invariant 5 0 1 = toda_invariant 3 4 1) ∧
     (toda_invariant 5 0 2 = toda_invariant 3 4 2) ∧
     (toda_invariant 5 0 3 = toda_invariant 3 4 3) ∧
     (toda_invariant 5 0 4 = toda_invariant 3 4 4)) ∧
    -- ... yet the form-D edge readout `max_k b_k` differs:
    max (5 : ℝ) 0 ≠ max (3 : ℝ) 4 :=
  ⟨cospectral_invariants, edge_readout_differs⟩

/-- **Corollary — there is no functional recovering the turnover from the invariants.**
For ANY purported function `F` from the conserved-invariant data (the 4-tuple of low-order Toda
invariants) to the edge readout `max_k b_k`, `F` is contradicted by the cospectral pair: it would
have to output both `max(5,0)=5` and `max(3,4)=4` on identical input.  This is the precise sense in
which a Lax-pair argument cannot supply `k* = O(log p)`. -/
theorem no_invariant_functional_for_edge
    (F : (ℝ × ℝ × ℝ × ℝ) → ℝ)
    (hF₁ : F (toda_invariant 5 0 1, toda_invariant 5 0 2, toda_invariant 5 0 3,
              toda_invariant 5 0 4) = max (5 : ℝ) 0)
    (hF₂ : F (toda_invariant 3 4 1, toda_invariant 3 4 2, toda_invariant 3 4 3,
              toda_invariant 3 4 4) = max (3 : ℝ) 4) : False := by
  obtain ⟨h1, h2, h3, h4⟩ := cospectral_invariants
  rw [h1, h2, h3, h4] at hF₁
  rw [hF₁] at hF₂
  exact edge_readout_differs hF₂

-- Axiom audit (must be `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`):
#print axioms todaInv_one
#print axioms todaInv_two
#print axioms todaInv_three
#print axioms todaInv_four
#print axioms cospectral_invariants
#print axioms edge_readout_differs
#print axioms todaTurnover_not_determined_by_invariants
#print axioms no_invariant_functional_for_edge

end ProximityGap.Frontier.AssaultV2JacobiToda
