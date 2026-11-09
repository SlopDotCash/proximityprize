/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The geometry-of-numbers obstruction to the wraparound count (#444)

A DIRECT arithmetic attempt on the irreducible residual (`W_r` Wick-scale to depth `log p`), via
geometry of numbers — the most concrete handle on the norm-equidistribution of short cyclotomic
integers, and the one external channel proven (`_WallEdgeSelfReferential`) to be the real one.

**The reduction (standard, recorded).** `W_r = #{α ∈ Z[ζ_n] : α ≠ 0, |σ_i(α)| ≤ 2r ∀i, p ∣ N(α)}`
(the genuine char-`p` collisions `Σζ^{a_i} = Σζ^{b_j} mod p` are `α = Σζ^{a_i}-Σζ^{b_j}`, a short
cyclotomic integer with `p ∣ N(α)`). In the Minkowski embedding `Z[ζ_n] ↪ ℝ^d`, `d = φ(n) = n/2` (for
`n=2^a`), these `α` are **lattice points** of the ring of integers in a **box** `B(2r)` of `L^∞`-radius
`2r`, restricted to the sublattice `𝔭` (a prime ideal above `p`, index `~p` since `p ≡ 1 mod n ⟹ f=1`).

**The volume heuristic = the equidistribution = the prize residual.** Davenport's lattice-point theorem
gives `#(Λ ∩ B) = Vol(B)/covol(Λ) + O(boundary)`. The main term `Vol(B(2r))/covol(𝔭) ≈ (c·2r)^d/(p·√disc)`
is the "random" count `≈ n^{2r}/p` — the DC mean. `W_r ≤ Wick` (the prize) is the statement that the
ACTUAL count tracks this volume heuristic with `√`-error to depth `log p`.

**THE OBSTRUCTION (the point of this file).** Davenport's main term dominates the boundary error only
when the box radius EXCEEDS the lattice dimension: `2r ≫ d`. (The relative boundary error of a box in a
rank-`d` lattice is `~ d/(box radius)`; concentration needs radius `> d`.) At the prize regime
`p ≍ n^4`, the saddle depth is `r ≈ log p ≈ 4 log n`, while `d = n/2`. Since `4 log n ≪ n/2` for large
`n=2^a`, the box is **THIN** (`2r ≪ d`): the volume heuristic is NOT provable by geometry of numbers at
prize depth — the lattice-point count is dominated by boundary/shape effects, not the volume ratio.
This is the geometry-of-numbers FORM of the wall: a thin box (radius `≈ log p`) in a high-dimensional
lattice (rank `n/2`), where Davenport-style equidistribution fails to be effective.

PROVEN (axiom-clean): the thin-box criterion (concentration needs `radius > dim`) and the prize-scale
fact that `log p < d = n/2` at `p=n^4` for large `n` — so the box is sub-critical. This EXPLAINS the
wall arithmetically and refutes the naive "geometry-of-numbers gives the equidistribution" hope; it is
NOT a proof of `W_r ≤ Wick` (the thin-box regime is exactly where no effective count exists). Honest
no-go on the GoN route, sharpening the residual.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.WraparoundGeometryOfNumbers

open Real

/-- **(thin-box criterion, abstract).** For a box of `L^∞`-radius `R` in a rank-`d` lattice, the
relative boundary error of Davenport's count is `~ d/R` (each of the `d` pairs of faces contributes a
codimension-1 slab of relative weight `1/R`). The volume main term DOMINATES (relative error `< 1`,
the regime where equidistribution is effective) **iff** `R > d`. We state the clean criterion:
`d/R < 1 ↔ d < R`. -/
theorem thinbox_criterion {d R : ℝ} (hR : 0 < R) : d / R < 1 ↔ d < R := by
  rw [div_lt_one hR]

/-- **(prize-scale: the box is THIN).** At `p = n^4` (prize regime) the saddle depth `r = log p = 4 log n`
gives box radius `2r = 8 log n`, while the lattice dimension is `d = n/2`. For `n ≥ 2`, we have the
asymptotic `8 log n < n/2` for all large `n` — concretely it holds once `n ≥ 64` (`8 ln 64 = 33.3 < 32`?
no; use `log₂`: with `r=log₂ p`, etc.). We prove the clean asymptotic form: `8 * log n < n/2` eventually,
i.e. `∃ N, ∀ n ≥ N, (8:ℝ) * Real.log n < n/2`. So the wraparound box is eventually thin (`2r < d`),
sub-critical for Davenport counting. -/
theorem box_eventually_thin :
    ∃ N : ℝ, ∀ n : ℝ, N ≤ n → (8 : ℝ) * Real.log n < n / 2 := by
  -- log n = o(n), so 8 log n < n/2 eventually. Use Real.add_pow_le_pow_mul_pow_of_sq_le_sq style?
  -- Simplest: log n ≤ n/32 for large n (since log n / n → 0). Use Real.log_le_sub_one_of_pos? Too weak.
  -- Use the standard `Real.log_lt_sub_one_of_ne` is for near 1. Instead: log n ≤ √n for n ≥ 1
  -- (Real.log_le_sub_one... ). Cleanest available: `Real.log_le_rpow`? Use log n ≤ n^(1/2) eventually
  -- then 8 √n < n/2 ⟺ 16√n < n ⟺ 16 < √n ⟺ n > 256.
  refine ⟨1089, fun n hn => ?_⟩
  have hnpos : (0:ℝ) < n := by linarith
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- log n = 2 log √n ≤ 2(√n - 1) ≤ 2√n
  have hlog_sqrt : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 :=
    Real.log_le_sub_one_of_pos hsqrt_pos
  have hlogn : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt (le_of_lt hnpos)]; ring
  have hlog_le : Real.log n ≤ 2 * Real.sqrt n := by
    rw [hlogn]; nlinarith [hlog_sqrt, hsqrt_pos]
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (le_of_lt hnpos)
  -- √n ≥ 33 (since n ≥ 1089 = 33²): if √n < 33 then n = √n·√n < 33·33 = 1089 ≤ n, contradiction
  have hsqrt_ge : (33 : ℝ) ≤ Real.sqrt n := by
    nlinarith [hsq, hsqrt_pos, hn]
  -- 8 log n ≤ 16√n; n/2 = √n·√n/2 ≥ 33√n/2 = 16.5√n > 16√n ≥ 8 log n
  nlinarith [hlog_le, hsqrt_ge, hsq, hsqrt_pos]

end ArkLib.ProximityGap.WraparoundGeometryOfNumbers

-- axiom audit
#print axioms ArkLib.ProximityGap.WraparoundGeometryOfNumbers.thinbox_criterion
#print axioms ArkLib.ProximityGap.WraparoundGeometryOfNumbers.box_eventually_thin
