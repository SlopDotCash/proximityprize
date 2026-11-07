/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentLinear
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallInterShell

/-!
# CS25 #82 — the sharp distance-dependent second moment (toward `ε_ca = 1`)

The covered-fraction half of the CS25 complete-CA breakdown needs a second-moment bound whose
per-pair term *decreases with the codeword weight*.  The loose `ballInterCount ≤ V`
(`sum_closeCount_sq_le`) makes the second moment as large as the first and provably **cannot** reach
the near-capacity covering threshold (the resulting covered-fraction condition
`H_q(δ) − H_2^q(2δ) − 2δ ≥ 0` is negative for large `q`).

This file composes the linear identity `∑_w (closeCount)² = |𝒞|·∑_{v∈𝒞} ballInterCount(r,v)`
(`sum_closeCount_sq_eq_card_mul`) with the shell containment
`ballInterCount(r,v) ≤ #{x : |x| ≤ r ∧ |v| ≤ |x|+r}` (`ballInterCount_le_shell`) into the sharp
second-moment bound whose inner term depends only on `|v|` (a Hamming shell `|v|−r ≤ |x| ≤ r`).
Grouping codewords by weight and feeding the MDS weight-enumerator count `A_w ≤ C(n,w)·q^{w−(n−k)}`
(`rs_near_codeword_count_le`) is intended to turn this into a `∑_w A_w · shell(w)` estimate whose
leading-order covered-fraction condition `H_2^q(2δ) − H_2^q(δ) + δ ≤ ρ` holds near capacity. That
grouping, the enumerator estimate and the asymptotic analysis are **not** carried out here; this
file proves only the shell inequality below.

The shell term is nonincreasing in `|v|` but only weakly: for `|v| ≤ r` the shell is the whole ball
`B(0,r)`, so the per-pair term equals `V`. The bound is strictly below `|𝒞|·|𝒞|·V` exactly when
some codeword has weight `> r`.
-/

open scoped BigOperators

namespace ArkLib.CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Sharp distance-dependent second moment.**  `∑_w (closeCount 𝒞 r w)² ≤ |𝒞| · ∑_{v∈𝒞} (shell of
`v`)`, where the shell `#{x : |x| ≤ r ∧ |v| ≤ |x|+r}` depends only on the codeword weight `|v|` and
thins to a sphere as `|v| → 2r`.  Never weaker than the loss-of-distance `ballInterCount ≤ V`
bound of `sum_closeCount_sq_le`, and strictly sharper only when some `v ∈ 𝒞` has `|v| > r` (for
`|v| ≤ r` the shell is the whole ball); intended as the input to the (not yet formalized)
MDS-weight covered-fraction estimate for the CS25 `ε_ca = 1` breakdown. -/
theorem sum_closeCount_sq_le_shell (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      ≤ 𝒞.card * ∑ v ∈ 𝒞,
          (Finset.univ.filter (fun x : ι → F =>
            hammingDist x 0 ≤ r ∧ hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)).card := by
  rw [sum_closeCount_sq_eq_card_mul 𝒞 r hsub hadd]
  exact Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun v _ => ballInterCount_le_shell r v))

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_closeCount_sq_le_shell
