/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentPairCount

/-!
# CS25 second moment — far codewords contribute nothing (#82)

The two-ball intersection volume `ballInterCount r v = |B(0,r) ∩ B(v,r)|` **vanishes** once the
codeword `v` is farther than `2r` from the origin: a point within Hamming distance `r` of both `0`
and `v` would force `Δ₀(0,v) ≤ 2r` by the triangle inequality.

This is the key sharpening for the CS25 second moment of a high-distance (MDS) code: since every
nonzero codeword has weight `≥ d_min`, if `d_min > 2r` then `∑_{v ∈ 𝒞} ballInterCount r v` collapses
to the single `v = 0` term `|B(0,r)|`, so `E[N²] = |𝒞| · |B(0,r)|` — matching `E[N]` up to the
`|𝒞|/q^n` factor and giving the Paley-Zygmund covered-fraction bound.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Far codewords give empty two-ball intersection.**  If `2r < Δ₀(0, v)` then no point is within
distance `r` of both `0` and `v` (triangle inequality), so `ballInterCount r v = 0`. -/
theorem ballInterCount_eq_zero_of_lt (r : ℕ) (v : ι → F)
    (h : 2 * r < hammingDist (0 : ι → F) v) :
    ballInterCount r v = 0 := by
  unfold ballInterCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x _ ⟨hx0, hxv⟩
  have htri : hammingDist (0 : ι → F) v
      ≤ hammingDist (0 : ι → F) x + hammingDist x v := hammingDist_triangle _ _ _
  rw [hammingDist_comm (0 : ι → F) x] at htri
  omega

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.ballInterCount_eq_zero_of_lt
