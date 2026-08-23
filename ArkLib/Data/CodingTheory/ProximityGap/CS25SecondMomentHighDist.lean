/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentLinear
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallInterVanish

/-!
# CS25 second moment + covered fraction for high-distance linear codes (#82)

For a **linear** code `𝒞` (closed under `±`, containing `0`) whose minimum distance exceeds `2r`,
the second moment collapses **exactly** to `|𝒞| · |B(0,r)|` (each far codeword's two-ball
intersection vanishes), and the CS25 Paley-Zygmund inequality then yields the **covered-fraction
lower bound**

  `|{w : Δ₀(w, 𝒞) ≤ r}| ≥ |𝒞| · |B(0,r)|`,

i.e. in the high-distance regime there is no variance loss: the covered set is at least the
first-moment count.  This is the favorable case of the CS25 covered-fraction / `ε_ca` argument.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Weight-enumerator sum collapse (high distance).**  If `0 ∈ 𝒞` and every nonzero codeword is
`> 2r` from the origin, then `∑_{v∈𝒞} ballInterCount r v = ballInterCount r (0 : ι → F)` (only
`v = 0` survives, by `ballInterCount_eq_zero_of_lt`). -/
theorem sum_ballInterCount_eq_of_minDist (𝒞 : Finset (ι → F)) (r : ℕ)
    (h0 : (0 : ι → F) ∈ 𝒞)
    (hd : ∀ v ∈ 𝒞, v ≠ 0 → 2 * r < hammingDist (0 : ι → F) v) :
    ∑ v ∈ 𝒞, ballInterCount r v = ballInterCount r (0 : ι → F) := by
  refine Finset.sum_eq_single (0 : ι → F) (fun v hv hv0 => ?_) (fun h => absurd h0 h)
  exact ballInterCount_eq_zero_of_lt r v (hd v hv hv0)

/-- **Exact second moment, high-distance linear code.**  For a linear code `𝒞` with minimum
distance `> 2r`, `∑_w (closeCount 𝒞 r w)² = |𝒞| · |B(0,r)|` — the variance-free second moment. -/
theorem sum_closeCount_sq_high_dist (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (h0 : (0 : ι → F) ∈ 𝒞)
    (hd : ∀ v ∈ 𝒞, v ≠ 0 → 2 * r < hammingDist (0 : ι → F) v) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2) = 𝒞.card * ballInterCount r (0 : ι → F) := by
  rw [sum_closeCount_sq_eq_card_mul 𝒞 r hsub hadd, sum_ballInterCount_eq_of_minDist 𝒞 r h0 hd]

/-- `ballInterCount r 0` is the Hamming ball volume `|B(0,r)|` (the `v = 0` two-ball intersection is
the ball itself). -/
theorem ballInterCount_zero_eq (r : ℕ) :
    ballInterCount r (0 : ι → F)
      = (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
  unfold ballInterCount
  congr 1
  ext x
  simp

/-- **Covered-fraction lower bound (high-distance linear code).**  Combining the exact second moment
with the CS25 Paley-Zygmund inequality, the covered set is at least the first-moment count:
`|𝒞| · |B(0,r)| ≤ |{w : closeCount 𝒞 r w ≠ 0}|` (no variance loss), provided `|𝒞|·V > 0`.  The
favorable regime of the CS25 covered-fraction / `ε_ca` bound. -/
theorem card_close_ge_card_mul_vol (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (h0 : (0 : ι → F) ∈ 𝒞)
    (hd : ∀ v ∈ 𝒞, v ≠ 0 → 2 * r < hammingDist (0 : ι → F) v)
    (hpos : 0 < 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card := by
  have hpz := sq_card_mul_volume_le_card_close_mul_sum_sq 𝒞 r
  rw [sum_closeCount_sq_high_dist 𝒞 r hsub hadd h0 hd, ballInterCount_zero_eq, sq] at hpz
  exact Nat.le_of_mul_le_mul_right hpz hpos

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_ballInterCount_eq_of_minDist
#print axioms ArkLib.CS25.sum_closeCount_sq_high_dist
#print axioms ArkLib.CS25.ballInterCount_zero_eq
#print axioms ArkLib.CS25.card_close_ge_card_mul_vol
