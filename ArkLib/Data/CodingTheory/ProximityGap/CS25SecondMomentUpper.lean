/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentLinear
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallInterVanish

/-!
# CS25 second moment — general upper bound (#82)

For an arbitrary linear code `𝒞`, the second moment is bounded by the number of *near* codewords
(weight `≤ 2r`) times the ball volume — no monomial-invariant `I(d)` combinatorics required, only
the two facts that far codewords contribute nothing (`ballInterCount_eq_zero_of_lt`) and that every
two-ball intersection is at most the single ball (`ballInterCount_le`):

  `∑_{v∈𝒞} |B(0,r)∩B(v,r)| ≤ |{v∈𝒞 : Δ₀(0,v) ≤ 2r}| · |B(0,r)|`,

hence `∑_w (closeCount 𝒞 r w)² ≤ |𝒞| · |{near codewords}| · |B(0,r)|`.  When the code has few near
codewords (high distance / sub-`2r` band), this controls the variance for the CS25 covered fraction.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Two-ball intersection ≤ single-ball volume.**  `|B(0,r) ∩ B(v,r)| ≤ |B(0,r)| = ballInterCount
r 0`, since the intersection imposes the extra constraint `Δ₀(x,v) ≤ r`. -/
theorem ballInterCount_le (r : ℕ) (v : ι → F) :
    ballInterCount r v ≤ ballInterCount r (0 : ι → F) := by
  unfold ballInterCount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.1⟩

/-- **Weight-enumerator sum bounded by near-codeword count.**  Far codewords (weight `> 2r`) drop
out and the rest are each `≤ |B(0,r)|`:
`∑_{v∈𝒞} ballInterCount r v ≤ |{v∈𝒞 : Δ₀(0,v) ≤ 2r}| · ballInterCount r 0`. -/
theorem sum_ballInterCount_le (𝒞 : Finset (ι → F)) (r : ℕ) :
    ∑ v ∈ 𝒞, ballInterCount r v
      ≤ (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card
          * ballInterCount r (0 : ι → F) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not 𝒞 (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)]
  have hzero :
      ∑ v ∈ 𝒞.filter (fun v => ¬ hammingDist (0 : ι → F) v ≤ 2 * r), ballInterCount r v = 0 := by
    refine Finset.sum_eq_zero (fun v hv => ?_)
    rw [Finset.mem_filter] at hv
    exact ballInterCount_eq_zero_of_lt r v (not_le.mp hv.2)
  rw [hzero, add_zero]
  calc ∑ v ∈ 𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r), ballInterCount r v
      ≤ ∑ _v ∈ 𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r),
          ballInterCount r (0 : ι → F) := Finset.sum_le_sum (fun v _ => ballInterCount_le r v)
    _ = (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card
          * ballInterCount r (0 : ι → F) := by rw [Finset.sum_const, smul_eq_mul]

/-- **General second-moment upper bound (linear code).**  `∑_w (closeCount 𝒞 r w)² ≤ |𝒞| ·
|{near codewords}| · |B(0,r)|`.  Composes the linear reduction with `sum_ballInterCount_le`. -/
theorem sum_closeCount_sq_le (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      ≤ 𝒞.card * ((𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card
          * ballInterCount r (0 : ι → F)) := by
  rw [sum_closeCount_sq_eq_card_mul 𝒞 r hsub hadd]
  exact Nat.mul_le_mul_left _ (sum_ballInterCount_le 𝒞 r)

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.ballInterCount_le
#print axioms ArkLib.CS25.sum_ballInterCount_le
#print axioms ArkLib.CS25.sum_closeCount_sq_le
