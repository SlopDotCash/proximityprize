/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallEntropy
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFraction

/-!
# Entropy-form CS25 covered fraction for general linear codes (#82)

The general-linear-code analogue of `rs_covered_fraction_entropy`: combining the general covered
fraction `card_close_mul_near_ge` (`|𝒞|·V ≤ |close|·|near|`) with the entropy ball bound
(`filter_ball_card_ge_qEntropy`: `q^{n·H_q(r/n)} ≤ (n+1)·V`) gives, for *any* linear code `𝒞`,

  `|𝒞| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · |near|`,

where `near = {v ∈ 𝒞 : Δ₀(0,v) ≤ 2r}`.  (RS specializes this with the explicit MDS bound on `|near|`.)
-/

namespace ArkLib.CS25

open scoped BigOperators
open CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Entropy-form covered fraction, general linear code (#82).**  For a code `𝒞` closed under `±`
(`q = |F| ≥ 2`, `n = |ι|`, `0 < r < n`, `|𝒞|·V > 0`):
`|𝒞| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · |near|`. -/
theorem covered_fraction_entropy_general (hq : 2 ≤ Fintype.card F) (𝒞 : Finset (ι → F)) (r : ℕ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞) (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (hpos : 0 < 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (𝒞.card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
          * (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
          * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := by
  have hball := filter_ball_card_ge_qEntropy hq r hr0 hrn
  have hVeq : (Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card
      = (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card := by
    congr 1; ext w; simp only [Finset.mem_filter, hammingDist_comm]
  rw [hVeq] at hball
  have hcov' : (𝒞.card : ℝ)
        * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
          * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := by
    exact_mod_cast card_close_mul_near_ge 𝒞 r hsub hadd hpos
  calc (𝒞.card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ (𝒞.card : ℝ)
            * (((Fintype.card ι : ℝ) + 1)
              * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :=
          mul_le_mul_of_nonneg_left hball (Nat.cast_nonneg _)
      _ = ((Fintype.card ι : ℝ) + 1)
            * ((𝒞.card : ℝ)
              * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) := by ring
      _ ≤ ((Fintype.card ι : ℝ) + 1)
            * ((Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
              * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card) :=
          mul_le_mul_of_nonneg_left hcov' (by positivity)
      _ = ((Fintype.card ι : ℝ) + 1)
            * (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
            * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := by ring

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.covered_fraction_entropy_general
