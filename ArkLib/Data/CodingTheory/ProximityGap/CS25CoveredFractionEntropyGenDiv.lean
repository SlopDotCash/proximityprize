/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionEntropyGen

/-!
# Entropy-form covered fraction, general linear code — division form (#82)

The directly interpretable lower-bound form of `covered_fraction_entropy_general`: for any linear
code `𝒞` with a nonempty near-set, the covered set satisfies

  `|𝒞| · q^{n·H_q(r/n)} / ((n+1) · |near|) ≤ |close|`.

This completes the covered-fraction theory in all four shapes: {RS, general} × {product, division}.
-/

namespace ArkLib.CS25

open scoped BigOperators
open CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Entropy-form covered fraction ≥ bound (general linear code, division form, #82).**
`|𝒞|·q^{n·H_q(r/n)} / ((n+1)·|near|) ≤ |close|`, for a code `𝒞` closed under `±` with `|near| > 0`. -/
theorem covered_fraction_entropy_general_div (hq : 2 ≤ Fintype.card F) (𝒞 : Finset (ι → F)) (r : ℕ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞) (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞)
    (hpos : 0 < 𝒞.card * (Finset.univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card)
    (hnear : 0 < (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card) :
    (𝒞.card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1)
            * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card)
      ≤ (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card := by
  have hnear' : (0 : ℝ) < ((𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card : ℝ) := by
    exact_mod_cast hnear
  rw [div_le_iff₀ (by positivity)]
  have h := covered_fraction_entropy_general hq 𝒞 r hr0 hrn hsub hadd hpos
  calc (𝒞.card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
            * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card := h
      _ = (Finset.univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card
            * (((Fintype.card ι : ℝ) + 1)
              * (𝒞.filter (fun v => hammingDist (0 : ι → F) v ≤ 2 * r)).card) := by ring

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.covered_fraction_entropy_general_div
