/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveredFractionEntropyListSize
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeJohnsonRadius
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeJohnsonRadiusSqrt
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSListDecoding

/-!
# General code entropy/rate covered fraction via the Johnson bound (#82)

The entropy/rate-form counterpart to `code_covered_count_johnson`, generalising
`rs_covered_count_johnson_entropy` to any code.  For any code `𝒞` with minimum distance `≥ d`
satisfying the Johnson conditions, every word has `≤ ℓ` close codewords
(`card_finset_le_of_johnson`), feeding the entropy-form second-moment covered fraction
(`covered_count_entropy_listSize`) to give

  `|𝒞| · q^{n·H_q(r/n)} ≤ (n+1) · |close| · ℓ`.

Specialising `hmin`/`d` to the Reed–Solomon minimum distance recovers
`rs_covered_count_johnson_entropy`.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **General code entropy/rate covered fraction via the Johnson bound (#82).** For any code `𝒞` with
minimum distance `≥ d` satisfying the Johnson conditions, `|𝒞|·q^{n·H_q(r/n)} ≤ (n+1)·|close|·ℓ`. -/
theorem code_covered_count_johnson_entropy (𝒞 : Finset (ι → F)) (r ℓ d : ℕ)
    (hqf : 2 ≤ Fintype.card F) (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - d : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    (𝒞.card : ℝ)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
          * (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * ℓ := by
  have hL : ∀ w : ι → F, closeCount 𝒞 r w ≤ ℓ := by
    intro w
    rw [closeCount]
    refine card_finset_le_of_johnson (d := d) hq1 hn w _ ℓ ?_ ?_ hP hsq
    · intro x hx; rw [Finset.mem_filter] at hx; rw [hammingDist_comm]; exact hx.2
    · intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      exact hmin x hx.1 y hy.1 hxy
  exact covered_count_entropy_listSize hqf 𝒞 r ℓ hr0 hrn hL hpos

/-- **Existential entropy-form covered fraction up to the Johnson radius (#232).**  The qualitative
Johnson-radius theorem supplies a list-size witness `ℓ`, and the entropy covered-fraction bound
uses that witness directly. -/
theorem code_covered_count_johnson_radius_entropy
    (hqf : 2 ≤ Fintype.card F) (𝒞 : Finset (ι → F)) (r d : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hradius :
      (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * (((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ∃ ℓ : ℕ,
      (𝒞.card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * ℓ := by
  obtain ⟨ℓ, hL⟩ := code_johnson_radius 𝒞 r d hq1 hn hmin hP hradius
  exact ⟨ℓ, covered_count_entropy_listSize hqf 𝒞 r ℓ hr0 hrn hL hpos⟩

/-- **Entropy covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook
`√(T·B) < A` condition supplies the list-size witness used by the entropy bound. -/
theorem code_covered_count_johnson_radius_sqrt_entropy
    (hqf : 2 ≤ Fintype.card F) (𝒞 : Finset (ι → F)) (r d : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hApos : 0 < ((Fintype.card ι - r : ℕ) : ℝ)
      - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hradius :
      Real.sqrt
          (((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
            * (((Fintype.card ι - d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
        < ((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ∃ ℓ : ℕ,
      (𝒞.card : ℝ)
          * (Fintype.card F : ℝ)
            ^ ((Fintype.card ι : ℝ)
              * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        ≤ ((Fintype.card ι : ℝ) + 1)
            * (univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card * ℓ := by
  obtain ⟨ℓ, hL⟩ := code_johnson_radius_sqrt 𝒞 r d hq1 hn hmin hP hApos hradius
  exact ⟨ℓ, covered_count_entropy_listSize hqf 𝒞 r ℓ hr0 hrn hL hpos⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.code_covered_count_johnson_entropy
#print axioms ArkLib.CS25.code_covered_count_johnson_radius_entropy
#print axioms ArkLib.CS25.code_covered_count_johnson_radius_sqrt_entropy
