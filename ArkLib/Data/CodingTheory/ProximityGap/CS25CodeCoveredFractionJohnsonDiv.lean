/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeCoveredFractionJohnson

/-!
# Covered fraction, interpretable division form (#82)

The directly interpretable conclusion of the Johnson-regime covered-fraction bound
`code_covered_count_johnson` (`|𝒞|·V ≤ |close|·ℓ`): dividing by the list-size bound `ℓ > 0`,

  `|𝒞|·V / ℓ ≤ |close|`,

i.e. the covered set is large — at least a `1/ℓ` fraction of the volume-`V` ball mass around the code
is covered.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **General code covered fraction, interpretable division form (#82).** In the Johnson regime the
covered set is large: `|𝒞|·V / ℓ ≤ |close|`. -/
theorem code_covered_fraction_johnson_div {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]
    (𝒞 : Finset (ι → F)) (r ℓ d : ℕ)
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι) (hℓ : 0 < ℓ)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c')
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - d : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpos : 0 < 𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ((𝒞.card * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card : ℕ) : ℝ) / (ℓ : ℝ)
      ≤ ((univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card : ℝ) := by
  have hbase := code_covered_count_johnson 𝒞 r ℓ d hq1 hn hmin hP hsq hpos
  have hℓr : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  rw [div_le_iff₀ hℓr]
  exact_mod_cast hbase

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.code_covered_fraction_johnson_div
