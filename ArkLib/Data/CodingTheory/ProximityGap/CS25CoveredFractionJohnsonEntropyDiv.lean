/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CodeCoveredFractionJohnsonEntropy
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSCoveredFractionJohnsonEntropy

/-!
# Rate-form covered fraction, interpretable division statements (#82)

The directly interpretable rate-form conclusions of the Johnson-regime covered fraction (the form
used in the proximity-gap literature): dividing `|𝒞|·q^{n·H_q(r/n)} ≤ (n+1)·|close|·ℓ` by
`(n+1)·ℓ > 0` gives

  `|𝒞| · q^{n·H_q(r/n)} / ((n+1)·ℓ) ≤ |close|`,

for both general codes (`code_covered_fraction_johnson_entropy_div`) and Reed–Solomon
(`rs_covered_fraction_johnson_entropy_div`) — the covered set occupies at least a
`q^{nH}/((n+1)ℓ)` share.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **General code rate covered fraction, division form (#82).** `|𝒞|·q^{nH}/((n+1)·ℓ) ≤ |close|`. -/
theorem code_covered_fraction_johnson_entropy_div {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F]
    (𝒞 : Finset (ι → F)) (r ℓ d : ℕ)
    (hqf : 2 ≤ Fintype.card F) (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι) (hℓ : 0 < ℓ)
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
        * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1) * (ℓ : ℝ))
      ≤ ((univ.filter (fun w : ι → F => closeCount 𝒞 r w ≠ 0)).card : ℝ) := by
  have hbase := code_covered_count_johnson_entropy 𝒞 r ℓ d hqf hq1 hn hr0 hrn hmin hP hsq hpos
  have hden : (0 : ℝ) < ((Fintype.card ι : ℝ) + 1) * (ℓ : ℝ) := by
    have : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast hℓ
    positivity
  rw [div_le_iff₀ hden]; nlinarith [hbase]

/-- **Reed–Solomon rate covered fraction, division form (#82).** `|RS|·q^{nH}/((n+1)·ℓ) ≤ |close|`. -/
theorem rs_covered_fraction_johnson_entropy_div {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) [NeZero k] (r ℓ : ℕ)
    (hqf : 2 ≤ Fintype.card F) (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι) (hℓ : 0 < ℓ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - r : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - r : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpos : 0 < (rsCodeFinset domain k).card
        * (univ.filter (fun w : ι → F => hammingDist w 0 ≤ r)).card) :
    ((rsCodeFinset domain k).card : ℝ)
        * (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
        / (((Fintype.card ι : ℝ) + 1) * (ℓ : ℝ))
      ≤ ((univ.filter (fun w : ι → F => closeCount (rsCodeFinset domain k) r w ≠ 0)).card : ℝ) := by
  have hbase := rs_covered_count_johnson_entropy domain k r ℓ hqf hq1 hn hr0 hrn hP hsq hpos
  have hden : (0 : ℝ) < ((Fintype.card ι : ℝ) + 1) * (ℓ : ℝ) := by
    have : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast hℓ
    positivity
  rw [div_le_iff₀ hden]; nlinarith [hbase]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.code_covered_fraction_johnson_entropy_div
#print axioms ArkLib.CS25.rs_covered_fraction_johnson_entropy_div
