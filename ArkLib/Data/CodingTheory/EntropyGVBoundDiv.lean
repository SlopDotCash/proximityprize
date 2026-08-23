/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyGVBound

/-!
# Entropy Gilbert–Varshamov bound — division (lower-bound) form

The directly interpretable form of `card_ge_qEntropy_of_covering`: a covering code has size at least
`q^{n·(1−H_q(⌊δn⌋/n))} / (n+1)`.
-/

namespace CodingTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Entropy GV bound, division form:** a covering code over `F` (`q = |F| ≥ 2`) has
`q^{n·(1−H_q(⌊δn⌋/n))} / (n+1) ≤ |C|`. -/
theorem card_ge_qEntropy_of_covering_div (hq : 2 ≤ Fintype.card F) (C : Finset (ι → F)) (δ : ℝ)
    (hr : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hcap : (⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ))
    (hcover : ∀ x : ι → F, ∃ c ∈ C, x ∈ ListDecodable.hammingBall c ⌊δ * Fintype.card ι⌋₊) :
    (Fintype.card F : ℝ)
        ^ ((Fintype.card ι : ℝ)
            * (1 - qEntropy (Fintype.card F)
                ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))))
        / ((Fintype.card ι : ℝ) + 1)
      ≤ (C.card : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h := card_ge_qEntropy_of_covering hq C δ hr hcap hcover
  linarith [h]

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.card_ge_qEntropy_of_covering_div
