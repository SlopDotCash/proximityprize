/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GVCounting
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# Entropy-form Gilbert–Varshamov bound

Dual to the entropy sphere-packing bound.  Combining the covering bound `qⁿ ≤ |𝒞| · Vol_q(δ,n)`
(`card_le_card_mul_hammingBallVolume_of_covering`, e.g. for a maximal/covering code) with the entropy
upper bound on the ball volume `Vol_q(δ,n) ≤ (n+1)·q^{n·H_q(⌊δn⌋/n)}` (`hammingBallVolume_le_qEntropy`)
gives the **entropy-rate form** of the Gilbert–Varshamov bound:

  `q^{n·(1 − H_q(⌊δn⌋/n))} ≤ (n+1) · |𝒞|`,

i.e. a covering code has size `|𝒞| ≥ q^{n(1−H_q(δ))}/(n+1)` — rate `≳ 1 − H_q(δ)`.  Together with the
entropy Hamming bound this brackets the achievable rate around `1 − H_q(δ)`.
-/

namespace CodingTheory

open Real

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Entropy-form Gilbert–Varshamov bound.**  A covering code `𝒞` over `F` (`q = |F| ≥ 2`,
`n = |ι|`, with `⌊δn⌋/n ≤ 1 − 1/q`) has `q^{n(1 − H_q(⌊δn⌋/n))} ≤ (n+1)·|𝒞|`, i.e. size at least
`q^{n(1−H_q(δ))}/(n+1)`. -/
theorem card_ge_qEntropy_of_covering (hq : 2 ≤ Fintype.card F) (C : Finset (ι → F)) (δ : ℝ)
    (hr : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hcap : (⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ) ≤ 1 - 1 / (Fintype.card F : ℝ))
    (hcover : ∀ x : ι → F, ∃ c ∈ C, x ∈ ListDecodable.hammingBall c ⌊δ * Fintype.card ι⌋₊) :
    (Fintype.card F : ℝ)
        ^ ((Fintype.card ι : ℝ)
            * (1 - qEntropy (Fintype.card F)
                ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ))))
      ≤ ((Fintype.card ι : ℝ) + 1) * (C.card : ℝ) := by
  set q := Fintype.card F with hq_def
  set n := Fintype.card ι with hn_def
  set H := qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) with hH
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hcov := card_le_card_mul_hammingBallVolume_of_covering C δ hcover
  have hub := hammingBallVolume_le_qEntropy hq δ hr hcap
  have hcard_eq : (Fintype.card (ι → F) : ℝ) = (q : ℝ) ^ (n : ℝ) := by
    rw [Fintype.card_fun, Nat.cast_pow, Real.rpow_natCast]
  have hcov' : (q : ℝ) ^ (n : ℝ) ≤ (C.card : ℝ) * (hammingBallVolume q δ n : ℝ) := by
    rw [← hcard_eq]; exact_mod_cast hcov
  have key : (q : ℝ) ^ (n : ℝ) ≤ ((n : ℝ) + 1) * (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H) := by
    calc (q : ℝ) ^ (n : ℝ)
        ≤ (C.card : ℝ) * (hammingBallVolume q δ n : ℝ) := hcov'
      _ ≤ (C.card : ℝ) * (((n : ℝ) + 1) * (q : ℝ) ^ ((n : ℝ) * H)) :=
          mul_le_mul_of_nonneg_left hub (Nat.cast_nonneg _)
      _ = ((n : ℝ) + 1) * (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H) := by ring
  rw [show (n : ℝ) * (1 - H) = (n : ℝ) - (n : ℝ) * H by ring, Real.rpow_sub hq0,
    div_le_iff₀ (Real.rpow_pos_of_pos hq0 _)]
  exact key

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.card_ge_qEntropy_of_covering
