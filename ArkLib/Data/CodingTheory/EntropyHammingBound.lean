/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBound
import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Entropy-form sphere-packing (Hamming) bound

Combining the raw sphere-packing bound `|𝒞| · Vol_q(δ,n) ≤ qⁿ`
(`card_mul_hammingBallVolume_le_of_minDist`) with the entropy lower bound on the ball volume
`q^{n·H_q(⌊δn⌋/n)} ≤ (n+1)·Vol_q(δ,n)` (`hammingBallVolume_ge_qEntropy`) gives the **entropy-rate
form** of the Hamming bound:

  `|𝒞| ≤ (n+1) · q^{n·(1 − H_q(⌊δn⌋/n))}`.

For a code of minimum distance `> 2⌊δn⌋`, this caps the size — equivalently the rate
`log_q|𝒞| / n ≲ 1 − H_q(δ)` — the classical entropy sphere-packing / rate bound, now assembled from
the in-tree pieces.
-/

namespace CodingTheory

open Real

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Entropy-form sphere-packing bound.**  A code `𝒞` over `F` (`q = |F| ≥ 2`, `n = |ι|`) with
pairwise distance `> 2⌊δn⌋` has size at most `(n+1)·q^{n(1−H_q(⌊δn⌋/n))}`. -/
theorem card_le_qEntropy_of_minDist (hq : 2 ≤ Fintype.card F) (C : Finset (ι → F)) (δ : ℝ)
    (hk0 : 0 < ⌊δ * Fintype.card ι⌋₊) (hkn : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hpack : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      2 * ⌊δ * Fintype.card ι⌋₊ + 1 ≤ hammingDist c c') :
    (C.card : ℝ) ≤ ((Fintype.card ι : ℝ) + 1)
        * (Fintype.card F : ℝ)
          ^ ((Fintype.card ι : ℝ)
              * (1 - qEntropy (Fintype.card F)
                  ((⌊δ * Fintype.card ι⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) := by
  set q := Fintype.card F with hq_def
  set n := Fintype.card ι with hn_def
  set H := qEntropy q ((⌊δ * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) with hH
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hsp := card_mul_hammingBallVolume_le_of_minDist C δ hpack
  have hvol := hammingBallVolume_ge_qEntropy hq δ n hk0 hkn
  have hcard_eq : (Fintype.card (ι → F) : ℝ) = (q : ℝ) ^ (n : ℝ) := by
    rw [Fintype.card_fun, Nat.cast_pow, Real.rpow_natCast]
  have hsp' : (C.card : ℝ) * (hammingBallVolume q δ n : ℝ) ≤ (q : ℝ) ^ (n : ℝ) := by
    rw [← hcard_eq]; exact_mod_cast hsp
  have key : (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H) ≤ ((n : ℝ) + 1) * (q : ℝ) ^ (n : ℝ) := by
    calc (C.card : ℝ) * (q : ℝ) ^ ((n : ℝ) * H)
        ≤ (C.card : ℝ) * (((n : ℝ) + 1) * (hammingBallVolume q δ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg _)
      _ = ((n : ℝ) + 1) * ((C.card : ℝ) * (hammingBallVolume q δ n : ℝ)) := by ring
      _ ≤ ((n : ℝ) + 1) * (q : ℝ) ^ (n : ℝ) :=
          mul_le_mul_of_nonneg_left hsp' (by positivity)
  rw [show (n : ℝ) * (1 - H) = (n : ℝ) - (n : ℝ) * H by ring, Real.rpow_sub hq0,
    ← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos hq0 _)]
  exact key

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.card_le_qEntropy_of_minDist
