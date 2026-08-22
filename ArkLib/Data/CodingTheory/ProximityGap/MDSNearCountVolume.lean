/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# MDS near-codeword count as a Hamming-ball volume (toward T4.17 far half, #82)

The RS near-codeword bound (`rs_near_codeword_count_le`) and the covered-fraction entropy bound
(`rs_covered_fraction_entropy`) carry the counting sum `∑_{d≤R} C(n,d)·q^d`. The genuine analytic
obstruction for the far/coverage half of the CS25 breakdown band inequality is bounding this sum by
a qEntropy exponential. This file supplies the bridge: the sum is *exactly* a Hamming-ball volume
over the alphabet `q+1`,

  `∑_{d≤R} C(n,d)·q^d = hammingBallVolume(q+1, R/n, n)`,

since `hammingBallVolume Q δ n = ∑_{i≤⌊δn⌋} C(n,i)·(Q−1)^i` with `Q = q+1`, `(Q−1) = q`, and
`⌊(R/n)·n⌋ = R`. Composing with `hammingBallVolume_le_qEntropy_real_radius` then bounds the near
count by `(n+1)·(q+1)^{n·H_{q+1}(R/n)}` — the missing input that turns the coverage *lower* bound
into the far *upper* bound `#{far}` small on the breakdown sub-band.
-/

namespace CodingTheory

/-- **MDS near-count sum = `(q+1)`-ary Hamming-ball volume.**
`∑_{d≤R} C(n,d)·q^d = hammingBallVolume(q+1, R/n, n)`. -/
theorem sum_choose_mul_pow_eq_hammingBallVolume (q n R : ℕ) (hn : 0 < n) :
    ∑ d ∈ Finset.range (R + 1), n.choose d * q ^ d
      = hammingBallVolume (q + 1) ((R : ℝ) / (n : ℝ)) n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold hammingBallVolume
  have heq : (R : ℝ) / (n : ℝ) * (n : ℝ) = (R : ℝ) := by field_simp
  have hfloor : ⌊(R : ℝ) / (n : ℝ) * (n : ℝ)⌋₊ = R := by rw [heq, Nat.floor_natCast]
  rw [hfloor]
  simp [Nat.add_sub_cancel]

/-- **MDS near-count qEntropy bound.** Below the `(q+1)`-ary capacity (`R/n ≤ 1 − 1/(q+1)`), the
near-codeword counting sum is bounded by the entropy exponential
`(n+1)·(q+1)^{n·H_{q+1}(R/n)}` — the far/coverage-half analytic input for the CS25 breakdown band
inequality. Composes `sum_choose_mul_pow_eq_hammingBallVolume` with
`hammingBallVolume_le_qEntropy_real_radius`. -/
theorem sum_choose_mul_pow_le_qEntropy (q n R : ℕ) (hn : 0 < n) (hq : 2 ≤ q + 1)
    (hcap : (R : ℝ) / (n : ℝ) ≤ 1 - 1 / ((q + 1 : ℕ) : ℝ)) :
    ((∑ d ∈ Finset.range (R + 1), n.choose d * q ^ d : ℕ) : ℝ)
      ≤ ((n : ℝ) + 1)
        * ((q + 1 : ℕ) : ℝ) ^ ((n : ℝ) * qEntropy (q + 1) ((R : ℝ) / (n : ℝ))) := by
  have hcast : ((∑ d ∈ Finset.range (R + 1), n.choose d * q ^ d : ℕ) : ℝ)
      = (hammingBallVolume (q + 1) ((R : ℝ) / (n : ℝ)) n : ℝ) :=
    congrArg (Nat.cast : ℕ → ℝ) (sum_choose_mul_pow_eq_hammingBallVolume q n R hn)
  rw [hcast]
  exact hammingBallVolume_le_qEntropy_real_radius hq ((R : ℝ) / (n : ℝ)) hn (by positivity) hcap

/-- **Truncated-exponent ≤ clean-exponent bridge.** The exact near-codeword counting sum carried by
`rs_covered_fraction_entropy`/`rs_near_codeword_count_le`, `∑_{d≤R} C(n,d)·q^{deg−(n−d)}`, is
term-wise below the clean `∑_{d≤R} C(n,d)·q^d` whenever `deg ≤ n` (since `deg−(n−d) ≤ d`). -/
theorem rs_near_count_le_sum_pow (q n deg R : ℕ) (hq : 1 ≤ q) (hdeg : deg ≤ n) :
    ∑ d ∈ Finset.range (R + 1), n.choose d * q ^ (deg - (n - d))
      ≤ ∑ d ∈ Finset.range (R + 1), n.choose d * q ^ d := by
  refine Finset.sum_le_sum (fun d _ => ?_)
  exact Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right hq (by omega))

/-- **RS near-codeword count qEntropy bound (exact form).** The MDS near-count sum in exactly the
shape used by `rs_covered_fraction_entropy` is bounded by `(n+1)·(q+1)^{n·H_{q+1}(R/n)}`. This is the
directly-pluggable far/coverage-half input: combined with the covered-fraction lower bound it gives
`#{close} ≥ |RS|·q^{n·H_q(δ)} / ((n+1)²·(q+1)^{n·H_{q+1}(2δ)})`. -/
theorem rs_near_count_le_qEntropy (q n deg R : ℕ) (hq1 : 1 ≤ q) (hdeg : deg ≤ n) (hn : 0 < n)
    (hq2 : 2 ≤ q + 1) (hcap : (R : ℝ) / (n : ℝ) ≤ 1 - 1 / ((q + 1 : ℕ) : ℝ)) :
    ((∑ d ∈ Finset.range (R + 1), n.choose d * q ^ (deg - (n - d)) : ℕ) : ℝ)
      ≤ ((n : ℝ) + 1)
        * ((q + 1 : ℕ) : ℝ) ^ ((n : ℝ) * qEntropy (q + 1) ((R : ℝ) / (n : ℝ))) := by
  refine le_trans ?_ (sum_choose_mul_pow_le_qEntropy q n R hn hq2 hcap)
  exact_mod_cast rs_near_count_le_sum_pow q n deg R hq1 hdeg

end CodingTheory
