/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Entropy lower bound on the Hamming ball cardinality

The radius-`r` Hamming ball (`ListDecodable.hammingBall`) is exactly `Vol_q(r/n, n)`
(`hammingBallVolume_eq_ncard_hammingBall`), so the entropy estimate `q^{n·H_q(r/n)} ≤ (n+1)·Vol`
(`hammingBallVolume_ge_qEntropy`) gives directly

  `q^{n·H_q(r/n)} ≤ (n+1) · |B(0,r)|`.

This is the entropy (rate) lower bound on the ball size in the `ncard` convention used throughout the
list-decoding development — the standard ingredient for covered-fraction / list-decoding rate
estimates.  `sorry`/`axiom`-free.
-/

namespace CodingTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [Zero F]

/-- **Entropy lower bound on the Hamming ball** (`q = |F| ≥ 2`, `n = |ι|`, `0 < r < n`):
`q^{n·H_q(r/n)} ≤ (n+1)·|B(0,r)|`, where `|B(0,r)| = (hammingBall 0 r).ncard`.  The ball is exactly
`Vol_q(r/n,n)`, to which `hammingBallVolume_ge_qEntropy` applies. -/
theorem hammingBall_ncard_ge_qEntropy (hq : 2 ≤ Fintype.card F) (r : ℕ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι) :
    (Fintype.card F : ℝ)
        ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
        * ((ListDecodable.hammingBall (0 : ι → F) r).ncard : ℝ) := by
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := lt_trans hr0 hrn
  have hfloor : ⌊(r : ℝ) / (n : ℝ) * (n : ℝ)⌋₊ = r := by
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)]; exact Nat.floor_natCast r
  have heq : (ListDecodable.hammingBall (0 : ι → F) r).ncard
      = hammingBallVolume (Fintype.card F) ((r : ℝ) / (n : ℝ)) n := by
    rw [hammingBallVolume_eq_ncard_hammingBall ((r : ℝ) / (n : ℝ)) (0 : ι → F), hfloor]
  rw [heq]
  have hent := hammingBallVolume_ge_qEntropy hq ((r : ℝ) / (n : ℝ)) n
    (by rw [hfloor]; exact hr0) (by rw [hfloor]; exact hrn)
  rw [hfloor] at hent
  exact_mod_cast hent

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.hammingBall_ncard_ge_qEntropy
