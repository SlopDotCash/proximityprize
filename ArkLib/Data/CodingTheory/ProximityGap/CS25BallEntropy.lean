/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.EntropyBallNcard

/-!
# Entropy lower bound on the CS25 covered-fraction ball (#82)

The CS25 covered-fraction development counts the radius-`r` ball as the `Finset`
`{w : Δ₀(0,w) ≤ r}` (the `univ.filter` convention), whereas the entropy-volume development uses
`(ListDecodable.hammingBall 0 r).ncard`.  `filter_card_eq_hammingBall_ncard` bridges the two
conventions (the only subtlety is a `Classical`-vs-instance `DecidableEq` reconciliation on
`hammingDist`, handled by `convert`).  Transporting `hammingBall_ncard_ge_qEntropy` across the bridge
gives the entropy lower bound on the CS25 ball:

  `q^{n·H_q(r/n)} ≤ (n+1) · |{w : Δ₀(0,w) ≤ r}|`,

i.e. `V ≥ q^{n·H_q(r/n)}/(n+1)` for the `V` appearing in `rs_card_close_mul_sum_ge`.
-/

namespace CodingTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [Zero F]

/-- **Convention bridge.**  The CS25 `univ.filter` ball and the ListDecodable `hammingBall.ncard`
agree: `|{w : Δ₀(0,w) ≤ r}| = (hammingBall 0 r).ncard`.  (`hammingBall` uses a `Classical`
`DecidableEq` for `hammingDist`; the per-element instance gap is closed by `convert`.) -/
theorem filter_card_eq_hammingBall_ncard (r : ℕ) :
    (Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card
      = (ListDecodable.hammingBall (0 : ι → F) r).ncard := by
  have hball : ListDecodable.hammingBall (0 : ι → F) r
      = ↑(Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)) := by
    ext x
    simp only [ListDecodable.hammingBall, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor <;> intro h <;> convert h using 2
  rw [hball, Set.ncard_eq_toFinset_card', Finset.toFinset_coe]

/-- **Entropy lower bound on the CS25 covered-fraction ball** (`q = |F| ≥ 2`, `n = |ι|`, `0 < r < n`):
`q^{n·H_q(r/n)} ≤ (n+1)·|{w : Δ₀(0,w) ≤ r}|`.  `hammingBall_ncard_ge_qEntropy` transported across
`filter_card_eq_hammingBall_ncard`. -/
theorem filter_ball_card_ge_qEntropy (hq : 2 ≤ Fintype.card F) (r : ℕ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι) :
    (Fintype.card F : ℝ)
        ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
        * ((Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card : ℝ) := by
  rw [filter_card_eq_hammingBall_ncard]
  exact hammingBall_ncard_ge_qEntropy hq r hr0 hrn

end CodingTheory

-- Axiom audit.
#print axioms CodingTheory.filter_card_eq_hammingBall_ncard
#print axioms CodingTheory.filter_ball_card_ge_qEntropy
