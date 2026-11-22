/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus

/-! # Six words at five agreements on sixteen coordinates

For seven five-element supports with pairwise overlaps at most one, the integer
second-moment bound at multiplicities two and three would give $140 \le 138$.
Thus a dimension-two interleaved list has size at most six below radius $12/16$.
-/

namespace ProximityGap.SixteenFiveListCap

open Code

variable {I : Type} [Fintype I] {F : Type*} [Field F]

/-- Seven blocks of size five cannot meet pairwise in at most one of sixteen coordinates. -/
theorem block_bound [DecidableEq I] (hn : Fintype.card I = 16) {s : ℕ}
    (S : Fin s → Finset I) (hs : ∀ i, 5 ≤ (S i).card)
    (hp : Pairwise fun i j => (S i ∩ S j).card ≤ 1) : s ≤ 6 := by
  by_contra! h
  let e : Fin 7 → Fin s := Fin.castLE (by omega)
  have hinj : Function.Injective e := Fin.castLE_injective _
  have bound := RateHalfRichHeadCensus.incidence_bound (fun i => S (e i))
    (fun i => hs (e i)) (fun i j hij => hp (hinj.ne hij)) 2
  rw [hn] at bound
  norm_num at bound

/-- Every closed list below the four-agreement radius has at most six words,
over any field, for every injective domain and interleaving width. -/
theorem list_bound_below [Nonempty I] (D : I ↪ F) (hn : Fintype.card I = 16) (m : ℕ)
    (δ : ℝ) (hδ : δ < 12 / 16) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 2 : Set (I → F))) δ ≤ 6 := by
  classical
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D 2 5 m 6
  · rw [hn]
    norm_num at *
    linarith
  · exact fun _ S hs hp => block_bound hn S (fun i => (hs i).ge) hp

/-- The closed ball at exactly eleven errors satisfies the six-word bound. -/
theorem list_bound [Nonempty I] (D : I ↪ F) (hn : Fintype.card I = 16) (m : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 2 : Set (I → F)))
      (11 / 16 : ℝ) ≤ 6 :=
  list_bound_below D hn m _ (by norm_num)

end ProximityGap.SixteenFiveListCap
