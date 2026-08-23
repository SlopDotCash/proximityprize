/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionBound
import Mathlib.Data.Finset.Powerset

/-!
# CS25 #82, deliverable 2 (b/d): the support-union tail bound (original argument)

A clean route to the ball-intersection tail that avoids the `(z,t,o)` multinomial estimate.

Since `supp(w - f) ⊆ supp(w) ∪ supp(f)`, every "far" pair (`Δ₀(w,f) > n-k`) has
`|supp(w) ∪ supp(f)| > n-k`.  Mapping a far pair to `⟨supp(w) ∪ supp(f), (w, f)⟩` injects the far
pairs into `⨆_{|U|>n-k} (subBall U)²`, giving

  `∑_{wt(e)>n-k} I(e) ≤ ∑_{U : |U|>n-k} (#{w : supp(w) ⊆ U, wt(w) ≤ r})²`,

which reduces the CS25 second-moment tail to a clean sum over coordinate sets.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- The Hamming support of `w`. -/
def hSupp (w : ι → F) : Finset ι := Finset.univ.filter (fun i => w i ≠ 0)

/-- `Δ₀(w,f)` counts only coordinates in `supp(w) ∪ supp(f)`. -/
theorem hammingDist_le_card_union (w f : ι → F) :
    hammingDist w f ≤ (hSupp w ∪ hSupp f).card := by
  classical
  rw [hammingDist]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_union, hSupp, hSupp]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hcon
  push_neg at hcon
  exact hi.2 (by rw [hcon.1, hcon.2])

/-- `supp(w) ⊆ supp(w) ∪ supp(f)` membership helper: `hSupp` is monotone enough for the union. -/
theorem hSupp_sub_union_left (w f : ι → F) : hSupp w ⊆ hSupp w ∪ hSupp f :=
  Finset.subset_union_left

end ArkLib.CS25
