/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionWeightInvariant
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionBudget

/-!
# CS25 #82, deliverable 2: the dimension-explicit second-moment decay sum

This file assembles the two halves of the ball-intersection second-moment machinery into a single,
fully `(d, q)`-explicit bound on the CS25 second-moment sum `∑_{e ∈ C} I(e)`,
`I(e) = jointCoverCount δ 0 e = |B(0,δ) ∩ B(e,δ)|`:

  `∑_{e ∈ C} I(e) ≤ ∑_d A_d · (V_{n−d}(⌊(2r−d)/2⌋) · q^d)`,

with `A_d = #{e ∈ C : wt(e) = d}` the code's weight enumerator, `r = ⌊δ·n⌋`, `q = |F|`, and
`V_m(B) = #{x ∈ F^m : wt(x) ≤ B}` a Hamming ball volume that depends only on the dimension `m`.

It combines:
* the **weight-enumerator collapse** `∑_{e∈C} I(e) = ∑_d A_d · I_d`
  (`CS25BallIntersectionWeightInvariant.sum_jointCoverCount_eq_weight_enumerator`); and
* the **explicit decay bound** `I(e) ≤ V_{n−wt(e)}(⌊(2r−wt(e))/2⌋) · q^{wt(e)}`
  (`CS25BallIntersectionBudget.jointCoverCount_le_ballVolume_mul`), here recast so the ball volume
  depends only on the codimension `n − wt(e)` rather than the specific support.

Plugging the MDS weight-enumerator bound `A_d ≤ C(n,d) q^{d−(n−k)}`
(`RSWeightEnumerator.card_evalWeight_le`) together with a `qEntropy` estimate on `V_{n−d}` into this
sum is the remaining route to the CS25 covered-fraction / proximity-gap second moment.

## Main results

* `hammingNorm_comp_equiv` — reindexing coordinates by a bijection preserves the Hamming norm.
* `hammingBallVol` / `card_hammingBall_eq_vol` — the Hamming ball volume depends only on dimension.
* `jointCoverCount_le_ballVol_dim` — the dimension-explicit decay bound for `I(e)`.
* `sum_jointCoverCount_le_weightEnum_decay` — the off-diagonal second moment `≤ ∑_d A_d · g(d)`.
-/

set_option linter.style.longLine false


open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- Reindexing coordinates by a bijection `σ` preserves the Hamming norm. -/
theorem hammingNorm_comp_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (σ : α ≃ β) (x : α → F) : hammingNorm (fun j => x (σ.symm j)) = hammingNorm x := by
  classical
  unfold hammingNorm
  refine Finset.card_bij' (fun j _ => σ.symm j) (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj
  · intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; simpa using hi
  · intro j _; simp
  · intro i _; simp

/-- Hamming ball volume: the number of length-`m` words over `F` of weight `≤ B`. -/
noncomputable def hammingBallVol (F : Type*) [Fintype F] [DecidableEq F] [Zero F] (m B : ℕ) : ℕ :=
  (univ.filter (fun x : Fin m → F => hammingNorm x ≤ B)).card

/-- **Dimension invariance of the ball volume.** The number of weight-`≤B` words over a coordinate
type `α` depends only on `|α|`. -/
theorem card_hammingBall_eq_vol {α : Type*} [Fintype α] [DecidableEq α] (B : ℕ) :
    (univ.filter (fun x : α → F => hammingNorm x ≤ B)).card
      = hammingBallVol F (Fintype.card α) B := by
  classical
  let σ : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  unfold hammingBallVol
  refine Finset.card_bij' (fun x _ => fun j => x (σ.symm j)) (fun y _ => fun i => y (σ i))
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rwa [hammingNorm_comp_equiv σ x]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [show (fun i => y (σ i)) = (fun i => y (σ.symm.symm i)) from by simp,
      hammingNorm_comp_equiv σ.symm y]
    exact hy
  · intro x _; funext i; simp
  · intro y _; funext j; simp

/-- The number of coordinates *off* `supp(e)` is the codimension `n − wt(e)`. -/
theorem card_compl_support (e : ι → F) :
    Fintype.card {i // e i = 0} = Fintype.card ι - hammingNorm e := by
  have h1 : Fintype.card {i // ¬ (e i = 0)}
      = Fintype.card ι - Fintype.card {i // e i = 0} := Fintype.card_subtype_compl _
  have h2 : Fintype.card {i // ¬ (e i = 0)} = hammingNorm e := by
    rw [Fintype.card_subtype]; rfl
  have h3 : Fintype.card {i // e i = 0} ≤ Fintype.card ι := Fintype.card_subtype_le _
  omega

/-- **Dimension-explicit ball-intersection decay.** `I(e) ≤ V_{n−wt(e)}(B')·q^{wt(e)}` with
`B' = ⌊(2r−wt(e))/2⌋`, `r = ⌊δ·n⌋`; the ball volume now depends only on the codimension `n − wt(e)`. -/
theorem jointCoverCount_le_ballVol_dim (δ : ℝ≥0) (e : ι → F) :
    jointCoverCount δ 0 e
      ≤ hammingBallVol F (Fintype.card ι - hammingNorm e)
          ((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - hammingNorm e) / 2)
        * (Fintype.card F) ^ (hammingNorm e) := by
  refine le_trans (jointCoverCount_le_ballVolume_mul δ e) ?_
  rw [card_hammingBall_eq_vol, card_compl_support]

/-- **Off-diagonal second moment bounded by the weight-enumerator decay sum.**
`∑_{e∈C} I(e) ≤ ∑_d A_d · (V_{n−d}(⌊(2r−d)/2⌋)·q^d)`, the fully `(d,q)`-explicit CS25 second-moment
bound.  Combine with the MDS weight enumerator `A_d ≤ C(n,d)q^{d−(n−k)}` and a `qEntropy` estimate on
`V_{n−d}` to bound the off-diagonal `∑_{e≠0} I(e)`. -/
theorem sum_jointCoverCount_le_weightEnum_decay (C : Finset (ι → F)) (δ : ℝ≥0)
    (rep : ℕ → (ι → F)) (hrep : ∀ d ∈ C.image hammingNorm, hammingNorm (rep d) = d) :
    ∑ e ∈ C, jointCoverCount δ 0 e
      ≤ ∑ d ∈ C.image hammingNorm,
          (C.filter (fun e => hammingNorm e = d)).card
            * (hammingBallVol F (Fintype.card ι - d)
                ((2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ - d) / 2) * (Fintype.card F) ^ d) := by
  rw [sum_jointCoverCount_eq_weight_enumerator C δ rep hrep]
  refine Finset.sum_le_sum (fun d hd => ?_)
  refine Nat.mul_le_mul_left _ ?_
  have hd' := hrep d hd
  have := jointCoverCount_le_ballVol_dim δ (rep d)
  rwa [hd'] at this

end ArkLib.CS25
