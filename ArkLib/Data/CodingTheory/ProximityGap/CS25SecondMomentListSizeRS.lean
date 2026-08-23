/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentListSize

/-!
# RS second moment as a sum of list-decoding list sizes (#82)

Combining the second-moment pairs/assembly identity `sum_sq_secondMomentCount_eq`
(`∑_w X(w)² = |RS|·∑_{e∈RS} |B(0,δ)∩B(e,δ)|`) with the Fubini list-size identity
`sum_jointCoverCount_eq_sum_listSize` gives the Reed–Solomon **second moment expressed directly as a
sum of list-decoding list sizes**:

  `∑_w X(w)²  =  |RS| · ∑_{w∈B(0,δ)} |{e∈RS : Δ(w,e) ≤ δ}|`,

and hence, for any uniform list-size bound `L`,

  `∑_w X(w)²  ≤  |RS| · (|B(0,δ)| · L)`.

This is the bridge from CS25's second moment to list decoding: the in-tree Johnson list-size bound
(`CodeGeometry.card_le_of_johnson_sq_dist`) supplies `L` in the Johnson-decoding range, controlling
`E[N²]`.  Both statements are `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators ENNReal NNReal
open Code Finset Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **RS second moment = `|RS|` × sum of list sizes (#82).**
`∑_w X(w)² = |RS| · ∑_{w∈B(0,δ)} |{e∈RS : Δ(w,e) ≤ δ}|`. -/
theorem sum_sq_secondMomentCount_eq_sum_listSize (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) :
    (∑ w : ι → F, (CodingTheory.secondMomentCount domain k δ w) ^ 2)
      = (univ.filter (fun c : ι → F => c ∈ (ReedSolomon.code domain k : Set (ι → F)))).card
        * ∑ w ∈ univ.filter
              (fun w : ι → F => (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal)),
            ((univ.filter (fun e : ι → F => e ∈ (ReedSolomon.code domain k : Set (ι → F)))).filter
              (fun e => (relHammingDist w e : ENNReal) ≤ (δ : ENNReal))).card := by
  rw [sum_sq_secondMomentCount_eq, sum_jointCoverCount_eq_sum_listSize]

/-- **RS second moment ≤ `|RS| · |B(0,δ)| · L`** for any uniform list-size bound `L`.
With the in-tree Johnson list-size bound supplying `L` in the Johnson-decoding range, this controls
the RS second moment `E[N²]`. -/
theorem sum_sq_secondMomentCount_le_listSize (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (L : ℕ)
    (hL : ∀ w : ι → F,
      ((univ.filter (fun e : ι → F => e ∈ (ReedSolomon.code domain k : Set (ι → F)))).filter
        (fun e => (relHammingDist w e : ENNReal) ≤ (δ : ENNReal))).card ≤ L) :
    (∑ w : ι → F, (CodingTheory.secondMomentCount domain k δ w) ^ 2)
      ≤ (univ.filter (fun c : ι → F => c ∈ (ReedSolomon.code domain k : Set (ι → F)))).card
        * ((univ.filter
            (fun w : ι → F => (relHammingDist w 0 : ENNReal) ≤ (δ : ENNReal))).card * L) := by
  rw [sum_sq_secondMomentCount_eq]
  exact Nat.mul_le_mul_left _
    (sum_jointCoverCount_le_card_mul_listSize
      (univ.filter (fun e : ι → F => e ∈ (ReedSolomon.code domain k : Set (ι → F)))) δ L hL)

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_sq_secondMomentCount_eq_sum_listSize
#print axioms ArkLib.CS25.sum_sq_secondMomentCount_le_listSize
