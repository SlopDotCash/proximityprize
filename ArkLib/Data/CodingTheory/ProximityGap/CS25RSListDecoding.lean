/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance

/-!
# Johnson-radius list decoding for Reed–Solomon codes (#82)

`card_finset_le_of_johnson` lifts the in-tree family-form Johnson list-size bound
(`CodeGeometry.card_le_of_johnson_sq_dist`) to a **Finset** of codewords (enumerated via
`Finset.equivFin`): a finset of codewords all within distance `e` of `f`, pairwise distance `≥ d`,
satisfying the Johnson quadratic condition, has size `≤ ℓ`.

`rs_list_size_le` specialises this to Reed–Solomon: using the RS minimum distance `n−(k−1)`
(`rsCodeFinset_hammingDist_ge`), the number of RS codewords within distance `e` of any word is `≤ ℓ`
whenever the Johnson conditions hold — i.e. RS codes are list-decodable up to the Johnson radius.
`sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset CodeGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Johnson bound, Finset form.** A finset `S` of codewords all within distance `e` of `f`, pairwise
distance `≥ d`, satisfying the Johnson quadratic condition, has `|S| ≤ ℓ`. -/
theorem card_finset_le_of_johnson (hq1 : 1 < Fintype.card α) (hn : 0 < Fintype.card ι)
    (f : ι → α) (S : Finset (ι → α)) {e d : ℕ} (ℓ : ℕ)
    (hclose : ∀ x ∈ S, hammingDist x f ≤ e)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ hammingDist x y)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - d : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))) :
    S.card ≤ ℓ := by
  classical
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · omega
  · set c : Fin S.card → (ι → α) := fun i => ((S.equivFin.symm i : ↥S) : ι → α) with hc
    have hcmem : ∀ i, c i ∈ S := fun i => (S.equivFin.symm i).2
    have hcinj : Function.Injective c := by
      intro i j hij
      exact S.equivFin.symm.injective (Subtype.val_injective hij)
    refine card_le_of_johnson_sq_dist hq1 hn hpos f c ℓ ?_ ?_ hP hsq
    · intro i; exact hclose (c i) (hcmem i)
    · intro i j hne; exact hdist (c i) (hcmem i) (c j) (hcmem j) (fun h => hne (hcinj h))

/-- **Reed–Solomon list-decoding (Johnson radius).** Given the Johnson conditions at the RS minimum
distance `d = n−(k−1)`, the number of RS codewords within Hamming distance `e` of any word `f` is at
most `ℓ`. -/
theorem rs_list_size_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) [NeZero k]
    (hq1 : 1 < Fintype.card F) (hn : 0 < Fintype.card ι) (f : ι → F) (e ℓ : ℕ)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - e : ℕ) : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - (Fintype.card ι - (k - 1)) : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    ((rsCodeFinset domain k).filter (fun c => hammingDist c f ≤ e)).card ≤ ℓ := by
  refine card_finset_le_of_johnson (d := Fintype.card ι - (k - 1)) hq1 hn f _ ℓ ?_ ?_ hP hsq
  · intro x hx; rw [Finset.mem_filter] at hx; exact hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_filter] at hx hy
    exact rsCodeFinset_hammingDist_ge domain k x y hx.1 hy.1 hxy

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.card_finset_le_of_johnson
#print axioms ArkLib.CS25.rs_list_size_le
