/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.CodeGeometry

/-!
# The Singleton bound

A code `𝒞 ⊆ (ι → F)` with minimum distance `≥ d` (`d ≥ 1`) has at most `q^(n − (d−1))` codewords,
where `q = |F|` and `n = |ι|`.  Projecting onto any `n − (d−1)` coordinates is injective on `𝒞`
(two codewords agreeing there would differ in `≤ d−1 < d` positions, contradicting the minimum
distance), so `|𝒞| ≤ |F^{n−(d−1)}| = q^(n−(d−1))`.

This is the classical Singleton bound.  Reed–Solomon codes achieve it with equality
(`rsCodeFinset_card = q^k` and minimum distance `n − k + 1`), i.e. they are MDS.  `sorry`/`axiom`-free.
-/

namespace ArkLib.CS25

open scoped BigOperators
open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F]

/-- **Singleton bound.**  A code with minimum distance `≥ d` (`d ≥ 1`) has at most `q^(n−(d−1))`
codewords. -/
theorem singleton_bound (𝒞 : Finset (ι → F)) (d : ℕ) (hd : 1 ≤ d)
    (hmin : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' → d ≤ hammingDist c c') :
    𝒞.card ≤ Fintype.card F ^ (Fintype.card ι - (d - 1)) := by
  classical
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
    (show Fintype.card ι - (d - 1) ≤ (univ : Finset ι).card by rw [card_univ]; exact Nat.sub_le _ _)
  have hinj : Set.InjOn (fun c : ι → F => fun i : ↥S => c (i : ι)) ↑𝒞 := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    by_contra hne
    have hagree_ge : S.card ≤ CodeGeometry.agree a b := by
      rw [CodeGeometry.agree]
      refine Finset.card_le_card (fun i hiS => ?_)
      exact mem_filter.mpr ⟨mem_univ _, congrFun hab ⟨i, hiS⟩⟩
    have hsum := CodeGeometry.agree_add_hammingDist a b
    have hdist := hmin a ha b hb hne
    omega
  calc 𝒞.card = (𝒞.image (fun c : ι → F => fun i : ↥S => c (i : ι))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (↥S → F) := Finset.card_le_univ _
    _ = Fintype.card F ^ (Fintype.card ι - (d - 1)) := by
        rw [Fintype.card_fun, Fintype.card_coe, hScard]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.singleton_bound
