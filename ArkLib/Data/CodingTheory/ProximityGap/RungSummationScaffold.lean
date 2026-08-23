/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RungSoloBound

/-!
# The summation scaffold (#371, rung): the partition-cover bound

The combinatorial frame the census summation plugs into.  The bad set of a
stack is covered by the zero-class (`≤ 1`, `poly_zero_class_unique`), a
finite family of frame classes (each `≤ n − |Aⱼ|`,
`maximal_frame_attached_card_le`), and the solo scalars (`≤ Fisher`,
`solo_scalars_card_le`).  This file proves the pure-`Finset` cover bound

  `#Γ ≤ 1 + Σ_{K ∈ classes} cap(K) + #solo`

(`bad_card_le_partition`), reducing the rung obligation to bounding the
class-cap sum — the class-coexistence count (the gluing/degree-collapse
laws constrain it; the empirical ceiling is `22 ≤ 31`).

The scaffold is fully general (no rung specifics), so it serves any
instance once the per-region caps are supplied.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

variable {F : Type} [DecidableEq F]

section SummationScaffold

/-- **The partition-cover bound**: a bad set covered by a single zero-class
element, a family of classes each bounded by its cap, and a solo set is
bounded by `1 + Σ caps + #solo`. -/
theorem bad_card_le_partition {Γ solo : Finset F} {z : F}
    {classes : Finset (Finset F)} {cap : Finset F → ℕ}
    (hcover : Γ ⊆ insert z (classes.biUnion id ∪ solo))
    (hcap : ∀ K ∈ classes, K.card ≤ cap K) :
    Γ.card ≤ 1 + (∑ K ∈ classes, cap K) + solo.card := by
  classical
  calc Γ.card ≤ (insert z (classes.biUnion id ∪ solo)).card :=
        Finset.card_le_card hcover
    _ ≤ 1 + (classes.biUnion id ∪ solo).card := by
        have := Finset.card_insert_le z (classes.biUnion id ∪ solo)
        omega
    _ ≤ 1 + ((classes.biUnion id).card + solo.card) := by
        have := Finset.card_union_le (classes.biUnion id) solo
        omega
    _ ≤ 1 + ((∑ K ∈ classes, K.card) + solo.card) := by
        have h := Finset.card_biUnion_le (s := classes) (t := id)
        simp only [id_eq] at h
        omega
    _ ≤ 1 + ((∑ K ∈ classes, cap K) + solo.card) := by
        have hsum : (∑ K ∈ classes, K.card) ≤ ∑ K ∈ classes, cap K :=
          Finset.sum_le_sum hcap
        omega
    _ = 1 + (∑ K ∈ classes, cap K) + solo.card := by ring

/-- **Uniform-cap corollary**: when every class shares a common cap `c` and
there are at most `t` classes, `#Γ ≤ 1 + t·c + #solo`. -/
theorem bad_card_le_uniform {Γ solo : Finset F} {z : F}
    {classes : Finset (Finset F)} {c t : ℕ}
    (hcover : Γ ⊆ insert z (classes.biUnion id ∪ solo))
    (hcap : ∀ K ∈ classes, K.card ≤ c)
    (ht : classes.card ≤ t) :
    Γ.card ≤ 1 + t * c + solo.card := by
  classical
  have h := bad_card_le_partition (cap := fun _ => c) hcover hcap
  have hsum : (∑ K ∈ classes, (fun _ => c) K) ≤ t * c := by
    rw [Finset.sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right c ht
  omega

end SummationScaffold

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.bad_card_le_partition
#print axioms ProximityGap.WBPencil.bad_card_le_uniform
