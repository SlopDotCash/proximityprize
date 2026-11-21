/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ListSupportRank
import ArkLib.ToMathlib.LinearAlgebra.Submodule.Union

/-! # Forced collisions in list support patterns

Over a field at least as large as the number of pairs, the full alternating
sum for a fixed support pattern reduces to one rank comparison per pair.
An oversized list exists if and only if some pattern loses dimension under
every individual collision constraint.
-/

namespace ProximityGap.ListSupportRank

open Code Finset

variable {K I : Type*} [Field K] [Fintype K] [Fintype I] {L : ℕ}

omit [Fintype I] in
/-- A support pattern realizes distinct words precisely when no individual pair is
forced equal by its overlap equations. The scalar solution avoiding all pairwise
collision spaces works in every positive width. -/
theorem positive_iff_proper [Finite I] (C : Submodule K (I → K)) (S : Fin L → Finset I)
    (m : ℕ) (hm : 0 < m) (hq : L.choose 2 ≤ Fintype.card K) :
    0 < rankCount C S m ↔ ∀ e ∈ pairs L, collisions C S {e} ≠ ⊤ := by
  classical
  rw [rankCount_pos_iff]
  constructor
  · rintro ⟨z, hz⟩ e he htop
    have hlt : e.1 < e.2 := (mem_filter.mp he).2
    apply hlt.ne
    apply hz
    funext j
    have hmem : z j ∈ collisions C S {e} := htop ▸ Submodule.mem_top
    exact hmem e (mem_singleton_self _)
  · intro hall
    have hcard : (pairs L).card ≤ Nat.card K := by
      simpa [pairs, Fintype.card_product_filter_lt, Nat.card_eq_fintype_card] using hq
    let _ : AddCommGroup ↥(compatible C S) := (compatible C S).addCommGroup
    obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_card_le (K := K) (M := ↥(compatible C S))
      (pairs L)
      (fun e => collisions C S {e}) hall hcard
    refine ⟨fun _ => z, fun {a b} heq => ?_⟩
    have he : z.val a = z.val b := congrFun heq ⟨0,hm⟩
    by_contra hne
    have avoid {a b : Fin L} (hlt : a < b) (he : z.val a = z.val b) : False :=
      hz (a,b) (mem_filter.mpr ⟨mem_univ _, hlt⟩) (by
        intro e he'
        simp only [mem_singleton] at he'
        subst e
        exact he)
    rcases lt_or_gt_of_ne hne with hl | hg
    · exact avoid hl he
    · exact avoid hg he.symm

omit [Fintype K] [Fintype I] in
private theorem empty_eq_top (C : Submodule K (I → K)) (S : Fin L → Finset I) :
    collisions C S ∅ = ⊤ := by
  ext
  simp [collisions]

/-- The full positivity criterion at large field size uses only the matrix with
no collision and the matrices with one collision. -/
theorem positive_iff_all_nullities_drop (α : I ↪ K) (k : ℕ) (hk : k ≤ Fintype.card I)
    (S : Fin L → Finset I) (m : ℕ) (hm : 0 < m) (hq : L.choose 2 ≤ Fintype.card K) :
    0 < rankCount (ReedSolomon.code α k) S m ↔ ∀ e ∈ pairs L,
      Module.finrank K (vandermonde α k S {e}).ker <
        Module.finrank K (vandermonde α k S ∅).ker := by
  rw [positive_iff_proper _ S m hm hq]
  apply forall_congr' fun e => forall_congr' fun _ => ?_
  rw [← nullity_eq α k hk S {e}, ← nullity_eq α k hk S ∅]
  let C := ReedSolomon.code α k
  let _ : AddCommGroup ↥(compatible C S) := (compatible C S).addCommGroup
  have hbase : Module.finrank K (collisions C S ∅) = Module.finrank K (compatible C S) :=
    (congrArg (fun p : Submodule K (compatible C S) => Module.finrank K p) (empty_eq_top C S)).trans
      (finrank_top K (compatible C S))
  change collisions C S {e} ≠ ⊤ ↔
    Module.finrank K (collisions C S {e}) < Module.finrank K (collisions C S ∅)
  rw [hbase]
  exact ⟨Submodule.finrank_lt, fun h heq => by
    rw [heq, finrank_top] at h
    exact lt_irrefl _ h⟩

/-- Safety at a specified agreement threshold is equivalent to every support pattern
forcing the equality of at least one pair of codewords. Neither centers nor words
appear on the right, and each pattern needs at most one plus the number of pairs
many kernel dimensions. -/
theorem rs_forced_pair_safe_iff (α : I ↪ K) (k m B t : ℕ) (hn : 0 < Fintype.card I)
    (hk : k ≤ Fintype.card I) (hm : 0 < m) (hq : (B + 1).choose 2 ≤ Fintype.card K) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
      (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) ↔
    ∀ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = t) → ∃ e ∈ pairs (B + 1),
      Module.finrank K (vandermonde α k S ∅).ker ≤
        Module.finrank K (vandermonde α k S {e}).ker := by
  rw [← not_lt, lambda_exceeds_iff (ReedSolomon.code α k) m B t hn]
  simp only [positive_iff_all_nullities_drop α k hk _ m hm hq]
  push Not
  rfl

/-- At 128-bit security throughout the field-size range highlighted by the prize paper,
the only field-size premise of the single-pair test holds automatically. -/
theorem prize_forced_pair_safe_iff (α : I ↪ K) (k m t : ℕ) (hn : 0 < Fintype.card I)
    (hk : k ≤ Fintype.card I) (hm : 0 < m) (hq : Fintype.card K < 2 ^ 256) :
    let B : ℕ := Fintype.card K / 2 ^ 128
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code α k : Set (I → K)))
      (1 - (t : ℝ) / Fintype.card I) ≤ (B : ℕ∞) ↔
    ∀ S : Fin (B + 1) → Finset I, (∀ a, (S a).card = t) → ∃ e ∈ pairs (B + 1),
      Module.finrank K (vandermonde α k S ∅).ker ≤
        Module.finrank K (vandermonde α k S {e}).ker := by
  intro B
  apply rs_forced_pair_safe_iff α k m B t hn hk hm
  have hB : B < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 128)).mpr
    exact hq
  rw [Nat.choose_two_right]
  apply (Nat.div_le_self _ 2).trans
  simp only [Nat.add_sub_cancel]
  exact (Nat.mul_le_mul_right B hB).trans
    ((Nat.mul_comm (2 ^ 128) B) ▸ Nat.div_mul_le_self (Fintype.card K) (2 ^ 128))

end ProximityGap.ListSupportRank

#print axioms ProximityGap.ListSupportRank.positive_iff_all_nullities_drop
#print axioms ProximityGap.ListSupportRank.rs_forced_pair_safe_iff

#print axioms ProximityGap.ListSupportRank.prize_forced_pair_safe_iff
