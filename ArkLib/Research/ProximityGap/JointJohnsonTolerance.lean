/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.ConstantJohnsonTolerance

/-! # Simultaneous Johnson equality at a supplied tolerance

The same smooth code must realize both numerical cutoffs at Johnson. In dimension
one the MCA cutoff is one exactly when all radii pass. The list cutoff is one
exactly when the integer budget covers the number of sites. -/

namespace ProximityPrize.JointJohnsonTolerance

open FullPrizeReview RankJohnsonComparison ConstantJohnsonTolerance ProximityGap
open scoped NNReal ENNReal

/-- A supplied code attains the common operational cutoff at every positive width. -/
def both {I F : Type} [Field F] [Fintype F] [Fintype I] (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) :
    Prop :=
  let J := 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)
  (cutoff (RankReview.mcaAnswer D ε k) : ℝ) / Fintype.card I = J ∧
    ∀ m : ℕ, 0 < m → (cutoff (RankReview.listAnswer D ε k m) : ℝ) / Fintype.card I = J

/-- At any eligible dimension, this reduces simultaneous equality on a supplied code
to dimension one, radius-one MCA safety, and an integer list budget of at least the length. -/
theorem supplied_iff {I F : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) {k : ℕ}
    (hr : hasPrizeRate (Fintype.card I) k) :
    both D ε k ↔ k = 1 ∧ RankReview.mcaAnswer D ε 1 = none ∧
      Fintype.card I ≤ RankReview.budget F ε := by
  have hn : 0 < Fintype.card I := Fintype.card_pos
  have eq_one (a : Boundary (Fintype.card I)) :
      (cutoff a : ℝ) / Fintype.card I = 1 - Real.sqrt (((1 - 1 : ℕ) : ℝ) / Fintype.card I) ↔
        cutoff a = Fintype.card I := by
    simp only [tsub_self, Nat.cast_zero, zero_div, Real.sqrt_zero, sub_zero]
    rw [div_eq_iff (by exact_mod_cast hn.ne'), one_mul, Nat.cast_inj]
  constructor
  · rintro ⟨mc, list⟩
    have one := JointJohnsonEquality.dimension_one_of_both D ε hr 1 mc (list 1 (by decide))
    subst k
    have good := (list_cutoff_iff D ε (m := 1) (by decide)).mp ((eq_one _).mp (list 1 (by decide)))
    refine ⟨rfl, ?_, good⟩
    have size := (eq_one _).mp mc
    cases ha : RankReview.mcaAnswer D ε 1 with
    | none => rfl
    | some e =>
      have bound := CapacityBoundaryReview.mca_ceiling D ε hr ha
      rw [ha] at size
      change e.val = Fintype.card I at size
      omega
  · rintro ⟨rfl, mc, list⟩
    refine ⟨(eq_one _).mpr ?_, fun m hm => (eq_one _).mpr ((list_cutoff_iff D ε hm).mpr list)⟩
    rw [mc]
    rfl

/-- A realization above any prescribed field-size lower bound exists exactly in
dimension one at strictly positive tolerance. The prime-field construction allows
arbitrarily large fields; the necessity also applies below any imposed ceiling. -/
theorem exists_above_iff {n k : ℕ} (hr : hasPrizeRate n k) (ε : ℝ≥0) (lower : ℕ) :
    (∃ (F I : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : Fintype I)
      (_ : Nonempty I) (D : I ↪ F), Nonempty (ReedSolomon.Smooth D) ∧
        Fintype.card I = n ∧ lower < Fintype.card F ∧ both D ε k) ↔ k = 1 ∧ 0 < ε := by
  constructor
  · rintro ⟨F, I, _, _, _, _, _, D, ⟨sm⟩, len, _, joint⟩
    subst n
    obtain ⟨one, _, budget⟩ := (supplied_iff D ε hr).mp joint
    refine ⟨one, lt_of_le_of_ne (bot_le : (0 : ℝ≥0) ≤ ε) ?_⟩
    rintro rfl
    simp [RankReview.budget, Fintype.card_ne_zero] at budget
  · rintro ⟨rfl, positive⟩
    obtain ⟨p, _, big, D, ⟨sm⟩, mc, list⟩ := arbitrarily_large hr ε positive lower
    have hn : 0 < n := by rcases hr with h | h | h | h <;> omega
    let _ : NeZero n := ⟨hn.ne'⟩
    refine ⟨ZMod p, Fin n, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, D, ⟨sm⟩, Fintype.card_fin n, (by simpa only [ZMod.card] using big), ?_⟩
    apply (supplied_iff D ε (by simpa only [Fintype.card_fin] using hr)).mpr
    refine ⟨rfl, mc, (list_cutoff_iff D ε (m := 1) (by decide)).mp ?_⟩
    simpa only [Fintype.card_fin] using list 1 (by decide)

end ProximityPrize.JointJohnsonTolerance
