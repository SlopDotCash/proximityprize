/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskSelections

/-! # Weighted union of the two anchor signature classes -/

set_option maxRecDepth 8000
namespace ProximityGap.QuotientMaskBudget

open Finset QuotientSignatureCensus QuotientMaskSelections
open scoped Classical

/-- Uniform labels on the odd leaves of a dyadic subtree. -/
def flat : (d : ℕ) → ℕ → Leaves ℕ d
  | 0, v => v
  | d+1, v => (flat d v, flat d v)

abbrev V := Leaves ℕ 4
abbrev M := Mask 4

def modes : Fin 4 → V :=
  ![flat 4 5, (flat 3 6, flat 3 5), (flat 3 5, flat 3 6), (flat 3 5, flat 2 5, flat 2 6)]

def singles : Fin 4 → ℕ := ![12219257340, 10463808348, 10463808348, 10080571912]

/-- Only the first three original signatures are used. -/
def joints : Fin 3 → Fin 4 → ℕ :=
  ![![237308948,0,0,0],![0,556624096,52922120,0],![0,52922120,556624096,0]]

private theorem single_table (i : Fin 4) : population (shape 4 (modes i) none) 33 = singles i := by
  fin_cases i
  · exact QuotientSignatureTables.singleA_count
  · exact QuotientSignatureTables.singleB_count
  · exact QuotientSignatureTables.singleC_count
  · exact QuotientSignatureTables.singleD_count

private theorem joint_table (i : Fin 3) (j : Fin 4) :
    population (shape 4 (modes i.castSucc) (some (modes j))) 33 = joints i j := by
  fin_cases i <;> fin_cases j
  · exact QuotientSignatureTables.jointAA_count
  · exact QuotientSignatureTables.jointAB_count
  · exact QuotientSignatureTables.jointAC_count
  · exact QuotientSignatureTables.jointAD_count
  · exact QuotientSignatureTables.jointBA_count
  · exact QuotientSignatureTables.jointBB_count
  · exact QuotientSignatureTables.jointBC_count
  · exact QuotientSignatureTables.jointBD_count
  · exact QuotientSignatureTables.jointCA_count
  · exact QuotientSignatureTables.jointCB_count
  · exact QuotientSignatureTables.jointCC_count
  · exact QuotientSignatureTables.jointCD_count

noncomputable def selections : Finset M := univ.filter fun m => count 4 m = 33

noncomputable def hit (s : V) (i : Fin 4) : ℤ := if s=modes i then 1 else 0

private theorem single_original (i : Fin 4) :
    ∑ m ∈ selections, hit (signatures 4 m).1 i = (singles i : ℤ) := by
  simp only [hit, sum_boole]
  rw [← single_table i, ← card_signatures 4 (modes i) none 33]
  apply congrArg (fun t : Finset M => (t.card : ℤ))
  ext m
  simp [selections, fits, and_comm]

private theorem single_rotated (i : Fin 4) :
    ∑ m ∈ selections, hit (signatures 4 m).2 i = (singles i : ℤ) := by
  simp only [hit, sum_boole]
  rw [← single_table i, ← card_rotated 4 (modes i) 33]
  apply congrArg (fun t : Finset M => (t.card : ℤ))
  ext m
  simp [selections, and_comm]

private theorem indicator_joint {α : Type} [Fintype α] (a b c : α → Prop)
    [DecidablePred a] [DecidablePred b] [DecidablePred c] :
    (∑ x ∈ univ.filter c, (if a x then (1 : ℤ) else 0)*(if b x then 1 else 0)) =
      ((univ.filter fun x => a x ∧ b x ∧ c x).card : ℤ) := by
  have term (x : α) : (if a x then (1 : ℤ) else 0)*(if b x then 1 else 0) =
      if a x ∧ b x then 1 else 0 := by split <;> split <;> simp_all
  simp only [term, sum_boole, filter_filter]
  apply congrArg (fun s : Finset α => (s.card : ℤ))
  apply filter_congr
  intro x _
  tauto

private theorem joint_sum (i : Fin 3) (j : Fin 4) :
    ∑ m ∈ selections, hit (signatures 4 m).1 i.castSucc * hit (signatures 4 m).2 j =
    (joints i j : ℤ) := by
  have anchor := card_signatures 4 (modes i.castSucc) (some (modes j)) 33
  exact (indicator_joint (fun m : M => (signatures 4 m).1=modes i.castSucc)
    (fun m : M => (signatures 4 m).2=modes j) (fun m : M => count 4 m=33)).trans
      (congrArg Nat.cast (anchor.trans (joint_table i j)))

/-- Number of admissible signs for an original or rotated mask, weighted by signature. -/
noncomputable def positive (u : Fin 3 → ℤ) (m : M) := ∑ i, u i * hit (signatures 4 m).1 i.castSucc
noncomputable def negative (v : Fin 4 → ℤ) (m : M) := ∑ i, v i * hit (signatures 4 m).2 i

private theorem pos_sum (u : Fin 3 → ℤ) :
    ∑ m ∈ selections, positive u m = ∑ i, u i * singles i.castSucc := by
  simp only [positive]
  rw [sum_comm]
  simp_rw [← mul_sum, single_original]

private theorem neg_sum (v : Fin 4 → ℤ) :
    ∑ m ∈ selections, negative v m = ∑ j, v j * singles j := by
  simp only [negative]
  rw [sum_comm]
  simp_rw [← mul_sum, single_rotated]

private theorem cross_sum (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) :
    ∑ m ∈ selections, positive u m * negative v m = ∑ i, ∑ j, (u i*v j)*joints i j := by
  simp only [positive, negative, sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp_rw [mul_mul_mul_comm (u i) _ (v j), ← mul_sum, joint_sum]

/-- Total multiplicity over the four independent choices of anchor signs. -/
noncomputable def total (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) :=
  ∑ m ∈ selections, (2*positive u m + 2*negative v m - positive u m * negative v m)

theorem total_eq (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) : total u v =
    2*(∑ i, u i * singles i.castSucc) + 2*(∑ j, v j * singles j) -
      ∑ i, ∑ j, (u i*v j)*joints i j := by
  simp only [total, sum_sub_distrib, sum_add_distrib, ← mul_sum, pos_sum, neg_sum, cross_sum]

theorem first_total : total ![2,0,1] ![2,1,0,0] = 138607134200 := by
  rw [total_eq]
  decide

theorem second_total : total ![2,2,2] ![2,2,2,1] = 279510530592 := by
  rw [total_eq]
  decide

private instance leavesDec (d : ℕ) : DecidableEq (Leaves ℕ d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq ℕ)
  | succ d ih => letI := ih; exact inferInstanceAs (DecidableEq (Leaves ℕ d × Leaves ℕ d))

theorem mode_injective : Function.Injective modes := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private theorem bounded_weight {ι : Type} [Fintype ι] [DecidableEq ι] (ids : ι ↪ Fin 4)
    (w : ι → ℤ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 2) (s : V) :
    0 ≤ (∑ i, w i * hit s (ids i)) ∧ (∑ i, w i * hit s (ids i)) ≤ 2 := by
  by_cases h : ∃ i, s=modes (ids i)
  · obtain ⟨i,hi⟩ := h
    have hz (j : ι) (_hj : j ∈ univ) (hji : j ≠ i) : w j * hit s (ids j) = 0 := by
      have ne : s ≠ modes (ids j) := fun he => hji (ids.injective (mode_injective (he.symm.trans hi)))
      simp [hit,ne]
    rw [sum_eq_single i hz (by simp)]
    simpa [hit,hi] using hw i
  · push Not at h
    simp [hit,h]

theorem seats_eq {ι : Type} [Fintype ι] [DecidableEq ι] (ids : ι ↪ Fin 4)
    (w : ι → ℤ) (s : V) (i : ι) (hi : s=modes (ids i)) :
    (∑ j, w j * hit s (ids j)) = w i := by
  rw [sum_eq_single i]
  · simp [hit,hi]
  · intro j _ hji
    have ne : s ≠ modes (ids j) := fun he => hji (ids.injective (mode_injective (he.symm.trans hi)))
    simp [hit,ne]
  · simp

theorem seats_zero {ι : Type} [Fintype ι] (ids : ι → Fin 4) (w : ι → ℤ) (s : V)
    (h : ∀ i, s≠modes (ids i)) : (∑ i, w i * hit s (ids i)) = 0 := by simp [hit,h]

/-- The sign chosen for a signature matters only when one anchor value is allocated. -/
def admissible (multiplicity : ℤ) (chosen actual : Bool) : Prop :=
  multiplicity=2 ∨ multiplicity=1 ∧ chosen=actual

instance (n : ℤ) (p a : Bool) : Decidable (admissible n p a) :=
  inferInstanceAs (Decidable (n=2 ∨ n=1 ∧ p=a))

abbrev Config := (Bool × Bool) × Fin 32

/-- The selections retained by one product bucket and by either permitted anchor value. -/
noncomputable def picked (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) (bucket : M → Fin 32)
    (atPlus atMinus : M → Bool) (cfg : Config) : Finset M :=
  selections.filter fun m => (admissible (positive u m) cfg.1.1 (atPlus m) ∨
    admissible (negative v m) cfg.1.2 (atMinus m)) ∧ bucket m=cfg.2

theorem mem_picked (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) (bucket : M → Fin 32)
    (atPlus atMinus : M → Bool) (cfg : Config) (m : M) :
    m ∈ picked u v bucket atPlus atMinus cfg ↔ m ∈ selections ∧
      (admissible (positive u m) cfg.1.1 (atPlus m) ∨ admissible (negative v m) cfg.1.2 (atMinus m)) ∧
        bucket m=cfg.2 := mem_filter

theorem mem_selections (m : M) : m ∈ selections ↔ count 4 m=33 := by
  simp [selections]

private theorem sign_pairs (a b : ℤ) (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2)
    (p q : Bool) : (∑ signs : Bool × Bool, if admissible a signs.1 p ∨ admissible b signs.2 q
      then (1 : ℤ) else 0) = 2*a+2*b-a*b := by
  rcases (show a=0 ∨ a=1 ∨ a=2 by omega) with rfl | rfl | rfl <;>
    rcases (show b=0 ∨ b=1 ∨ b=2 by omega) with rfl | rfl | rfl <;>
    cases p <;> cases q <;> decide

/-- Pigeonhole the product and two independent signs while retaining their
joint intersection on the same selections. -/
theorem exists_bucket (u : Fin 3 → ℤ) (v : Fin 4 → ℤ) (bucket : M → Fin 32)
    (atPlus atMinus : M → Bool) (B : ℕ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 2) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 2)
    (budget : 128*(B : ℤ)<total u v) :
    ∃ cfg : Config, B < (picked u v bucket atPlus atMinus cfg).card := by
  by_contra! h
  have bound := sum_le_sum (s:=univ) (fun (c : Config) _ =>
    (show ((picked u v bucket atPlus atMinus c).card : ℤ) ≤ B by exact_mod_cast h c))
  have cardinal : Fintype.card Config = 128 := by decide
  rw [sum_const, card_univ, cardinal, nsmul_eq_mul] at bound
  apply (not_le_of_gt budget)
  apply le_trans _ bound
  apply le_of_eq
  symm
  unfold picked
  simp_rw [← sum_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Fintype.sum_prod_type]
  have each (z : Bool × Bool) :
      (∑ g : Fin 32, if (admissible (positive u m) z.1 (atPlus m) ∨
        admissible (negative v m) z.2 (atMinus m)) ∧ bucket m=g then (1 : ℤ) else 0) =
        if admissible (positive u m) z.1 (atPlus m) ∨ admissible (negative v m) z.2 (atMinus m)
        then 1 else 0 := by
    by_cases ok : admissible (positive u m) z.1 (atPlus m) ∨ admissible (negative v m) z.2 (atMinus m)
    · simp [ok]
    · simp [ok]
  simp only [each]
  exact sign_pairs _ _ (bounded_weight (Fin.castSuccEmb : Fin 3 ↪ Fin 4) u hu _)
    (bounded_weight (Function.Embedding.refl _) v hv _) _ _

theorem first_bucket (bucket : M → Fin 32) (atPlus atMinus : M → Bool) :
    ∃ cfg : Config, 1082868235 < (picked ![2,0,1] ![2,1,0,0] bucket atPlus atMinus cfg).card :=
  exists_bucket _ _ _ _ _ _ (by decide) (by decide) (by rw [first_total]; decide)

theorem second_bucket (bucket : M → Fin 32) (atPlus atMinus : M → Bool) :
    ∃ cfg : Config, 2183676020 < (picked ![2,2,2] ![2,2,2,1] bucket atPlus atMinus cfg).card :=
  exists_bucket _ _ _ _ _ _ (by decide) (by decide) (by rw [second_total]; decide)

#print axioms first_bucket
#print axioms second_bucket
#print axioms first_total
#print axioms second_total
end ProximityGap.QuotientMaskBudget
