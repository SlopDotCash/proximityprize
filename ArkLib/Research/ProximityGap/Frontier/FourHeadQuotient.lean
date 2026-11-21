/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Four cubic heads on an order-eight quotient

The first two identities verify the coincidences not already visible from the
roots and the shared normalization. The label-separation lemma allows a single
field parameter to serve all coordinates outside the line of heads.
-/

namespace ProximityGap.FourHeadQuotient

section Identities
variable {R : Type*} [CommRing R]

/-- The three nonzero cubics before normalization, with z a primitive eighth root. -/
def first (z y : R) := (y - z ^ 3) * (y + z ^ 2) * (y + z ^ 3)
def second (z y : R) := (y - z ^ 3) * (y + z) * (y + z ^ 3)
def third (z y : R) := (y + 1) * (y + z) * (y + z ^ 2)

/-- Heads one and three, each normalized at z², coincide at z. -/
theorem eq_at_z {z : R} (hz : z ^ 4 = -1) :
    first z z * third z (z ^ 2) = third z z * first z (z ^ 2) := by
  unfold first third
  linear_combination (2*z^6 + 4*z^7 - 4*z^9 - 2*z^10) * hz

/-- Heads two and three, each normalized at z², coincide at one. -/
theorem eq_at_one {z : R} (hz : z ^ 4 = -1) :
    second z 1 * third z (z ^ 2) = third z 1 * second z (z ^ 2) := by
  unfold second third
  linear_combination (2*z^3 + 4*z^4 + 2*z^5 - 2*z^7 - 4*z^8 - 2*z^9) * hz

end Identities

open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Distinct affine functions on a finite field take distinct values simultaneously
at some parameter when the square of their number is smaller than the field. -/
theorem exists_injective_affine_labels (labels : Finset (F × F))
    (hq : labels.card * labels.card < Fintype.card F) :
    ∃ t : F, Set.InjOn (fun v : F × F => v.1 + t * v.2) (↑labels : Set (F × F)) := by
  classical
  let bad := (labels ×ˢ labels).image
    (fun v : (F × F) × (F × F) => (v.2.1 - v.1.1) / (v.1.2 - v.2.2))
  have hb : bad.card < (univ : Finset F).card := by
    exact card_image_le.trans_lt (by simpa only [card_product, card_univ] using hq)
  obtain ⟨t, _, ht⟩ := exists_mem_notMem_of_card_lt_card hb
  refine ⟨t, ?_⟩
  intro a ha b hb heq
  change a.1 + t * a.2 = b.1 + t * b.2 at heq
  by_cases h : a.2 = b.2
  · rw [h] at heq
    exact Prod.ext (add_right_cancel heq) h
  · exfalso
    apply ht
    apply mem_image.mpr
    refine ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, ?_⟩
    exact ((eq_div_iff (sub_ne_zero.mpr h)).mpr (by linear_combination heq)).symm

omit [Fintype F] [DecidableEq F] in
/-- If a head has value (x H v, H v), this received value gives the prescribed
translated scalar label. The identity is stated without dividing by H. -/
theorem off_line_agreement (x H v τ t : F) (hτ : τ ≠ v) :
    H * (x * τ - t) + (-x + t / (τ-v)) * (H * τ) =
      (x * (H*v)) + (-x + t / (τ-v)) * (H*v) := by
  field_simp [sub_ne_zero.mpr hτ]
  ring

/-- Exact counts for the eight fibers of length 2^27. Of the nonzero-multiplier
nodes, the half-fiber off the line contributes three labels per coordinate. -/
theorem first_prime_budgets :
    let s := 2 ^ 27
    let n := 8 * s
    let k := 4 * s
    let roots := 2 * (s / 2 - 1)
    let off := s / 2
    let ordinary := n - roots - off
    let core := roots + 4*s + (s - off)
    roots + 3*s + 1 < k ∧ k ≤ core ∧
    n - (core + 1) = 335544321 ∧
    ordinary + 3*off = n+2 ∧
    (4*n)^2 < 365375409332725729550921208179070755120141565953 ∧
    365375409332725729550921208179070755120141565953 < (n+2)*2^128 := by
  decide

#print axioms eq_at_z
#print axioms eq_at_one
#print axioms exists_injective_affine_labels
#print axioms off_line_agreement
#print axioms first_prime_budgets

end ProximityGap.FourHeadQuotient
