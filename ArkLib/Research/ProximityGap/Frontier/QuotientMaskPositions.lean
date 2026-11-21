/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskSelections

/-! # The ordinary quotient roots selected by a dyadic mask -/

namespace ProximityGap.QuotientMaskPositions

open Finset QuotientMaskSelections QuotientSignatureCensus

/-- Each node has two ordinary root positions. -/
def Position : ℕ → Type
  | 0 => Bool
  | d+1 => Bool ⊕ (Position d ⊕ Position d)

instance posFintype : (d : ℕ) → Fintype (Position d)
  | 0 => inferInstanceAs (Fintype Bool)
  | d+1 => let _ := posFintype d; inferInstanceAs (Fintype (Bool ⊕ (Position d ⊕ Position d)))

instance posDec : (d : ℕ) → DecidableEq (Position d)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | d+1 => let _ := posDec d; inferInstanceAs (DecidableEq (Bool ⊕ (Position d ⊕ Position d)))

/-- Two bits of a choice, in the positive and inverse orientation. -/
def bit (c : Choice) (b : Bool) : Bool := if b then decide (2 ≤ c.val) else decide (c.val % 2 = 1)

def chosen : (d : ℕ) → Mask d → Position d → Bool
  | 0, c, b => bit c b
  | _+1, (a,_,_), .inl b => bit a b
  | d+1, (_,l,_), .inr (.inl p) => chosen d l p
  | d+1, (_,_,r), .inr (.inr p) => chosen d r p

theorem chosen_injective (d : ℕ) : Function.Injective (chosen d) := by
  have inject : Function.Injective bit := by decide
  induction d with
  | zero => exact inject
  | succ d ih =>
    rintro ⟨a,l,r⟩ ⟨b,v,w⟩ he
    have ha : a=b := inject (funext fun t => congrFun he (.inl t))
    have hl : l=v := ih (funext fun t => congrFun he (.inr (.inl t)))
    have hr : r=w := ih (funext fun t => congrFun he (.inr (.inr t)))
    rw [ha,hl,hr]

private def oriented (j : ℕ) (b : Bool) : Fin 64 := Fin.ofNat 64 (if b then 64-j else j)

/-- General exponents in an order-64 quotient. Opposite orientations are indexed modulo 64. -/
def exponent : (d : ℕ) → ℕ → Position d → Fin 64
  | 0, j, b => oriented j b
  | _+1, j, .inl b => oriented j b
  | d+1, j, .inr (.inl p) => exponent d (j/2) p
  | d+1, j, .inr (.inr p) => exponent d ((64-j)/2) p

/-- These 62 positions are all distinct and avoid both anchor exponents. -/
def ordinary : Position 4 ↪ Fin 64 := ⟨exponent 4 16, by decide +kernel⟩

theorem ordinary_nonanchor (p : Position 4) : ordinary p ≠ 0 ∧ ordinary p ≠ 32 := by
  revert p
  decide +kernel

def selected (d : ℕ) (m : Mask d) : Finset (Position d) := univ.filter (fun p => chosen d m p=true)

theorem selected_injective (d : ℕ) : Function.Injective (selected d) := by
  intro m n he
  apply chosen_injective d
  funext p
  have h : p ∈ selected d m ↔ p ∈ selected d n := he ▸ Iff.rfl
  simp [selected] at h
  exact h

/-- Distinct masks give distinct ordinary quotient subsets. -/
def subset (m : Mask 4) : Finset (Fin 64) := (selected 4 m).map ordinary

theorem subset_injective : Function.Injective subset := by
  intro m n e
  exact selected_injective 4 ((Finset.map_inj ..).mp e)

theorem omits (m : Mask 4) : 0 ∉ subset m ∧ 32 ∉ subset m := by
  constructor
  · intro h
    obtain ⟨p,_,e⟩ := mem_map.mp h
    exact (ordinary_nonanchor p).1 e
  · intro h
    obtain ⟨p,_,e⟩ := mem_map.mp h
    exact (ordinary_nonanchor p).2 e

/-- Summing an arbitrary selected-site weight splits at each of the two children. -/
theorem selected_card (d : ℕ) (m : Mask d) : (selected d m).card = count d m := by
  have pair (a : Choice) : (∑ b : Bool, if bit a b then 1 else 0 : ℕ) = occ a := by
    revert a
    decide
  have repr (k : ℕ) (n : Mask k) : (selected k n).card =
      ∑ p : Position k, if chosen k n p = true then 1 else 0 := by
    exact (sum_boole _ _).symm
  induction d with
  | zero =>
    rw [repr]
    exact pair m
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    refine (repr (d+1) (a,l,r)).trans ?_
    change (∑ x : Bool ⊕ (Position d ⊕ Position d),
      if chosen (d+1) (a,l,r) x = true then 1 else 0) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    change (∑ b : Bool, if bit a b = true then 1 else 0) +
      ((∑ x : Position d, if chosen d l x = true then 1 else 0) +
       (∑ x : Position d, if chosen d r x = true then 1 else 0)) = _
    rw [pair, ← repr, ← repr, ih, ih]
    rfl


theorem subset_card (m : Mask 4) : (subset m).card = count 4 m := by
  rw [subset, card_map, selected_card]

#print axioms subset_card
#print axioms subset_injective
end ProximityGap.QuotientMaskPositions
