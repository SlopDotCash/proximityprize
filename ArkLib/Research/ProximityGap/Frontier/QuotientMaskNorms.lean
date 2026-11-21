/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskPositions

/-! # Products of reciprocal factors for the two anchor signatures -/

namespace ProximityGap.QuotientMaskNorms

open Finset QuotientMaskSelections QuotientMaskPositions QuotientSignatureCensus
variable {A : Type*} [CommMonoid A]

def block : (d : ℕ) → Leaves A d → A
  | 0, v => v
  | d+1, (l,r) => block d l * block d r

private def onePower (v : A) (n : ℕ) : A := v^n

def powered : (d : ℕ) → Leaves A d → Leaves ℕ d → A
  | 0, v, n => onePower v n
  | d+1, (l,r), (n,m) => powered d l n * powered d r m

/-- The factor at a node comes from all leaves below it. At the opposite
anchor sibling nodes exchange their factors. -/
def nodeValue (rev : Bool) : (d : ℕ) → Leaves A d → A → Position d → A
  | 0, _, top, _ => top
  | _+1, _, top, .inl _ => top
  | d+1, (l,r), _, .inr (.inl p) => nodeValue rev d l (if rev then block d r else block d l) p
  | d+1, (l,r), _, .inr (.inr p) => nodeValue rev d r (if rev then block d l else block d r) p

def descendants (rev : Bool) : (d : ℕ) → Leaves A d → Mask d → A
  | 0, _, _ => 1
  | d+1, (u,v), (_,l,r) =>
    (if rev then block d v else block d u) ^ occ (root d l) * descendants rev d u l *
      ((if rev then block d u else block d v) ^ occ (root d r) * descendants rev d v r)

private theorem pair_product (a : Choice) (z : A) :
    (∏ b : Bool, if bit a b then z else 1) = z^occ a := by
  fin_cases a <;> simp [bit, occ]

theorem product_nodes (rev : Bool) (d : ℕ) (v : Leaves A d) (top : A) (m : Mask d) :
    (∏ p ∈ selected d m, nodeValue rev d v top p) =
      top ^ occ (root d m) * descendants rev d v m := by
  have repr (k : ℕ) (v : Leaves A k) (a : A) (n : Mask k) :
      (∏ p ∈ selected k n, nodeValue rev k v a p) =
      ∏ p : Position k, if chosen k n p = true then nodeValue rev k v a p else 1 := by
    exact Finset.prod_filter ..
  induction d generalizing top with
  | zero =>
    refine (repr 0 v top m).trans ?_
    change (∏ b : Bool, if bit m b then top else 1) = top^occ m * 1
    exact (pair_product (A:=A) m top).trans (mul_one _).symm
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    rcases v with ⟨u,v⟩
    refine (repr (d+1) (u,v) top (a,l,r)).trans ?_
    change (∏ p : Bool ⊕ (Position d ⊕ Position d),
      if chosen (d+1) (a,l,r) p = true then nodeValue rev (d+1) (u,v) top p else 1) = _
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    change (∏ b : Bool, if bit a b then top else 1) *
      ((∏ p : Position d, if chosen d l p = true then nodeValue rev d u
        (if rev then block d v else block d u) p else 1) *
       (∏ p : Position d, if chosen d r p = true then nodeValue rev d v
        (if rev then block d u else block d v) p else 1)) = _
    rw [pair_product, ← repr, ← repr, ih, ih]
    rfl

private theorem trace_products (d : ℕ) (v : Leaves A d) (m : Mask d) (x y : ℕ) :
    powered d v (traces d x y m).1 = block d v ^ x * descendants false d v m ∧
    powered d v (traces d x y m).2 = block d v ^ y * descendants true d v m := by
  induction d generalizing x y with
  | zero => exact ⟨(mul_one _).symm, (mul_one _).symm⟩
  | succ d ih =>
    rcases m with ⟨a,l,r⟩
    rcases v with ⟨u,v⟩
    obtain ⟨h₁,h₂⟩ := ih u l (x+occ (root d l)) (y+occ (root d r))
    obtain ⟨h₃,h₄⟩ := ih v r (x+occ (root d r)) (y+occ (root d l))
    constructor <;> simp only [traces, powered, block, descendants, Bool.false_eq_true, Bool.true_eq,
      ite_false, ite_true, h₁, h₂, h₃, h₄, mul_pow, pow_add] <;> ac_rfl

theorem norm_products (d : ℕ) (v : Leaves A d) (m : Mask d) :
    (∏ p ∈ selected d m, nodeValue false d v (block d v) p) = powered d v (signatures d m).1 ∧
    (∏ p ∈ selected d m, nodeValue true d v (block d v) p) = powered d v (signatures d m).2 := by
  rw [product_nodes, product_nodes]
  have h := trace_products d v m (occ (root d m)) (occ (root d m))
  exact ⟨h.1.symm,h.2.symm⟩

#print axioms norm_products
end ProximityGap.QuotientMaskNorms
