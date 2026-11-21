/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskNorms
import ArkLib.Research.ProximityGap.Frontier.QuotientMaskBudget

/-! # Product buckets and the two squared locator evaluations -/

namespace ProximityGap.QuotientMaskLocator
open Finset QuotientMaskSelections QuotientMaskBudget QuotientMaskPositions QuotientMaskNorms
open scoped BigOperators

def exponentSum (m : M) := ∑ p ∈ selected 4 m, (ordinary p).val

def bucket (m : M) : Fin 32 :=
  ⟨exponentSum m % 64 / 2, by have := Nat.mod_lt (exponentSum m) (by decide : 0<64); omega⟩

def signs : (d : ℕ) → Leaves ℤ d
  | 0 => (-1 : ℤ)
  | d+1 => (signs d,signs d)

private theorem parity_node (p : Position 4) :
    (-1 : ℤ)^(ordinary p).val = nodeValue false 4 (signs 4) (block 4 (signs 4)) p ∧
    (-1 : ℤ)^(ordinary p).val = nodeValue true 4 (signs 4) (block 4 (signs 4)) p := by
  revert p
  decide +kernel

private theorem mode_even (i : Fin 4) : powered 4 (signs 4) (modes i) = 1 := by
  revert i
  decide +kernel

theorem even_exponent (m : M) (hs : (∃ i, (signatures 4 m).1=modes i) ∨
    (∃ i, (signatures 4 m).2=modes i)) : Even (exponentSum m) := by
  apply (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp
  rw [exponentSum, ← prod_pow_eq_pow_sum]
  obtain ⟨hp,hm⟩ := norm_products 4 (signs 4) m
  rcases hs with ⟨i,hi⟩ | ⟨i,hi⟩
  · rw [prod_congr rfl (fun p _ => (parity_node p).1),hp,hi,mode_even]
  · rw [prod_congr rfl (fun p _ => (parity_node p).2),hm,hi,mode_even]

theorem residue_eq (m n : M) (h : bucket m=bucket n) (hm : Even (exponentSum m))
    (hn : Even (exponentSum n)) : exponentSum m%64=exponentSum n%64 := by
  have h' := congrArg Fin.val h
  change exponentSum m%64/2 = exponentSum n%64/2 at h'
  obtain ⟨a,ha⟩ := hm
  obtain ⟨b,hb⟩ := hn
  omega

variable {F : Type} [Field F]

def posNorm (z : F) (i : Fin 64) : F := (1-z^i.val)*(1-z^(64-i.val))
def negNorm (z : F) (i : Fin 64) : F := (1+z^i.val)*(1+z^(64-i.val))

def weights (z : F) : (d : ℕ) → ℕ → Leaves F d
  | 0, j => posNorm (F:=F) z (Fin.ofNat 64 j)
  | d+1, j => (weights z d (j/2),weights z d ((64-j)/2))

/-- A field-specific certificate checks exactly 62 pairs of factor identities. -/
def Valid (z : F) : Prop := ∀ p : Position 4,
  posNorm z (ordinary p) = nodeValue false 4 (weights z 4 16) (block 4 (weights z 4 16)) p ∧
  negNorm z (ordinary p) = nodeValue true 4 (weights z 4 16) (block 4 (weights z 4 16)) p

def loc (z a : F) (m : M) : F := ∏ p ∈ selected 4 m, (a-z^(ordinary p).val)

private theorem root_inverse (z : F) (hz : z^64=1) (i : Fin 64) :
    z^i.val*z^(64-i.val)=1 := by rw [←pow_add, Nat.add_sub_of_le i.isLt.le,hz]

private theorem squares (z : F) (hz : z^64=1) (i : Fin 64) :
    (1-z^i.val)^2=(-z^i.val)*posNorm z i ∧
    (-1-z^i.val)^2=z^i.val*negNorm z i := by
  have h := root_inverse z hz i
  unfold posNorm negNorm
  constructor
  · linear_combination (z^i.val-1)*h
  · linear_combination -(1+z^i.val)*h

theorem loc_squares (z : F) (hz : z^64=1) (valid : Valid z) (m : M) :
    (loc z 1 m)^2=(-1 : F)^(count 4 m) * z^(exponentSum m) *
      powered 4 (weights z 4 16) (signatures 4 m).1 ∧
    (loc z (-1) m)^2=z^(exponentSum m) * powered 4 (weights z 4 16) (signatures 4 m).2 := by
  have hn := norm_products 4 (weights z 4 16) m
  unfold loc
  rw [← prod_pow, ← prod_pow]
  constructor
  · rw [prod_congr rfl (fun p _ => (squares z hz (ordinary p)).1), prod_mul_distrib, prod_neg,
      selected_card, prod_pow_eq_pow_sum, prod_congr rfl (fun p _ => (valid p).1), hn.1]
    rfl
  · rw [prod_congr rfl (fun p _ => (squares z hz (ordinary p)).2), prod_mul_distrib,
      prod_pow_eq_pow_sum, prod_congr rfl (fun p _ => (valid p).2), hn.2]
    rfl

theorem root_power (z : F) (hz : z^64=1) (m : ℕ) : z^m = z^(m%64) := by
  conv_lhs => rw [← Nat.mod_add_div m 64]
  rw [pow_add,pow_mul,hz,one_pow,mul_one]

theorem anchor_classes (z : F) (hz : z^64=1) (valid : Valid z) (m n : M)
    (hm : count 4 m=33) (hn : count 4 n=33) (hb : bucket m=bucket n) (i : Fin 4) :
    ((signatures 4 m).1=modes i → (signatures 4 n).1=modes i → (loc z 1 m)^2=(loc z 1 n)^2) ∧
    ((signatures 4 m).2=modes i → (signatures 4 n).2=modes i → (loc z (-1) m)^2=(loc z (-1) n)^2) := by
  have h1 := loc_squares z hz valid m
  have h2 := loc_squares z hz valid n
  constructor
  · intro h1s h2s
    have he := residue_eq m n hb (even_exponent m (.inl ⟨i,h1s⟩)) (even_exponent n (.inl ⟨i,h2s⟩))
    rw [h1.1,h2.1,hm,hn,h1s,h2s,root_power z hz (exponentSum m), root_power z hz (exponentSum n), he]
  · intro h1s h2s
    have he := residue_eq m n hb (even_exponent m (.inr ⟨i,h1s⟩)) (even_exponent n (.inr ⟨i,h2s⟩))
    rw [h1.2,h2.2,h1s,h2s,root_power z hz (exponentSum m), root_power z hz (exponentSum n), he]

#print axioms anchor_classes
#print axioms even_exponent
end ProximityGap.QuotientMaskLocator
