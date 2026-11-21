/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FinCases
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Eight quadratic-character sums on the two named production subgroups -/

namespace ProximityGap.NamedCharacterBlocks
open ArkLib.ProximityGap
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
open Finset Polynomial

/-- The additive quadratic-character bit. At the diagonal the circulant uses zero. -/
def bit {p : ℕ} (x : ZMod p) : ZMod 2 :=
  if x ^ ((p-1)/2) = -1 then 1 else 0

private theorem bit_prod {p : ℕ} [Fact p.Prime] (hodd : (p-1)/2*2 = p-1)
    (hone : (1 : ZMod p) ≠ -1) {α : Type*} (s : Finset α) (f : α → ZMod p)
    (hn : ∏ i ∈ s, f i ≠ 0) : ∑ i ∈ s, bit (f i) = bit (∏ i ∈ s, f i) := by
  classical
  have dich (z : ZMod p) (hz : z ≠ 0) : z^((p-1)/2) = 1 ∨ z^((p-1)/2) = -1 := by
    apply sq_eq_one_iff.mp
    rw [← pow_mul, hodd, ZMod.pow_card_sub_one_eq_one hz]
  induction s using Finset.induction_on with
  | empty => simp [bit, hone]
  | @insert a s ha ih =>
    rw [prod_insert ha, mul_ne_zero_iff] at hn
    rw [sum_insert ha, prod_insert ha, ih hn.2]
    rcases dich _ hn.1 with h | h <;> rcases dich _ hn.2 with k | k <;>
      simp [bit, mul_pow, h, k, hone, show (1+1 : ZMod 2) = 0 by decide]

private abbrev m : ℕ := 2^27

/-- The factor used to compute the quadratic character at exponent 8i+r.
The diagonal factor is one and hence contributes a zero bit. -/
def factor {p : ℕ} (g : ZMod p) (r i : ℕ) : ZMod p :=
  if r = 0 ∧ i = 0 then 1 else 1-(g^8)^i*g^r

/-- The explicit off-diagonal exponent in the cyclic matrix. -/
theorem factor_eq {p : ℕ} (g : ZMod p) (r i : ℕ) :
    factor g r i = if r = 0 ∧ i = 0 then 1 else 1-g^(8*i+r) := by
  simp [factor, pow_add, pow_mul]

/-- Product of a whole residue class, with the diagonal factor omitted. -/
def blockValue {p : ℕ} (g : ZMod p) (r : ℕ) : ZMod p :=
  if r = 0 then (m : ZMod p) else 1-(g^r)^m

private theorem product_zero {p j : ℕ} [Fact p.Prime] (g : ZMod p)
    (hp : IsPrimitiveRoot (g^8) (j+1)) :
    ∏ i ∈ range (j+1), factor g 0 i = ((j+1 : ℕ) : ZMod p) := by
  rw [prod_range_succ']
  simpa [factor, Nat.cast_add, Nat.cast_one] using hp.prod_one_sub_pow_eq_order

private theorem product_nonzero {p t : ℕ} [Fact p.Prime] (g : ZMod p) (r : ℕ)
    (hp : IsPrimitiveRoot (g^8) t) (ht : 0 < t) (hr : r ≠ 0) :
    ∏ i ∈ range t, factor g r i = 1-(g^r)^t := by
  have he := congrArg (Polynomial.eval (1 : ZMod p))
    (X_pow_sub_C_eq_prod hp ht (rfl : (g^r)^t = (g^r)^t))
  simpa [factor, hr, eval_prod] using he.symm

private theorem product_block {p : ℕ} [Fact p.Prime] (g : ZMod p)
    (hg : IsPrimitiveRoot g (2^30)) (r : ℕ) :
    ∏ i ∈ range m, factor g r i = blockValue g r := by
  have hp : IsPrimitiveRoot (g^8) m := hg.pow_of_dvd (p := 8) (by decide) (by decide)
  by_cases hr : r = 0
  · subst r
    exact product_zero (j := 134217727) g hp
  · rw [blockValue, if_neg hr]
    exact product_nonzero g r hp (by decide) hr

/-- Multiplying the whole coset reduces each billion-scale cyclic sum to one Euler test. -/
theorem sum_block {p : ℕ} [Fact p.Prime] (g : ZMod p) (hg : IsPrimitiveRoot g (2^30))
    (hodd : (p-1)/2*2 = p-1) (hone : (1 : ZMod p) ≠ -1) (r : Fin 8)
    (hz : blockValue g r ≠ 0) :
    ∑ i : Fin m, bit (factor g r i) = bit (blockValue g r) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => bit (factor g r i)) m]
  rw [← product_block g hg] at hz ⊢
  exact bit_prod hodd hone _ _ hz

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


private theorem table_implies_sums {p : ℕ} [Fact p.Prime] (g w : ZMod p)
    (hg : orderOf g = 2^30) (hw : g^m = w)
    (hodd : (p-1)/2*2 = p-1) (hone : (1 : ZMod p) ≠ -1)
    (table : ∀ r : Fin 8, let a : ZMod p := if r.val = 0 then m else 1-w^r.val
      a ≠ 0 ∧ bit a = (r.val : ZMod 2)) (r : Fin 8) :
    ∑ i : Fin m, bit (factor g r i) = (r.val : ZMod 2) := by
  have hb := table r
  have hval : blockValue g r = (if r.val = 0 then (m : ZMod p) else 1-w^r.val) := by
    rw [blockValue, pow_right_comm g r.val m, hw]
  rw [← hval] at hb
  rw [sum_block g (hg ▸ IsPrimitiveRoot.orderOf g) hodd hone r hb.1, hb.2]

section
open PrizeShapePrimeP30
local instance : Fact P.Prime := ⟨prime_P⟩

/-- All eight coset parities at the first named production prime. -/
theorem first_block_sums (r : Fin 8) :
    ∑ i : Fin (2^27), bit (factor g r i) = (r.val : ZMod 2) := by
  let w : ZMod P := 18943363311336672863882327061011457227257409586
  apply table_implies_sums g w orderOf_g
  · rw [← binaryPow_eq_pow]
    decide
  · decide
  · decide
  · simp only [bit, ← binaryPow_eq_pow]
    decide
end

section
open PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩

/-- All eight coset parities at the second named production prime. -/
theorem second_block_sums (r : Fin 8) :
    ∑ i : Fin (2^27), bit (factor g r i) = (r.val : ZMod 2) := by
  let w : ZMod P := 684944486517762849622048856798491974355853664681
  apply table_implies_sums g w orderOf_g
  · rw [← binaryPow_eq_pow]
    decide
  · decide
  · decide
  · simp only [bit, ← binaryPow_eq_pow]
    decide
end

#print axioms first_block_sums
#print axioms second_block_sums
end ProximityGap.NamedCharacterBlocks
