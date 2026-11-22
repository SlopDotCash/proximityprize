/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Research.ProximityGap.KKH26RegimeSplit

/-! # Three cubic seed polynomials on the second named smooth domain -/

open Finset Polynomial
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open ArkLib.ProximityGap.BinaryPower
open ProximityGap.KKH26RegimeSplit

namespace ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed

local instance : Fact P.Prime := ⟨prime_P⟩

abbrev N : ℕ := 2 ^ 30
abbrev F := ZMod P
abbrev dom : Fin N ↪ F := powDomain g orderOf_g (ne_zero_of_orderOf_eq orderOf_g)

/-- Primitive sixteenth root in the second named field. -/
def w : F := 262862187708019762731226873972141088659660725826

/-- Primitive thirty-second root in the second named field. -/
def z : F := 592700706662122438502135184501773543141949939930

/-- Three seed evaluations before multiplication by the common locator. -/
def values (u : F) : Fin 3 → F :=
  ![0, (u-1)*(u-w)*(u-w^8), w^2*((u-w^2)*(u-w^9)*(u-w^10))]

private noncomputable def factor (s : ℕ) (a : F) : F[X] :=
  (Polynomial.X : F[X])^s - Polynomial.C a

private noncomputable def cubic (s : ℕ) (a b c : F) : F[X] :=
  factor s a * factor s b * factor s c

/-- The scalar variable in the cubic seed is the power map of exponent `s`. -/
noncomputable def seed (s : ℕ) : Fin 3 → F[X] :=
  ![0, cubic s 1 w (w^8), C (w^2) * cubic s (w^2) (w^9) (w^10)]

theorem degree (s : ℕ) (j : Fin 3) : (seed s j).natDegree ≤ 3*s := by
  have h (a : F) : (factor s a).natDegree ≤ s := (natDegree_sub_le _ _).trans (by simp)
  have h3 (a b c : F) : (cubic s a b c).natDegree ≤ 3*s := by
    have hab := (natDegree_mul_le (p := factor s a) (q := factor s b)).trans (add_le_add (h a) (h b))
    have ht := (natDegree_mul_le (p := factor s a * factor s b) (q := factor s c)).trans
      (add_le_add hab (h c))
    unfold cubic
    omega
  fin_cases j
  · simp [seed]
  · exact h3 1 w (w^8)
  · change (C (w^2) * cubic s (w^2) (w^9) (w^10)).natDegree ≤ 3*s
    apply natDegree_mul_le.trans
    rw [natDegree_C, zero_add]
    exact h3 (w^2) (w^9) (w^10)

private theorem eval_seed (s : ℕ) (j : Fin 3) (a : F) :
    (seed s j).eval a = values (a^s) j := by
  fin_cases j <;> simp [seed, cubic, factor, values]

/-- Pair classes of the cubic pencil indexed by the missing head. -/
abbrev bucket := SmoothFourHeadFibers.bucket

/-- The field evaluations on either smooth quotient determine all pair coincidences. -/
private theorem table16 : ∀ i : Fin 16, ∀ a b : Fin 3,
    values (w^i.val) a = values (w^i.val) b ↔ SmoothFourHeadFibers.coincide (bucket 1 i.val) a b := by
  decide

private theorem table32 : ∀ i : Fin 32, ∀ a b : Fin 3,
    values (z^i.val) a = values (z^i.val) b ↔ SmoothFourHeadFibers.coincide (bucket 2 i.val) a b := by
  decide

private theorem eval_power (s q : ℕ) (u : F) (x : Fin N) (hs : PrizeShapePrimeP30Second.g ^ s = u) (hu : u^q = 1) :
    (dom x)^s = u^(x.val%q) := by
  change (PrizeShapePrimeP30Second.g^x.val)^s = _
  rw [← pow_mul, Nat.mul_comm, pow_mul, hs]
  calc
    u^x.val = u^(x.val%q + q*(x.val/q)) := congrArg (u^·) (Nat.mod_add_div _ _).symm
    _ = _ := by rw [pow_add, pow_mul, hu, one_pow, mul_one]

/-- At a production site the three eighth-rate seeds depend only on the index modulo 32. -/
theorem eval_eighth_seed (i : Fin 3) (x : Fin N) :
    (seed 33554432 i).eval (dom x) = values (z ^ (x.val % 32)) i := by
  rw [eval_seed, eval_power 33554432 32 z x (by rw [← binaryPow_eq_pow]; decide) (by decide)]

/-- Fiber data of the eighth-rate attack. -/
theorem eighth :
    (∀ j, (univ.filter (fun x : Fin N => bucket 2 (x.val%32) = j)).card =
      (![100663296,100663296,100663296,771751936] : Fin 4 → ℕ) j) ∧
    (∀ x i j, (seed 33554432 i).eval (dom x) = (seed 33554432 j).eval (dom x) ↔
      SmoothFourHeadFibers.coincide (bucket 2 (x.val%32)) i j) := by
  constructor
  · intro j
    change (univ.filter (fun x : Fin (33554432*32) => bucket 2 x.modNat.val = j)).card = _
    rw [SmoothFourHeadFibers.count_blocks (fun r : Fin 32 => bucket 2 r.val) j]
    fin_cases j <;> decide
  · intro x i j
    rw [eval_seed, eval_seed, eval_power 33554432 32 z x (by rw [← binaryPow_eq_pow]; decide) (by decide)]
    exact table32 ⟨_, Nat.mod_lt _ (by decide)⟩ i j

/-- Fiber data of the quarter-rate attack. -/
theorem quarter :
    (∀ j, (univ.filter (fun x : Fin N => bucket 1 (x.val%16) = j)).card =
      (![201326592,201326592,201326592,469762048] : Fin 4 → ℕ) j) ∧
    (∀ x i j, (seed 67108864 i).eval (dom x) = (seed 67108864 j).eval (dom x) ↔
      SmoothFourHeadFibers.coincide (bucket 1 (x.val%16)) i j) := by
  constructor
  · intro j
    change (univ.filter (fun x : Fin (67108864*16) => bucket 1 x.modNat.val = j)).card = _
    rw [SmoothFourHeadFibers.count_blocks (fun r : Fin 16 => bucket 1 r.val) j]
    fin_cases j <;> decide
  · intro x i j
    rw [eval_seed, eval_seed, eval_power 67108864 16 w x (by rw [← binaryPow_eq_pow]; decide) (by decide)]
    exact table16 ⟨_, Nat.mod_lt _ (by decide)⟩ i j

end ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed.eighth
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeSmoothSeed.quarter
