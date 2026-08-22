/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic

/-!
# Shallow natural-number certificates for products in `ZMod p`

Large products containing field inverses are expensive to reduce directly in
the Lean kernel.  This file supplies a certificate format that computes the
product recursively in `Nat` modulo `p`, then transports the result to `ZMod p`
with a proved cast identity.  Certificate checks have depth linear in the list
length and contain no field inversion.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.NatModProductCertificate

/-- Right-associated modular product of natural representatives. -/
def productMod (p : Nat) : List Nat -> Nat
  | [] => 1 % p
  | x :: xs => (x * productMod p xs) % p

theorem productMod_lt (p : Nat) (hp : 0 < p) (factors : List Nat) :
    productMod p factors < p := by
  cases factors <;> simp only [productMod] <;> exact Nat.mod_lt _ hp

/-- The natural modular evaluator agrees with multiplication in `ZMod p`. -/
theorem natCast_productMod (p : Nat) (factors : List Nat) :
    ((productMod p factors : Nat) : ZMod p) =
      List.prod (List.map (fun x : Nat => (x : ZMod p)) factors) := by
  induction factors with
  | nil => simp [productMod]
  | cons x xs ih => simp [productMod, ZMod.natCast_mod, ih]

/-- A checked natural result can be substituted directly for the corresponding
field product. -/
theorem zmod_product_eq_of_productMod_eq
    (p result : Nat) (factors : List Nat)
    (h : productMod p factors = result) :
    List.prod (List.map (fun x : Nat => (x : ZMod p)) factors) =
      (result : ZMod p) := by
  rw [← natCast_productMod, h]

end ArkLib.ProximityGap.Frontier.NatModProductCertificate

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.NatModProductCertificate
#print axioms natCast_productMod
#print axioms zmod_product_eq_of_productMod_eq
#print axioms productMod_lt
