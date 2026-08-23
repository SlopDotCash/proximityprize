/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Additive characters of a finite product factorize coordinate-wise (#389)

For `ψ : AddChar (ι → F) M` and the per-axis restrictions `ψ_i(x) := ψ(Pi.single i x)`:

> **`addChar_pi_factor`** — `ψ(e) = ∏_i ψ_i(e_i)`.

The structural input for the Fourier→Krawtchouk bridge (the Shaw operator = Krawtchouk-weighted
dual-MDS character sum). Built from scratch: the single-coordinate hom + `AddChar` sum→product.
Axiom-clean.
-/
set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.CharFactor

variable {ι F M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup F] [CommMonoid M]

/-- The single-coordinate additive hom `x ↦ Pi.single i x : F →+ (ι → F)`. -/
def singleHom (i : ι) : F →+ (ι → F) where
  toFun := fun x => Pi.single i x
  map_zero' := by ext j; simp [Pi.single_apply]
  map_add' := fun a b => by
    ext j; simp only [Pi.single_apply, Pi.add_apply]; split_ifs <;> simp

@[simp] theorem singleHom_apply (i : ι) (x : F) : singleHom i x = Pi.single i x := rfl

/-- An additive character sends a finite sum to the product of its values (the multiplicativity of
`AddChar` extended over `Finset.sum`). -/
theorem addChar_map_sum (ψ : AddChar F M) {κ : Type*} (s : Finset κ) (g : κ → F) :
    ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The per-axis restriction `ψ_i(x) = ψ(Pi.single i x)`, as an `AddChar F M`. -/
def axisChar (ψ : AddChar (ι → F) M) (i : ι) : AddChar F M :=
  ψ.compAddMonoidHom (singleHom i)

@[simp] theorem axisChar_apply (ψ : AddChar (ι → F) M) (i : ι) (x : F) :
    axisChar ψ i x = ψ (Pi.single i x) := by
  simp [axisChar]

/-- **Coordinate-wise factorization of an additive character of a finite product.**
`ψ(e) = ∏_i ψ_i(e_i)`. -/
theorem addChar_pi_factor (ψ : AddChar (ι → F) M) (e : ι → F) :
    ψ e = ∏ i, axisChar ψ i (e i) := by
  conv_lhs => rw [← Finset.univ_sum_single e]
  rw [addChar_map_sum ψ Finset.univ (fun i => Pi.single i (e i))]
  exact Finset.prod_congr rfl (fun i _ => by rw [axisChar_apply])

end ArkLib.ProximityGap.CharFactor

#print axioms ArkLib.ProximityGap.CharFactor.addChar_pi_factor
