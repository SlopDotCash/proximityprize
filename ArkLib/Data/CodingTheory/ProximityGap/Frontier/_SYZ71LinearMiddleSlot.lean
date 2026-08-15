/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ47GeometricBalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ50WitnessRealizability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ70FirstOpenMiddleSlot

/-!
# SYZ71 — the first middle slot is a linear-cofactor syzygy, and it is on-domain

## The question

SYZ70 localised the first nonempty balanced middle band to the singleton
`middleBand 6 6 6 δ₁ ↔ δ₁ = 7`, read by the convention bridge as a **degree-`1` cofactor**
syzygy of three degree-`6` polynomials.  Two hopes sit on that slot:

1. *Algebraic degeneration*: a product-degree-`7` syzygy might collapse to a two-term
   relation or a constant-cofactor (floor-attained) relation.
2. *On-domain emptiness*: even if the algebra is healthy, perhaps no such triple has
   roots on `μ_n` at the first band-realizable size `n = 20`.

## What is proved here (axiom-clean)

1. **Two-term collapse is impossible at this slot.**  A vanished cofactor on a pairwise-coprime
   pair costs product-degree `≥ 12` (SYZ47).  So every product-degree-`≤ 7` syzygy of a
   sextic triple uses all three slots.
2. **Degree window.**  Slot product-degree `≤ 7` and `deg Wᵢ = 6` force every cofactor to
   have degree `≤ 1`.  If some cofactor is genuinely linear, the max slot product is `7`
   and the syzygy occupies the SYZ70 slot (`middleBand 6 6 6 7`).
3. **Möbius form.**  On any point where `W_AC` and `s_BC` are nonzero, the combination
   `s_AC W_AC + s_BC W_BC` vanishes iff `W_BC/W_AC` equals the Möbius value
   `−s_AC/s_BC`.  This is the linear analogue of SYZ49's constant-ratio level set.
4. **Assembly.**  If the linear combination equals `s_AB · W_AB`, a three-term linear
   syzygy exists.  Combined with (2) this is a middle-slot occupant.
5. **Polytope.**  The first band-realizable home of `(6,6,6)` is `k = 10`, `t = 2`,
   `n = 20` (`Realizable 6 6 6 2 10`).  The whole-subgroup `μ₁₈ = μ_{3·6}` is
   **not** realizable (`n = 18 < 19 = 3d+1`), the same one-point shortfall SYZ50
   recorded for `(4,4,4)` on `μ₁₂`.

## Probe (not a Lean theorem)

`scripts/probes/probe_syz71_linear_middle_slot.py` finds on-domain occupants at the
first realizable size.  Verified witness over `μ₂₀ ⊂ 𝔽₄₁` (generator `2`):

* `S_AC = {1,2,23,25,37,39}`, `S_BC = {5,8,10,16,18,36}`, `S_AB = {4,9,21,31,33,40}`
* leftover triple region `T = {20,32}` (size `2`)
* kernel `(s_AC, s_BC) = (29 + 10 X,\; 30 + X)`, rank `3`, `deg P = 7`
* `P` vanishes on `S_AB` and not on `T`; all three slot products equal `7`

So hope (2) is **false** at the Venn/counting level: the first middle slot *is*
on-domain, with room for the forced nonempty `T`.  The remaining gate is the same
one SYZ50 left for the constant `(4,4,4)` family — the over-budget-stack lift
(SYZ42), not emptiness of this slot on `μ_n`.

The explicit `𝔽₄₁` arithmetic is **not** replayed in Lean (`native_decide` would
leave the axiom surface).  The probe is the witness; the theorems below are the
interface it occupies.

## What is not claimed

CORE remains OPEN / ON-BGK.  Occupying the slot on-domain does not discharge
`UniformSylvesterInjective` or production `δ*`.  It **narrows** the residual:
the first middle slot is not an empty combinatorial cell.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ71

open Polynomial
open ArkLib.ProximityGap

/-! ## 1. Two-term collapse cannot live in the first slot -/

/-- **Vanished slot ⟹ product-degree `≥ 12`.**  If `s_AB = 0` on a pairwise-coprime
sextic pair `(W_AC, W_BC)`, the residual two-term syzygy costs at least
`deg W_AC + deg W_BC = 12` in the carrying slot.  Hence no product-degree-`≤ 7`
syzygy can drop a slot. -/
theorem vanished_slot_product_ge_twelve
    {K : Type*} [Field K] (WAC WBC sAC sBC : K[X])
    (hcop : IsCoprime WAC WBC)
    (hWAC : WAC ≠ 0) (hWBC : WBC ≠ 0)
    (hdegAC : WAC.natDegree = 6) (hdegBC : WBC.natDegree = 6)
    (hsyz : WAC * sAC + WBC * sBC = 0)
    (hnz : ¬ (sAC = 0 ∧ sBC = 0)) :
    12 ≤ (WAC * sAC).natDegree ∨ 12 ≤ (WBC * sBC).natDegree := by
  have hsBC : sBC ≠ 0 := by
    rintro rfl
    have h0 : WAC * sAC = 0 := by simpa using hsyz
    rcases mul_eq_zero.mp h0 with h | h
    · exact hWAC h
    · exact hnz ⟨h, rfl⟩
  have hge := SYZ47.two_term_product_degree_ge WAC WBC sAC sBC hcop hsyz hWBC hsBC
  have : (WBC * sBC).natDegree = WBC.natDegree + sBC.natDegree :=
    natDegree_mul hWBC hsBC
  omega

/-! ## 2. Degree window: product `≤ 7` on a sextic is a linear cofactor -/

/-- **Slot bound ⟹ cofactor degree `≤ 1`.**  If `deg W = 6` and the slot product-degree
is `≤ 7`, then either the cofactor vanishes or it has degree `≤ 1`. -/
theorem slot_le_seven_cofactor_le_one
    {K : Type*} [Field K] (W s : K[X])
    (hW : W ≠ 0) (hdeg : W.natDegree = 6)
    (hslot : (W * s).natDegree ≤ 7) :
    s = 0 ∨ s.natDegree ≤ 1 := by
  refine or_iff_not_imp_left.mpr ?_
  intro hs
  have hmul : (W * s).natDegree = W.natDegree + s.natDegree := natDegree_mul hW hs
  omega

/-- **A genuinely linear slot has product-degree `7`.** -/
theorem linear_slot_product_eq_seven
    {K : Type*} [Field K] (W s : K[X])
    (hW : W ≠ 0) (hs : s ≠ 0)
    (hWdeg : W.natDegree = 6) (hsdeg : s.natDegree = 1) :
    (W * s).natDegree = 7 := by
  have hmul : (W * s).natDegree = W.natDegree + s.natDegree := natDegree_mul hW hs
  omega

/-- **The SYZ70 slot, from a linear product-degree.**  A balanced sextic with
minimal syzygy product-degree `7` is exactly the first middle slot. -/
theorem product_seven_is_first_slot :
    SYZ59.middleBand 6 6 6 7 :=
  SYZ70.first_balanced_middle_occupied

/-- **Linear product-degree occupies the middle, not the floor.**  Floor-attained
is `δ₁ = 6`; the linear slot is `δ₁ = 7`. -/
theorem linear_slot_not_floor :
    ¬ SYZ59.middleBand 6 6 6 6 :=
  SYZ70.first_slot_not_floor_attained

/-! ## 3. Möbius form of a linear combination -/

/-- **Root ⟺ Möbius value.**  At a point where `W_AC` and `s_BC` are nonzero,
`s_AC W_AC + s_BC W_BC` vanishes iff `W_BC / W_AC = − s_AC / s_BC`.  For linear
cofactors the right-hand side is a Möbius transformation — the linear analogue
of SYZ49 `combination_isRoot_iff_ratio`. -/
theorem linear_combo_isRoot_iff_mobius
    {K : Type*} [Field K] (WAC WBC sAC sBC : K[X]) (r : K)
    (_hWAC : WAC.eval r ≠ 0) (hsBC : sBC.eval r ≠ 0) :
    (sAC * WAC + sBC * WBC).IsRoot r ↔
      WBC.eval r = (-sAC.eval r / sBC.eval r) * WAC.eval r := by
  unfold Polynomial.IsRoot
  rw [eval_add, eval_mul, eval_mul]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- **Linear combination degree bound.**  Cofactors of degree `≤ 1` and sextic
slots give `deg(s_AC W_AC + s_BC W_BC) ≤ 7`. -/
theorem linear_combo_natDegree_le
    {K : Type*} [Field K] (WAC WBC sAC sBC : K[X])
    (hsAC : sAC.natDegree ≤ 1) (hsBC : sBC.natDegree ≤ 1)
    (hWAC : WAC.natDegree ≤ 6) (hWBC : WBC.natDegree ≤ 6) :
    (sAC * WAC + sBC * WBC).natDegree ≤ 7 := by
  refine (natDegree_add_le _ _).trans ?_
  have h1 : (sAC * WAC).natDegree ≤ 7 :=
    (natDegree_mul_le).trans (by omega)
  have h2 : (sBC * WBC).natDegree ≤ 7 :=
    (natDegree_mul_le).trans (by omega)
  exact max_le h1 h2

/-! ## 4. Assembly: a split linear combination is a three-term linear syzygy -/

/-- **Assembly.**  If `s_AC W_AC + s_BC W_BC = s_AB W_AB`, then
`s_AB W_AB − s_AC W_AC − s_BC W_BC = 0` is a three-term syzygy.  This is the
linear analogue of SYZ48 `dvd_scalar_gives_syzygy` / SYZ49
`full_split_gives_constant_syzygy`. -/
theorem linear_split_gives_syzygy
    {K : Type*} [Field K] (WAB WAC WBC sAB sAC sBC : K[X])
    (hP : sAC * WAC + sBC * WBC = sAB * WAB) :
    sAB * WAB + (-sAC) * WAC + (-sBC) * WBC = 0 := by
  linear_combination -hP

/-! ## 5. Band polytope: first realizable home is `n = 20`, not `μ₁₈` -/

/-- **`(6,6,6)` is balanced-interior.**  `max + 1 = 7 < 9 = ⌊18/2⌋`. -/
theorem sextic_balanced_interior : SYZ48.BalancedInterior 6 6 6 := by
  unfold SYZ48.BalancedInterior
  decide

/-- **First band-realizable home.**  `k = 10` (`n = 20`), `t = 2`:
disjointness `18+2 ≤ 20`, budget `6+1+2 = 9 ≤ 10`, slack `21 ≤ 18+4 = 22`. -/
theorem sextic_realizable_n20 : SYZ50.Realizable 6 6 6 2 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`μ₁₈ = μ_{3·6}` is not band-realizable.**  SYZ50's domain law needs
`n ≥ 3d + 1 = 19`; the whole subgroup of size `18` is one point short, exactly
as `μ₁₂` was for `(4,4,4)`. -/
theorem mu18_sextic_not_realizable : ¬ ∃ t : ℕ, SYZ50.Realizable 6 6 6 t 9 := by
  rintro ⟨t, h⟩
  have := SYZ50.balanced_profile_needs_domain h
  omega

/-- **The intersection is nonempty at the first middle degree.**  `(6,6,6)` is
both balanced-interior and band-realizable at rate `1/2` (`n = 20`, `t = 2`).
The first middle slot therefore has a combinatorially legal home — the same
polytope verdict SYZ50 gave for `(4,4,4)` on `n = 14`. -/
theorem first_middle_meets_realizable :
    SYZ50.Realizable 6 6 6 2 10 ∧ SYZ48.BalancedInterior 6 6 6 :=
  ⟨sextic_realizable_n20, sextic_balanced_interior⟩

/-- **Lift ceiling on the `n = 20` home.**  Each core has size
`s = 6+6+2 = 14`, so `∑(n − sᵢ) = 3·6 = 18 ≤ 19 = n − 1`.  A maximal pencil
lift still sits at-or-below the SYZ22 budget, as in SYZ50's `n = 14` case. -/
theorem sextic_lift_ceiling_le_budget :
    3 * (20 - (6 + 6 + 2)) ≤ 20 - 1 := by
  decide

end ArkLib.ProximityGap.SYZ71

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ71.vanished_slot_product_ge_twelve
#print axioms ArkLib.ProximityGap.SYZ71.slot_le_seven_cofactor_le_one
#print axioms ArkLib.ProximityGap.SYZ71.linear_slot_product_eq_seven
#print axioms ArkLib.ProximityGap.SYZ71.product_seven_is_first_slot
#print axioms ArkLib.ProximityGap.SYZ71.linear_slot_not_floor
#print axioms ArkLib.ProximityGap.SYZ71.linear_combo_isRoot_iff_mobius
#print axioms ArkLib.ProximityGap.SYZ71.linear_combo_natDegree_le
#print axioms ArkLib.ProximityGap.SYZ71.linear_split_gives_syzygy
#print axioms ArkLib.ProximityGap.SYZ71.sextic_balanced_interior
#print axioms ArkLib.ProximityGap.SYZ71.sextic_realizable_n20
#print axioms ArkLib.ProximityGap.SYZ71.mu18_sextic_not_realizable
#print axioms ArkLib.ProximityGap.SYZ71.first_middle_meets_realizable
#print axioms ArkLib.ProximityGap.SYZ71.sextic_lift_ceiling_le_budget
