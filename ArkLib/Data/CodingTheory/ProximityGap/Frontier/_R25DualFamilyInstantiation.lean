/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24InvolutionNoGo
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# LANE B2 (#466 round 25): the dual family INSTANTIATED — `SubgroupDualFamily` +
  `DualFamilyGroupLaw` reduce to a bare discrete-log package

Rounds 19–24 took the dual family `{λ_j}` of `F*/G` as a bundled hypothesis package (five
character-theoretic fields plus the group/modulus law).  This brick DISCHARGES all of it from
one elementary input: a discrete logarithm `dl : F → ℤ/m` (a fiber-equal surjective-hom-style
map vanishing exactly on `G`).  Concretely,

  `λ_j(a) := ψ_m(j·dl(a))`  (`ψ_m` the standard additive character of `ℤ/m`, `λ_j(0) := 0`)

satisfies EVERY field of both packages (`dualFam_isSubgroupDualFamily`,
`dualFam_groupLaw`): the indicator orthogonality and the punctured-sum vanishing are the
`ℤ/m` character orthogonality (`AddChar.sum_mulShift`), the group law is bilinearity, and
unit modulus is `‖exp(2πi·k/m)‖ = 1`.

The remaining input `DiscreteLogTo` is bare cyclic-group bookkeeping (`F*` is cyclic; any
generator induces `dl` for the index-`m` subgroup) — a far weaker hypothesis than the analytic
-looking package it replaces.  With this, the round 19–24 chain (Jacobi–Fourier expansion,
Parseval, quartic/sextic collapses, the calibrated `TripleConvEnergyBound` consumer, and the
involution no-go) holds for every finite field given only a discrete log.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 25, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### (0) The standard character of `ℤ/m` and its properties. -/

/-- The primitive `m`-th root `ζ_m = exp(2πi/m)`. -/
noncomputable def zetaM (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

theorem zetaM_pow (m : ℕ) [NeZero m] : zetaM m ^ m = 1 := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [zetaM, ← Complex.exp_nat_mul]
  rw [show (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I from by
    field_simp]
  exact Complex.exp_two_pi_mul_I

/-- The standard additive character `ψ_m` of `ℤ/m`. -/
noncomputable def psiM (m : ℕ) [NeZero m] : AddChar (ZMod m) ℂ :=
  AddChar.zmodChar m (zetaM_pow m)

theorem psiM_primitive (m : ℕ) [NeZero m] : (psiM m).IsPrimitive := by
  have hprim : IsPrimitiveRoot (zetaM m) m := by
    show IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / m)) m
    exact Complex.isPrimitiveRoot_exp m (NeZero.ne m)
  exact AddChar.zmodChar_primitive_of_primitive_root m hprim

theorem norm_psiM (m : ℕ) [NeZero m] (x : ZMod m) : ‖psiM m x‖ = 1 := by
  rw [psiM, AddChar.zmodChar_apply, norm_pow]
  have : ‖zetaM m‖ = 1 := by
    rw [zetaM, Complex.norm_exp]
    have : (2 * Real.pi * Complex.I / m).re = 0 := by
      rw [show (2 * Real.pi * Complex.I / m) = ((2 * Real.pi / m : ℝ) : ℂ) * Complex.I from by
        push_cast; ring]
      simp
    rw [this, Real.exp_zero]
  rw [this, one_pow]

/-! ### (1) The discrete-log package — the ONLY remaining input. -/

/-- A discrete logarithm onto `ℤ/m` with kernel exactly `G` and equal fibers.  Bare cyclic
bookkeeping: `F*` cyclic ⟹ this exists for the index-`m` subgroup (companion lane). -/
structure DiscreteLogTo (G : Finset F) (m : ℕ) (dl : F → ZMod m) : Prop where
  zero_notMem : (0 : F) ∉ G
  map_mul : ∀ a b : F, a ≠ 0 → b ≠ 0 → dl (a * b) = dl a + dl b
  vanish_iff : ∀ a : F, a ≠ 0 → (dl a = 0 ↔ a ∈ G)
  fiber_card : ∀ c : ZMod m,
    (((Finset.univ : Finset F).erase 0).filter (fun a => dl a = c)).card
      = (Fintype.card F - 1) / m

/-- The instantiated dual family: `λ_j(a) = ψ_m(j·dl(a))`, `λ_j(0) = 0`. -/
noncomputable def dualFam (m : ℕ) [NeZero m] (dl : F → ZMod m) : ZMod m → F → ℂ :=
  fun j a => if a = 0 then 0 else psiM m (j * dl a)

variable {G : Finset F} {m : ℕ} [NeZero m] {dl : F → ZMod m}

/-- **The group/modulus law holds for the instantiated family** (bilinearity + unit modulus). -/
theorem dualFam_groupLaw (m : ℕ) [NeZero m] (dl : F → ZMod m) :
    DualFamilyGroupLaw m (dualFam m dl) where
  add_eq_mul := by
    intro i j a
    by_cases ha : a = 0
    · simp [dualFam, ha]
    · simp only [dualFam, if_neg ha]
      rw [add_mul, AddChar.map_add_eq_mul]
  norm_one := by
    intro j a ha
    simp only [dualFam, if_neg ha]
    exact norm_psiM m _

/-- **The full dual-family package holds for the instantiated family** — every field
discharged from the discrete-log package via `ℤ/m` character orthogonality. -/
theorem dualFam_isSubgroupDualFamily (hdl : DiscreteLogTo G m dl) :
    SubgroupDualFamily G m (dualFam m dl) where
  map_zero := by
    intro j
    simp [dualFam]
  map_mul := by
    intro j a b
    by_cases ha : a = 0
    · simp [dualFam, ha]
    · by_cases hb : b = 0
      · simp [dualFam, hb]
      · have hab : a * b ≠ 0 := mul_ne_zero ha hb
        simp only [dualFam, if_neg ha, if_neg hb, if_neg hab]
        rw [hdl.map_mul a b ha hb, mul_add, AddChar.map_add_eq_mul]
  triv_on_units := by
    intro a ha
    simp only [dualFam, if_neg ha, zero_mul, AddChar.map_zero_eq_one]
  sum_eq_zero := by
    intro j hj
    classical
    -- Σ_{a:F} λ_j(a) = Σ_{a≠0} ψ(j·dl a) = ((q−1)/m)·Σ_c ψ(j·c) = 0
    have hsplit : ∑ a : F, dualFam m dl j a
        = ∑ a ∈ (Finset.univ : Finset F).erase 0, psiM m (j * dl a) := by
      rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
        (f := fun a => dualFam m dl j a) (by simp [dualFam])]
      exact Finset.sum_congr rfl (fun a ha => by
        simp only [dualFam, if_neg (Finset.mem_erase.mp ha).1])
    rw [hsplit]
    have hfiber : ∑ a ∈ (Finset.univ : Finset F).erase 0, psiM m (j * dl a)
        = ∑ c : ZMod m, ∑ a ∈ ((Finset.univ : Finset F).erase 0).filter
            (fun a => dl a = c), psiM m (j * dl a) := by
      exact (Finset.sum_fiberwise ((Finset.univ : Finset F).erase 0)
        (fun a => dl a) (fun a => psiM m (j * dl a))).symm
    rw [hfiber]
    have hinner : ∀ c : ZMod m,
        ∑ a ∈ ((Finset.univ : Finset F).erase 0).filter (fun a => dl a = c),
          psiM m (j * dl a)
        = (((Fintype.card F - 1) / m : ℕ) : ℂ) * psiM m (j * c) := by
      intro c
      have hpt : ∀ a ∈ ((Finset.univ : Finset F).erase 0).filter (fun a => dl a = c),
          psiM m (j * dl a) = psiM m (j * c) := by
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, hdl.fiber_card c]
    rw [Finset.sum_congr rfl (fun c _ => hinner c), ← Finset.mul_sum]
    have horth : ∑ c : ZMod m, psiM m (j * c) = 0 := by
      have := AddChar.sum_mulShift (ψ := psiM m) j (psiM_primitive m)
      rw [if_neg hj] at this
      calc ∑ c : ZMod m, psiM m (j * c) = ∑ c : ZMod m, psiM m (c * j) := by
            exact Finset.sum_congr rfl (fun c _ => by rw [mul_comm])
        _ = 0 := by exact_mod_cast this
    rw [horth, mul_zero]
  indicator := by
    intro w
    classical
    by_cases hw : w = 0
    · subst hw
      have hL : ∑ j : ZMod m, dualFam m dl j (0 : F) = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        simp [dualFam]
      rw [hL, if_neg hdl.zero_notMem, mul_zero]
    · have hL : ∑ j : ZMod m, dualFam m dl j w = ∑ j : ZMod m, psiM m (j * dl w) := by
        exact Finset.sum_congr rfl (fun j _ => by simp only [dualFam, if_neg hw])
      rw [hL]
      have := AddChar.sum_mulShift (ψ := psiM m) (dl w) (psiM_primitive m)
      have hcard : ∑ j : ZMod m, psiM m (j * dl w)
          = if dl w = 0 then ((Fintype.card (ZMod m) : ℕ) : ℂ) else 0 := by
        simpa using this
      rw [hcard]
      have hzc : (Fintype.card (ZMod m) : ℕ) = m := ZMod.card m
      by_cases hdlw : dl w = 0
      · rw [if_pos hdlw, if_pos ((hdl.vanish_iff w hw).mp hdlw), hzc, mul_one]
      · rw [if_neg hdlw, if_neg (fun hmem => hdlw ((hdl.vanish_iff w hw).mpr hmem)),
          mul_zero]

end ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation.psiM_primitive
#print axioms ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation.dualFam_groupLaw
#print axioms
  ArkLib.ProximityGap.Frontier.R25DualFamilyInstantiation.dualFam_isSubgroupDualFamily
