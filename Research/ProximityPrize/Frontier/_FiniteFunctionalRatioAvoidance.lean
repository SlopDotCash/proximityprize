/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RadiusOneExact

/-!
# Finite functional and ratio avoidance

This file isolates the finite-field hyperplane argument used by the three-core
radix construction.  Fewer than `|F|` nonzero linear functionals cannot vanish
collectively on every vector.  Applying this first to denominator functionals
and then to their pairwise cross-products produces two vectors whose functional
ratios are all finite and pairwise distinct.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.FiniteFunctionalRatioAvoidance

attribute [local instance] Classical.propDecidable

variable {F J : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype J] [DecidableEq J]

/-- Ordered pairs of distinct indices.  Using ordered pairs costs only a factor
two and keeps the collision-avoidance indexing elementary. -/
abbrev OffDiag (J : Type) := {pair : J × J // pair.1 ≠ pair.2}

/-- A family of fewer than `|F|` nonzero functionals on `F^d` has a common
nonvanishing point. -/
theorem exists_forall_apply_ne_zero
    (d : Nat) (hd : 0 < d) (ell : J -> Module.Dual F (Fin d -> F))
    (hell : forall j, ell j ≠ 0)
    (hcard : Fintype.card J < Fintype.card F) :
    exists v : Fin d -> F, forall j, ell j v ≠ 0 := by
  classical
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.1 hd
  let bad : Finset (Fin d -> F) := Finset.univ.biUnion fun j =>
    Finset.univ.filter fun v => ell j v = 0
  suffices exists v : Fin d -> F, v ∉ bad by
    obtain ⟨v, hv⟩ := this
    refine ⟨v, ?_⟩
    intro j hj
    exact hv (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)
  have hfilter : forall j,
      (Finset.univ.filter fun v : Fin d -> F => ell j v = 0).card =
        Fintype.card F ^ (d - 1) := by
    intro j
    have hfin : Fintype (LinearMap.ker (ell j)) := Fintype.ofFinite _
    calc
      (Finset.univ.filter fun v : Fin d -> F => ell j v = 0).card
          = Fintype.card {v : Fin d -> F // ell j v = 0} := by
            symm
            exact Fintype.card_subtype _
      _ = Nat.card (LinearMap.ker (ell j)) := by
            rw [Nat.card_eq_fintype_card]
            exact Fintype.card_congr
              (Equiv.subtypeEquivRight (fun v => by rw [LinearMap.mem_ker]))
      _ = Fintype.card F ^ (Fintype.card (Fin d) - 1) :=
            ProximityGap.card_ker_eq (ell j) (hell j)
      _ = Fintype.card F ^ (d - 1) := by simp
  have hbad : bad.card ≤ Fintype.card J * Fintype.card F ^ (d - 1) := by
    calc
      bad.card ≤ ∑ j : J,
          (Finset.univ.filter fun v : Fin d -> F => ell j v = 0).card :=
        Finset.card_biUnion_le
      _ = ∑ _j : J, Fintype.card F ^ (d - 1) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hfilter j
      _ = Fintype.card J * Fintype.card F ^ (d - 1) := by simp
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  have hpowpos : 0 < Fintype.card F ^ (d - 1) := pow_pos hqpos _
  have hstrict : bad.card < Fintype.card F ^ d := by
    calc
      bad.card ≤ Fintype.card J * Fintype.card F ^ (d - 1) := hbad
      _ < Fintype.card F * Fintype.card F ^ (d - 1) :=
        Nat.mul_lt_mul_of_pos_right hcard hpowpos
      _ = Fintype.card F ^ d := by
        rw [← pow_succ']
        congr
        omega
  by_contra hcover
  push Not at hcover
  have hbaduniv : bad = Finset.univ := Finset.eq_univ_of_forall hcover
  have huniv : (Finset.univ : Finset (Fin d -> F)).card = Fintype.card F ^ d := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [hbaduniv, huniv] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Two applications of hyperplane avoidance produce pairwise distinct finite
ratios.  `hcross` is exactly projective distinctness of the functionals, stated
in the form consumed by the second application. -/
theorem exists_ratio_injective
    (d : Nat) (hd : 0 < d) (ell : J -> Module.Dual F (Fin d -> F))
    (hell : forall j, ell j ≠ 0)
    (hdenom : Fintype.card J < Fintype.card F)
    (hpairs : Fintype.card (OffDiag J) < Fintype.card F)
    (hcross : forall (v : Fin d -> F), (forall j, ell j v ≠ 0) ->
      forall pair : OffDiag J,
        (ell pair.1.2 v) • ell pair.1.1 - (ell pair.1.1 v) • ell pair.1.2 ≠ 0) :
    exists u0 u1 : Fin d -> F,
      (forall j, ell j u1 ≠ 0) ∧
      Function.Injective (fun j => -(ell j u0) / ell j u1) := by
  obtain ⟨u1, hu1⟩ := exists_forall_apply_ne_zero d hd ell hell hdenom
  let collision : OffDiag J -> Module.Dual F (Fin d -> F) := fun pair =>
    (ell pair.1.2 u1) • ell pair.1.1 - (ell pair.1.1 u1) • ell pair.1.2
  have hcollision : forall pair, collision pair ≠ 0 := by
    intro pair
    exact hcross u1 hu1 pair
  obtain ⟨u0, hu0⟩ :=
    exists_forall_apply_ne_zero d hd collision hcollision hpairs
  refine ⟨u0, u1, hu1, ?_⟩
  intro i j hij
  by_contra hne
  let pair : OffDiag J := ⟨(i, j), hne⟩
  have hcrossne := hu0 pair
  apply hcrossne
  simp only [collision, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hi := hu1 i
  have hj := hu1 j
  field_simp at hij
  linear_combination -hij

end ArkLib.ProximityGap.Frontier.FiniteFunctionalRatioAvoidance

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.FiniteFunctionalRatioAvoidance
#print axioms exists_forall_apply_ne_zero
#print axioms exists_ratio_injective
