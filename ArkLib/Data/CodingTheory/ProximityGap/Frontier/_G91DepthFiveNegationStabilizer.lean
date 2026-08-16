/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86DepthFiveConstantGap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# G91: the exceptional depth-five scaling stabilizer is zero-sum

After quotienting a distinct depth-five core by coordinate permutations and side swap, a diagonal
scaling stabilizer can exchange the two five-sets.  In a dyadic scaling group the only possible
such multiplier is the involution `-1`; hence the exceptional pair has the form `{A, -A}`.

This file isolates the algebraic consequence: if `A` and `-A` have equal sums in a group without
two-torsion, then `A` has sum zero.  Such exceptional cores admit a four-free-coordinate cover.
At production parameters even the full `n^4` raw cover is absorbed by the corrected depth-five
Wick budget.  This does not quotient by scaling and therefore remains a valid decoder input after
the G83 orbit-representative retraction.

The group-action classification of `-1` as the only possible stabilizer is separate; the exact
small-order census is reproducible with `scripts/probes/probe_g91_depth_five_distinct_orbits.py`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G91DepthFiveNegationStabilizer

open scoped BigOperators
open G86DepthFiveConstantGap

/-- Negating every member of a finite set negates its sum. -/
theorem sum_image_neg {A : Type*} [AddCommGroup A] [DecidableEq A] (S : Finset A) :
    ∑ x ∈ S.image (- ·), x = -(∑ x ∈ S, x) := by
  rw [Finset.sum_image]
  · rw [Finset.sum_neg_distrib]
  · intro a₁ ha₁ a₂ ha₂ h
    simpa using congrArg Neg.neg h

/-- A side-swapping negation stabilizer on an equal-sum pair forces the five-set sum to vanish. -/
theorem sum_eq_zero_of_negation_sum_eq
    {A : Type*} [AddCommGroup A] [DecidableEq A]
    (S : Finset A)
    (hTwo : ∀ x : A, (2 : ℕ) • x = 0 → x = 0)
    (hEq : (∑ x ∈ S, x) = ∑ x ∈ S.image (- ·), x) :
    ∑ x ∈ S, x = 0 := by
  rw [sum_image_neg] at hEq
  have htwo : (2 : ℕ) • (∑ x ∈ S, x) = 0 := by
    simpa [two_nsmul] using congrArg (fun z => z + ∑ x ∈ S, x) hEq
  exact hTwo _ htwo

/-- Ordered zero-sum words of length five.  Injectivity/distinctness is deliberately omitted, so
this is a cover of the exceptional distinct-core stratum. -/
abbrev ZeroSumFive (A : Type*) [AddCommGroup A] :=
  {f : Fin 5 → A // ∑ i, f i = 0}

/-- Forget the last coordinate of a zero-sum five-word. -/
def zeroSumFiveInit {A : Type*} [AddCommGroup A] (f : ZeroSumFive A) : Fin 4 → A :=
  fun i => f.1 i.castSucc

/-- Four coordinates determine the fifth coordinate of a zero-sum five-word. -/
theorem zeroSumFiveInit_injective {A : Type*} [AddCommGroup A] :
    Function.Injective (zeroSumFiveInit (A := A)) := by
  intro f g hinit
  apply Subtype.ext
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact congrFun hinit i
  · have hpart : (∑ i : Fin 4, f.1 i.castSucc) = ∑ i : Fin 4, g.1 i.castSucc :=
      Finset.sum_congr rfl (fun i _ => congrFun hinit i)
    have hf : (∑ i : Fin 4, f.1 i.castSucc) + f.1 (Fin.last 4) = 0 := by
      simpa only [Fin.sum_univ_castSucc] using f.2
    have hg : (∑ i : Fin 4, g.1 i.castSucc) + g.1 (Fin.last 4) = 0 := by
      simpa only [Fin.sum_univ_castSucc] using g.2
    rw [hpart] at hf
    exact add_left_cancel (hf.trans hg.symm)

/-- Exact elementary cover bound for the exceptional zero-sum stratum. -/
theorem card_zeroSumFive_le_fourth_power
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] :
    Fintype.card (ZeroSumFive A) ≤ Fintype.card A ^ 4 := by
  classical
  calc
    Fintype.card (ZeroSumFive A) ≤ Fintype.card (Fin 4 → A) :=
      Fintype.card_le_of_injective (zeroSumFiveInit (A := A))
        (zeroSumFiveInit_injective (A := A))
    _ = Fintype.card A ^ 4 := by simp

/-- The full `n^4` zero-sum cover, with its scale retained, fits the production Wick budget. -/
theorem production_depth_five_negation_exception_absorbed :
    (2 ^ 30) ^ 4 * correctedEnvelope (2 ^ 30) 110 1 5 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedEnvelope, Nat.descFactorial, Nat.factorial, Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G91DepthFiveNegationStabilizer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveNegationStabilizer.sum_eq_zero_of_negation_sum_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveNegationStabilizer.card_zeroSumFive_le_fourth_power
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveNegationStabilizer.production_depth_five_negation_exception_absorbed
