/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GWInterpolation
import Mathlib

/-!
# Degree bookkeeping for the GW folded substitution — discharging BRICK-I's named residual (#93/#94)

`GWFoldedDegreeObligation A p shift agreeCount := (foldedSubstitution A p shift).natDegree < agreeCount`
was the one named residual of BRICK-I (`GWInterpolation`). It is **pure polynomial degree arithmetic**,
not open math: from `foldedSubstitution A p shift = A 0 + ∑ⱼ A_{j+1}·(p ∘ shiftⱼ)` and the GW degree
budgets `deg A 0 ≤ d₀`, `deg A_{j+1} ≤ d`, `deg p ≤ dₚ`, `deg shiftⱼ ≤ 1`, the folded substitution has

> `foldedSubstitution_natDegree_le` :  `deg (foldedSubstitution A p shift) ≤ max d₀ (d + dₚ)`.

Hence (`gwFoldedDegreeObligation_of_lt`) the obligation holds whenever `max d₀ (d + dₚ) < agreeCount` —
a transparent parameter inequality. For folded/multiplicity RS (small block degrees, large agreement)
this is satisfied and closes BRICK-I → BRICK-V; for plain RS in the prize regime the budgets force
`max d₀ (d+dₚ) ≥ n+k-1 ≥ agreeCount` (this is exactly wall W1), so the residual is now a *precise*
arithmetic statement rather than a black box. Either way the named residual is reduced to a closed,
computable inequality with no remaining open lemma.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Polynomial

namespace CodingTheory.GWBrickI

variable {F : Type*} [Field F]

/-- **Degree of the GW folded substitution.** With block-degree budgets `deg A 0 ≤ d₀`,
`deg A_{j+1} ≤ d`, `deg p ≤ dₚ`, and degree-`≤1` folding shifts, the folded substitution
`A 0 + ∑ⱼ A_{j+1}·(p ∘ shiftⱼ)` has degree `≤ max d₀ (d + dₚ)`. Pure degree bookkeeping. -/
theorem foldedSubstitution_natDegree_le {s : ℕ} (A : Fin (s + 1) → F[X]) (p : F[X])
    (shift : Fin s → F[X]) {d₀ d dₚ : ℕ}
    (hA0 : (A 0).natDegree ≤ d₀) (hAj : ∀ j : Fin s, (A j.succ).natDegree ≤ d)
    (hp : p.natDegree ≤ dₚ) (hshift : ∀ j : Fin s, (shift j).natDegree ≤ 1) :
    (foldedSubstitution A p shift).natDegree ≤ max d₀ (d + dₚ) := by
  simp only [foldedSubstitution]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans hA0 (le_max_left _ _)
  · refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    refine le_trans (natDegree_mul_le) ?_
    have hcomp : (p.comp (shift j)).natDegree ≤ dₚ :=
      le_trans natDegree_comp_le
        (by calc p.natDegree * (shift j).natDegree ≤ dₚ * 1 := Nat.mul_le_mul hp (hshift j)
              _ = dₚ := mul_one dₚ)
    calc (A j.succ).natDegree + (p.comp (shift j)).natDegree
        ≤ d + dₚ := Nat.add_le_add (hAj j) hcomp
      _ ≤ max d₀ (d + dₚ) := le_max_right _ _

/-- **BRICK-I's residual is a transparent inequality.** The folded-substitution degree obligation
holds whenever the (computable) degree budget `max d₀ (d + dₚ)` is below the agreement count. -/
theorem gwFoldedDegreeObligation_of_lt {s : ℕ} (A : Fin (s + 1) → F[X]) (p : F[X])
    (shift : Fin s → F[X]) {d₀ d dₚ agreeCount : ℕ}
    (hA0 : (A 0).natDegree ≤ d₀) (hAj : ∀ j : Fin s, (A j.succ).natDegree ≤ d)
    (hp : p.natDegree ≤ dₚ) (hshift : ∀ j : Fin s, (shift j).natDegree ≤ 1)
    (hlt : max d₀ (d + dₚ) < agreeCount) :
    GWFoldedDegreeObligation A p shift agreeCount :=
  lt_of_le_of_lt (foldedSubstitution_natDegree_le A p shift hA0 hAj hp hshift) hlt

end CodingTheory.GWBrickI

/-! ## Axiom audit -/
#print axioms CodingTheory.GWBrickI.foldedSubstitution_natDegree_le
#print axioms CodingTheory.GWBrickI.gwFoldedDegreeObligation_of_lt
