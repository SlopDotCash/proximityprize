/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R391FourFiberToricNormalization

/-!
# R392: a linear four-fiber envelope forces constant pair multiplicity

For every pair `u + v = c` and every `x ∈ G`, insert the antipodal pair `(x,-x)`.  This injects
`G × pairFiber(G,c)` into `fourFiber(G,c)`.  Consequently any bound
`fourFiber(G,c) ≤ C|G|` already implies `pairFiber(G,c) ≤ C` when `G` is nonempty.

This identifies a necessary lower-dimensional input for the finite-characteristic switching route:
one must control pair multiplicity as well as the primitive no-antipodal remainder.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber

open ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- Ordered pairs from `G` with sum `c`. -/
noncomputable def pairFiber (G : Finset F) (c : F) : Finset (Fin 2 → F) :=
  (Fintype.piFinset fun _ : Fin 2 => G).filter (fun u => ∑ i, u i = c)

/-- Insert `(x,-x)` before an ordered pair. -/
def insertAntipodal (x : F) (u : Fin 2 → F) : Fin 4 → F :=
  ![x, -x, u 0, u 1]

theorem sum_insertAntipodal (x : F) (u : Fin 2 → F) :
    ∑ i, insertAntipodal x u i = ∑ i, u i := by
  rw [Fin.sum_univ_four, Fin.sum_univ_two]
  simp [insertAntipodal]

theorem insertAntipodal_in_fourFiber
    {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) {c x : F} (hx : x ∈ G)
    {u : Fin 2 → F} (hu : u ∈ pairFiber G c) :
    insertAntipodal x u ∈ fourFiber G c := by
  rw [pairFiber, Finset.mem_filter] at hu
  rw [fourFiber, Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hx
    · exact hneg x hx
    · exact (Fintype.mem_piFinset.mp hu.1) 0
    · exact (Fintype.mem_piFinset.mp hu.1) 1
  · rw [sum_insertAntipodal, hu.2]

/-- The insertion remembers both the antipodal parameter and the residual ordered pair. -/
theorem insertAntipodal_injective :
    Function.Injective (fun xu : F × (Fin 2 → F) => insertAntipodal xu.1 xu.2) := by
  intro xu yv h
  rcases xu with ⟨x, u⟩
  rcases yv with ⟨y, v⟩
  have hxy := congrFun h 0
  have h0 := congrFun h 2
  have h1 := congrFun h 3
  simp [insertAntipodal] at hxy h0 h1
  have huv : u = v := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  exact Prod.ext hxy huv

/-- **Antipodal insertion lower bound.** -/
theorem card_mul_card_pairFiber_le_card_fourFiber
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    G.card * (pairFiber G c).card ≤ (fourFiber G c).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun xu : F × (Fin 2 → F) => insertAntipodal xu.1 xu.2)
  · intro xu hxu
    rw [Finset.mem_coe, Finset.mem_product] at hxu
    exact insertAntipodal_in_fourFiber hneg hxu.1 hxu.2
  · exact fun _ _ _ _ h => insertAntipodal_injective h

/-- **Necessary pair-multiplicity consequence.** A nonempty linear four-fiber envelope with
constant `C` forces the same constant pair-fiber envelope. -/
theorem card_pairFiber_le_of_fourFiber_le
    (G : Finset F) (hG : G.Nonempty) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) (C : ℕ)
    (hfour : (fourFiber G c).card ≤ C * G.card) :
    (pairFiber G c).card ≤ C := by
  have hlower := card_mul_card_pairFiber_le_card_fourFiber G hneg c
  have hpos : 0 < G.card := Finset.card_pos.mpr hG
  nlinarith

end ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber.card_mul_card_pairFiber_le_card_fourFiber
#print axioms
  ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber.card_pairFiber_le_of_fourFiber_le
