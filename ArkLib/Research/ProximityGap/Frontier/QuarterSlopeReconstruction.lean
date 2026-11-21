/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadCoreDeterminant

/-! # Reconstructing four signed heads from three rational direction maps -/

set_option autoImplicit false
noncomputable section
open _root_.ProximityGap.FourHeadCoreDeterminant
namespace ArkLib.ProximityGap.Frontier.QuarterSlopeReconstruction
variable {R : Type*} [CommRing R]

private def signed (x y z : R) : Fin 4 → R :=
  ![x+y+z,x-y-z,-x+y-z,-x-y+z]

/-- First scalar row of the reconstruction. Exchanging the two triples gives the second. -/
def row (p q : Fin 3 → R) : Fin 4 → R :=
  signed (p 0*q 1*q 2) (p 1*q 0*q 2) (p 2*q 0*q 1)

private def j : Fin 3 → Fin 3 := ![1,0,0]
private def k : Fin 3 → Fin 3 := ![2,2,1]

/-- The two signed coincidence forms for the maps opposite the stated index. -/
def plus (p q : Fin 3 → R) (i : Fin 3) := p (j i)*q (k i)+p (k i)*q (j i)
def minus (p q : Fin 3 → R) (i : Fin 3) := p (j i)*q (k i)-p (k i)*q (j i)

/-- The exact factorizations recover both coordinate differences of all six edges. -/
theorem edge_forms (p q : Fin 3 → R) (i : Fin 3) :
    nearSide (row p q) i = -2*q i*plus p q i ∧
    nearSide (row q p) i = -2*p i*plus p q i ∧
    farSide (row p q) i = -2*q i*minus p q i ∧
    farSide (row q p) i = 2*p i*minus p q i := by
  fin_cases i <;> dsimp [nearSide,farSide,row,signed,plus,minus,j,k,Fin.succ] <;>
    exact ⟨by ring,by ring,by ring,by ring⟩

/-- Conjugate numerator-denominator pairs yield conjugate reconstructed rows. -/
theorem conjugate_rows (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (p : Fin 3 → R) (i : Fin 4) :
    σ (row p (fun j => σ (p j)) i) = row (fun j => σ (p j)) p i := by
  fin_cases i <;> dsimp [row,signed] <;> simp only [map_mul,map_add,map_sub,map_neg,hσ]

/-- With each double orbit contributing two directions, these are the exact ways
the finite singleton contribution can push the total over the twice-length budget. -/
theorem orbit_budget (d orbits fresh : ℕ) (ho : orbits ≤ 4*d) (hf : fresh ≤ 12) :
    2*(4*d+4) < 2*orbits+fresh ↔
      (orbits=4*d ∧ 9≤fresh) ∨ (orbits+1=4*d ∧ 11≤fresh) := by omega

#print axioms edge_forms
#print axioms conjugate_rows
#print axioms orbit_budget
end ArkLib.ProximityGap.Frontier.QuarterSlopeReconstruction
