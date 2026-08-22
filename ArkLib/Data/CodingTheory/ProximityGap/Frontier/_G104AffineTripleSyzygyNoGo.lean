/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# G104: three affine scalar blocks already force a syzygy

G103 showed that the arbitrary-functional endpoint of G86/G87 admits replicated blocks of
unbounded cardinality.  This file retains the most important cross-witness structure discarded by
that abstraction: constraint rows depend affinely on the bad scalar.  Even then, a common row
stratum has rank at most two in the scalar direction.  Any three scalar values obey an explicit
Lagrange dependence.

Thus a syzygy is automatic on every shared-row stratum of size three, including when the scalars
are distinct and every individual block is internally linearly independent.  A quantitative
continuation must bound the multiplicities and intersections of the witness row strata (or exploit
more structure), rather than merely detect a global syzygy.  This does not bound or construct
concrete `mcaEvent` witnesses.  Issue #466/#507.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

/-- An affine scalar pencil in an arbitrary `F`-module. -/
def affineRow (a b : W) (γ : F) : W := a + γ • b

/-- **Three-scalar Lagrange syzygy.** Every three points of an affine pencil have this explicit
linear dependence. -/
theorem affineRow_triple_syzygy (a b : W) (γ₀ γ₁ γ₂ : F) :
    (γ₁ - γ₂) • affineRow a b γ₀ +
      (γ₂ - γ₀) • affineRow a b γ₁ +
        (γ₀ - γ₁) • affineRow a b γ₂ = 0 := by
  simp only [affineRow, smul_add, smul_smul]
  module

/-- Pairwise distinct scalar values make the displayed certificate nontrivial. -/
theorem affineRow_triple_syzygy_nontrivial (a b : W) {γ₀ γ₁ γ₂ : F}
    (h₁₂ : γ₁ ≠ γ₂) :
    (γ₁ - γ₂) • affineRow a b γ₀ +
          (γ₂ - γ₀) • affineRow a b γ₁ +
            (γ₀ - γ₁) • affineRow a b γ₂ = 0 ∧
      γ₁ - γ₂ ≠ 0 := by
  exact ⟨affineRow_triple_syzygy a b γ₀ γ₁ γ₂, sub_ne_zero.mpr h₁₂⟩

/-- Three affine copies of one row are linearly dependent whenever two of their scalar parameters
are distinct. -/
theorem affineRow_triple_not_linearIndependent (a b : W) (γ : Fin 3 → F)
    (h₁₂ : γ 1 ≠ γ 2) :
    ¬ LinearIndependent F (fun i : Fin 3 => affineRow a b (γ i)) := by
  intro hli
  let c : Fin 3 → F := ![γ 1 - γ 2, γ 2 - γ 0, γ 0 - γ 1]
  have hsum : ∑ i : Fin 3, c i • affineRow a b (γ i) = 0 := by
    simpa [c, Fin.sum_univ_succ, add_assoc] using
      affineRow_triple_syzygy a b (γ 0) (γ 1) (γ 2)
  have hc := Fintype.linearIndependent_iff.mp hli c hsum 0
  exact sub_ne_zero.mpr h₁₂ (by simpa [c] using hc)

/-- An affine family of `m`-row witness blocks. -/
def affineBlock {m : ℕ} (a b : Fin m → W) (γ : F) : Fin m → W :=
  fun j => affineRow (a j) (b j) γ

/-- **Shared-row-stratum no-go.** Internal independence of all three witness blocks coexists with
an unavoidable global syzygy.  Therefore per-block independence does not make affine syzygies
exceptional. -/
theorem affineBlock_three_witnesses_syzygy {m : ℕ} (hm : 0 < m)
    (a b : Fin m → W) (γ : Fin 3 → F) (hγ : Function.Injective γ)
    (hblock : ∀ i : Fin 3, LinearIndependent F (affineBlock a b (γ i))) :
    (∀ i : Fin 3, LinearIndependent F (affineBlock a b (γ i))) ∧
      ∃ j : Fin m,
        ¬ LinearIndependent F (fun i : Fin 3 => affineBlock a b (γ i) j) := by
  refine ⟨hblock, ⟨⟨0, hm⟩, ?_⟩⟩
  apply affineRow_triple_not_linearIndependent
  exact hγ.ne (by decide)

end ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo

#print axioms
  ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo.affineRow_triple_syzygy
#print axioms
  ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo.affineRow_triple_syzygy_nontrivial
#print axioms
  ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo.affineRow_triple_not_linearIndependent
#print axioms
  ArkLib.ProximityGap.Frontier.G104AffineTripleSyzygyNoGo.affineBlock_three_witnesses_syzygy
