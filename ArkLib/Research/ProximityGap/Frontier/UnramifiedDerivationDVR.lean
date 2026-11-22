/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TameLogarithmicDVR

/-! # Derivations at an unramified DVR extension -/

namespace ArkLib.ProximityGap.UnramifiedDerivationDVR

open TameLogarithmicDVR Polynomial

variable {E : Type*} [Field E] {B : Subring E} [IsDiscreteValuationRing B]

/-- If the uniformizer of the upper DVR comes from the base up to a unit, any
base-regular derivation extends regularly. The derivation may move the base divisor. -/
theorem unramified_lift [IsFractionRing B E] (D : Derivation ℤ E E)
    (R : Subring B) [IsLocalRing R] [IsLocalHom (algebraMap R B)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B)]
    (A : Subalgebra R B) [Module.Finite R A] (S : Submonoid A) [IsLocalization S B]
    (u : B) (hu : Irreducible u) (π : R) (v : Bˣ) (hπ : (π : B) = u * v)
    (hr : ∀ r : R, D ((r : B) : E) ∈ B) :
    ∀ b : B, D (b : E) ∈ B := by
  let vE : Eˣ := Units.map B.subtype.toMonoidHom v
  let πE : E := ((π : B) : E)
  let Dπ := πE • D
  have hscaled (x : E) : Dπ x = πE * D x := rfl
  have hrπ (r : R) : Dπ ((r : B) : E) ∈ B := B.mul_mem (π : B).property (hr r)
  have hlog : ∃ c : B, Dπ ((u ^ (0 + 1) * v : B) : E) =
      ((u ^ (0 + 1) * v : B) : E) * (c : E) := by
    refine ⟨⟨D πE, hr π⟩, ?_⟩
    simp only [Nat.zero_add, pow_one, ← hπ, hscaled, πE]
  have hclear := clear_finite_localization Dπ R A S u hu hrπ
  obtain ⟨hb, c, hc⟩ := logarithmic_of_clears Dπ R u hu 0 v (by simp) hrπ hlog hclear
  let Δ := scaled Dπ u 0 (fun b ↦ by simpa using hb b)
  let ρ := IsLocalRing.residue B
  have hker (b : B) : ρ b = 0 ↔ u ∣ b := by
    rw [IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hu]
    exact Ideal.mem_span_singleton
  have hval (b : B) : (Δ b : E) = πE * D (b : E) := by
    change (u : E)^0 * Dπ (b : E) = _
    simp only [pow_zero, one_mul, hscaled]
  have htan : u ∣ Δ u := ⟨c, Subtype.ext ((hval u).trans hc)⟩
  have hres (r : R) : ρ (Δ (R.subtype r)) = 0 := by
    apply (hker _).mpr
    refine ⟨v * (⟨D ((r : B) : E), hr r⟩ : B), Subtype.ext ?_⟩
    rw [hval]
    change ((π : B) : E) * D ((r : B) : E) = (u : E) * ((v : B) * D ((r : B) : E))
    rw [hπ, Subring.coe_mul, mul_assoc]
  have hs (b : B) := residue_simple_lift (IsLocalRing.residue R)
    IsLocalRing.residue_surjective (ρ.comp R.subtype)
    (show ρ.comp R.subtype = (algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField B)).comp (IsLocalRing.residue R) by rfl) (ρ b)
  intro b
  obtain ⟨d, hd⟩ := residue_vanishes Δ u htan ρ hker R.subtype hres hs b
  have hm : (u : E) * ((vE : E) * D (b : E)) = (u : E) * (d : E) := by
    have ht := (hval b).symm.trans (congrArg (fun t : B ↦ (t : E)) hd)
    change ((π : B) : E) * D (b : E) = (u : E) * (d : E) at ht
    rw [hπ, Subring.coe_mul, mul_assoc] at ht
    exact ht
  have ht := mul_left_cancel₀ (show (u : E) ≠ 0 from fun h ↦ hu.ne_zero (Subtype.ext h)) hm
  have heq : D (b : E) = ((↑v⁻¹ : B) : E) * (d : E) := by
    rw [← ht, ← mul_assoc]
    change D (b : E) = (↑vE⁻¹ * (vE : E)) * D (b : E)
    simp
  exact heq ▸ B.mul_mem (↑v⁻¹ : B).property d.property

end ArkLib.ProximityGap.UnramifiedDerivationDVR

#print axioms ArkLib.ProximityGap.UnramifiedDerivationDVR.unramified_lift
