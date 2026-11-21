/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface

/-! # A common irreducible factor from many distinct section labels

A value-primitive surface can be reducible. If all its irreducible factors
are coprime to the auxiliary after passing to the coefficient fraction field,
the actual resultant bounds the number of shared sections.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DoubleInterpolationCommonFactor
open Polynomial Finset
variable {F : Type} [Field F]
private abbrev Surface (F : Type) [Field F] := F[X][X][X]

/-- A primitive value polynomial having one polynomial section has positive value degree. -/
theorem positive_of_section {P : Surface F} (prim : P.IsPrimitive) (z : F) (w : F[X])
    (root : P.eval₂ (evalRingHom (C z)) w = 0) : 0 < P.natDegree := by
  obtain ⟨U,factors,_,_,cover⟩ := SecondPrimePrimitiveSurface.factor_cover P prim.ne_zero prim
  obtain ⟨f,hf,_⟩ := cover z w root
  exact (factors f hf).2.1.trans_le (natDegree_le_of_dvd (factors f hf).2.2 prim.ne_zero)

/-- A common irreducible component exists whenever the joint section population
exceeds the resultant degree of the two entire surfaces. -/
theorem exists_common {P A : Surface F} (prim : P.IsPrimitive) (G : Finset F) (w : F → F[X])
    (root : ∀ z∈G, P.eval₂ (evalRingHom (C z)) (w z) = 0 ∧ A.eval₂ (evalRingHom (C z)) (w z) = 0)
    {s b : ℕ} (pdeg : WeightedSylvesterDegree.TotalDegreeLe P s)
    (adeg : WeightedSylvesterDegree.TotalDegreeLe A b)
    (large : P.natDegree*b+A.natDegree*s < G.card) :
    ∃ f : Surface F, Irreducible f ∧ 0 < f.natDegree ∧ f ∣ P ∧ f ∣ A := by
  classical
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < G.card by omega)
  have pos := positive_of_section prim x (w x) (root x hx).1
  have vanish : resultant P A P.natDegree A.natDegree = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : G => C (z:F))
      (C_injective.comp Subtype.val_injective)
    · intro z
      apply map_resultant_eq_zero_of_common_root (evalRingHom (C (z:F))) P A le_rfl le_rfl
        (Or.inl pos.ne') (w z)
      · simpa only [eval_map] using (root z z.property).1
      · simpa only [eval_map] using (root z z.property).2
    · simpa using (WeightedSylvesterDegree.natDegree_resultant_le P A pdeg adeg).trans_lt
        ((Nat.sub_le _ _).trans_lt large)
  let K := FractionRing F[X][X]
  let φ := algebraMap F[X][X] K
  have inj : Function.Injective φ := IsFractionRing.injective _ _
  obtain ⟨U,irrs,prod⟩ := WfDvdMonoid.exists_factors P prim.ne_zero
  by_contra! none
  have single (f : Surface F) (hf : f∈U) : IsCoprime (f.map φ) (A.map φ) := by
    have fd := (Multiset.dvd_prod hf).trans prod.dvd
    have fp := isPrimitive_of_dvd prim fd
    have deg : 0 < f.natDegree := by
      by_contra! zero
      have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero zero)
      have unit := fp (f.coeff 0) (eq ▸ dvd_rfl)
      exact (irrs f hf).not_isUnit (eq ▸ isUnit_C.mpr unit)
    have irr := (fp.irreducible_iff_irreducible_map_fraction_map (K:=K)).mp (irrs f hf)
    apply (irr.isCoprime_or_dvd (A.map φ)).resolve_right
    exact fun h => none f (irrs f hf) deg fd ((fp.dvd_iff_fraction_map_dvd_fraction_map K).mpr h)
  have all (V : Multiset (Surface F)) (every : ∀ f∈V, IsCoprime (f.map φ) (A.map φ)) :
      IsCoprime (V.prod.map φ) (A.map φ) := by
    induction V using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_left (x:=A.map φ))
    | cons f V ih =>
      rw [Multiset.prod_cons, Polynomial.map_mul]
      exact (every f (Multiset.mem_cons_self ..)).mul_left
        (ih fun g hg => every g (Multiset.mem_cons_of_mem hg))
  have cop := (all U single).of_isCoprime_of_dvd_left ((prod.map (mapRingHom φ)).dvd')
  have nz := Polynomial.resultant_ne_zero (P.map φ) (A.map φ) cop
  rw [natDegree_map_eq_of_injective inj,natDegree_map_eq_of_injective inj,resultant_map_map,vanish,map_zero] at nz
  exact nz rfl

end ArkLib.ProximityGap.Frontier.DoubleInterpolationCommonFactor
#print axioms ArkLib.ProximityGap.Frontier.DoubleInterpolationCommonFactor.exists_common
