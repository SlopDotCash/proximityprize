/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CyclotomicPairDeterminant
import ArkLib.Research.ProximityGap.Frontier.ThreeInvolutionPairs
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import Mathlib.FieldTheory.Finite.Basic

/-! # Every projective involution exchanging four pairs of smooth order-128 sites is dihedral -/

namespace ProximityGap.Smooth128Involutions

open TwoErrorSlice AuxiliaryRatioSlotFacts AuxiliaryRatioSlotData

/-- For all sponsor-size primes, the reflection product is the only product
with at least three representations on a nonantipodal order-128 row. -/
theorem unique_product {p : ℕ} [Fact p.Prime] (hp : 2^128 ≤ p)
    (D : Fin 128 ↪ ZMod p) (z : ZMod p) (hz : IsPrimitiveRoot z 128)
    (hD : ∀ i,D i=z^(i : ℕ)) (u v : Fin 128) (huv : u≠v) (hanti : D u≠-D v)
    (t : ZMod p) (big : 3 ≤ (alternatives D u v t).card) : t=D u/D v := by
  have hp' := (by decide : 128 < 2^128).trans_le hp
  let : NeZero (128 : ZMod p) := ⟨fun h =>
    hp'.not_ge (Nat.le_of_dvd (by decide : 0<128) ((ZMod.natCast_eq_zero_iff 128 p).mp h))⟩
  let : NeZero (128 : F) := ⟨by decide⟩
  apply ReflectionRowTransfer.classify D domain z (root:F) hz primitive hD (fun _ => rfl)
    _ AuxiliaryReflectionRow.six u v huv hanti t big
  intro s hs d hd a b ha hb ha' hb' same
  have pos : 0 < d.val := Nat.pos_of_ne_zero (fun he => hd (Fin.ext he))
  exact CyclotomicPairDeterminant.transfer (by decide : 2<128) hz hs d.val
    (Nat.not_dvd_of_pos_of_lt pos d.isLt) a b ha hb ha' hb' same
    (CyclotomicPairDeterminant.height128 hp)

/-- Every smooth 128-site prime-field domain is a scaled primitive power orbit. -/
theorem power_reindex {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128) :
    ∃ (z : ZMod p) (s : (ZMod p)ˣ) (f : I ≃ Fin 128), IsPrimitiveRoot z 128 ∧
      ∀ i, D i=(s : ZMod p)*z^(f i).val := by
  classical
  let H := ReedSolomon.Smooth.H D
  obtain ⟨c,hc⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let : Fintype H := Fintype.ofEquiv I c
  have cH : Fintype.card H=128 := (Fintype.card_congr c).symm.trans hn
  obtain ⟨g,hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := H)).mp inferInstance
  let z := ((g : (ZMod p)ˣ) : ZMod p)
  have hz : IsPrimitiveRoot z 128 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf ((g : (ZMod p)ˣ) : ZMod p)=128
    rw [orderOf_units,Subgroup.orderOf_coe,hg,Nat.card_eq_fintype_card,cH]
  let idx (i : Fin 128) : H := g^i.val
  have inj : Function.Injective idx := fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt
    (congrArg (fun b : H => ((b : (ZMod p)ˣ) : ZMod p)) h))
  let e := Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).mpr
    ⟨inj,(Fintype.card_fin _).trans cH.symm⟩)
  refine ⟨z,ReedSolomon.Smooth.a D,c.trans e.symm,hz,fun i => (hc i).trans ?_⟩
  congr 1
  exact congrArg (fun b : H => ((b : (ZMod p)ˣ) : ZMod p)) (e.apply_symm_apply (c i)).symm

/-- An involution (ax+b)/(cx−a) exchanging any four disjoint pairs of sites
of any smooth 128-site domain is an inversion x ↦ b/(cx) or the antipodal
rotation x ↦ −x. This holds over all primes at least 2^128. -/
theorem dihedral {p : ℕ} [Fact p.Prime] (hp : 2^128 ≤ p)
    {I : Type} [Fintype I] (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (points : Fin 4 × Fin 2 ↪ I) (a b c : ZMod p) (det : a^2+b*c≠0)
    (law : ∀ i : Fin 4, c*D (points (i,0))*D (points (i,1)) -
      a*(D (points (i,0))+D (points (i,1)))=b) : a=0 ∨ c=0 ∧ b=0 := by
  obtain ⟨z,s,f,hz,hD⟩ := power_reindex D hn
  let E : Fin 128 ↪ ZMod p :=
    ⟨fun i => z^i.val,fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h)⟩
  have nz (i : Fin 128) : E i≠0 := pow_ne_zero i.val (hz.ne_zero (by decide))
  let q := points.trans f.toEmbedding
  have newlaw (i : Fin 4) :
      (c*(s : ZMod p)^2)*E (q (i,0))*E (q (i,1)) -
      (a*(s : ZMod p))*(E (q (i,0))+E (q (i,1)))=b := by
    have h := law i
    simp only [hD] at h
    change c*(s : ZMod p)^2*z^(f (points (i,0))).val*z^(f (points (i,1))).val -
      a*s*(z^(f (points (i,0))).val+z^(f (points (i,1))).val)=b
    linear_combination h
  have det' : (a*(s : ZMod p))^2+b*(c*(s : ZMod p)^2)≠0 := by
    rw [show (a*(s : ZMod p))^2+b*(c*(s : ZMod p)^2)=(a^2+b*c)*(s : ZMod p)^2 by ring]
    exact mul_ne_zero det (pow_ne_zero _ s.ne_zero)
  rcases FourInvolutionPairs.classify E nz (unique_product hp E z hz (fun _ => rfl))
    q _ b _ det' newlaw with h|⟨h,hb⟩
  · exact Or.inl ((mul_eq_zero.mp h).resolve_right s.ne_zero)
  · exact Or.inr ⟨(mul_eq_zero.mp h).resolve_right (pow_ne_zero _ s.ne_zero),hb⟩

/-- Three disjoint transpositions are achieved on every smooth 128-site domain
by a non-dihedral projective involution. -/
theorem sharp {p : ℕ} [Fact p.Prime] {I : Type} [Fintype I]
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128) :
    ∃ (q : Fin 3 × Fin 2 ↪ I) (a b c : ZMod p), a≠0 ∧ c≠0 ∧ a^2+b*c≠0 ∧
      ∀ i : Fin 3, c*D (q (i,0))*D (q (i,1))-a*(D (q (i,0))+D (q (i,1)))=b := by
  obtain ⟨z,s,f,hz,hD⟩ := power_reindex D hn
  let q := ThreeInvolutionPairs.points 64 (by decide)
  obtain ⟨a,b,c,ha,hc,det,law⟩ := ThreeInvolutionPairs.sharp 64 (by decide) z hz
  refine ⟨q.trans f.symm.toEmbedding,a*(s:ZMod p),b*(s:ZMod p)^2,c,
    mul_ne_zero ha s.ne_zero,hc,?_,?_⟩
  · rw [show (a*(s:ZMod p))^2+(b*(s:ZMod p)^2)*c=(a^2+b*c)*(s:ZMod p)^2 by ring]
    exact mul_ne_zero det (pow_ne_zero _ s.ne_zero)
  · intro i
    simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,hD,Equiv.apply_symm_apply]
    change c*((s:ZMod p)*z^(q (i,0)).val)*((s:ZMod p)*z^(q (i,1)).val)-
      (a*(s:ZMod p))*((s:ZMod p)*z^(q (i,0)).val+(s:ZMod p)*z^(q (i,1)).val) = b*(s:ZMod p)^2
    have h := law i
    change c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b at h
    linear_combination (s:ZMod p)^2*h

end ProximityGap.Smooth128Involutions

#print axioms ProximityGap.Smooth128Involutions.unique_product
#print axioms ProximityGap.Smooth128Involutions.dihedral

#print axioms ProximityGap.Smooth128Involutions.sharp
