/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeInvolutionPairs
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import Mathlib.FieldTheory.Finite.Basic

/-! # Reindexing smooth cosets and realizing three transpositions -/

namespace ProximityGap.SmoothPowerOrbit

/-- Every ordering of a smooth multiplicative coset is a scaled, reindexed primitive orbit. -/
theorem reindex {F I : Type} [Field F] [DecidableEq F] [Fintype I] {n : ℕ}
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I=n) :
    ∃ (z : F) (s : (F)ˣ) (f : I ≃ Fin n), IsPrimitiveRoot z n ∧
      ∀ i, D i=(s : F)*z^(f i).val := by
  classical
  let H := ReedSolomon.Smooth.H D
  obtain ⟨c,hc⟩ := SmoothDomainMcaEquivalence.coset_equiv D
  let : Fintype H := Fintype.ofEquiv I c
  have cH : Fintype.card H=n := (Fintype.card_congr c).symm.trans hn
  obtain ⟨g,hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := H)).mp inferInstance
  let z := ((g : (F)ˣ) : F)
  have hz : IsPrimitiveRoot z n := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf ((g : (F)ˣ) : F)=n
    rw [orderOf_units,Subgroup.orderOf_coe,hg,Nat.card_eq_fintype_card,cH]
  let idx (i : Fin n) : H := g^i.val
  have inj : Function.Injective idx := fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt
    (congrArg (fun b : H => ((b : (F)ˣ) : F)) h))
  let e := Equiv.ofBijective idx ((Fintype.bijective_iff_injective_and_card idx).mpr
    ⟨inj,(Fintype.card_fin _).trans cH.symm⟩)
  refine ⟨z,ReedSolomon.Smooth.a D,c.trans e.symm,hz,fun i => (hc i).trans ?_⟩
  congr 1
  exact congrArg (fun b : H => ((b : (F)ˣ) : F)) (e.apply_symm_apply (c i)).symm

/-- Every smooth coset of even order at least eight has a non-dihedral involution exchanging three disjoint pairs. -/
theorem sharp {F I : Type} [Field F] [DecidableEq F] [Fintype I] {m : ℕ} (hm : 4≤m)
    (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I=2*m) :
    ∃ (q : Fin 3 × Fin 2 ↪ I) (a b c : F), a≠0 ∧ c≠0 ∧ a^2+b*c≠0 ∧
      ∀ i : Fin 3, c*D (q (i,0))*D (q (i,1))-a*(D (q (i,0))+D (q (i,1)))=b := by
  obtain ⟨z,s,f,hz,hD⟩ := reindex D hn
  let q := ThreeInvolutionPairs.points m hm
  obtain ⟨a,b,c,ha,hc,det,law⟩ := ThreeInvolutionPairs.sharp m hm z hz
  refine ⟨q.trans f.symm.toEmbedding,a*(s:F),b*(s:F)^2,c,
    mul_ne_zero ha s.ne_zero,hc,?_,?_⟩
  · rw [show (a*(s:F))^2+(b*(s:F)^2)*c=(a^2+b*c)*(s:F)^2 by ring]
    exact mul_ne_zero det (pow_ne_zero _ s.ne_zero)
  · intro i
    simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,hD,Equiv.apply_symm_apply]
    change c*((s:F)*z^(q (i,0)).val)*((s:F)*z^(q (i,1)).val)-
      (a*(s:F))*((s:F)*z^(q (i,0)).val+(s:F)*z^(q (i,1)).val) = b*(s:F)^2
    have h := law i
    change c*z^(q (i,0)).val*z^(q (i,1)).val-a*(z^(q (i,0)).val+z^(q (i,1)).val)=b at h
    linear_combination (s:F)^2*h

end ProximityGap.SmoothPowerOrbit
#print axioms ProximityGap.SmoothPowerOrbit.sharp
