/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadColored
import ArkLib.Research.ProximityGap.Frontier.FourHeadQuotient

/-! # Distinct scalar labels for the transverse four-head construction -/

namespace ProximityGap.QuarterTransverseKeys

open Finset ArkLib.ProximityGap.Frontier.SmoothFourHeadColored

variable {I F : Type} [Fintype I] [Field F] [Fintype F]

/-- Sites contributing a scalar independent of the projection parameter. -/
def ordinary (col : I → Fin 8) : Finset I := univ.filter fun x => col x ∈ ordinaryClasses

/-- Ordinary sites contributing a second scalar from the owner. -/
def variableSites (col : I → Fin 8) : Finset I :=
  univ.filter fun x => col x ∈ ordinaryClasses ∧ col x ≠ 2

/-- Class seven contributes one scalar for each of the three original heads. -/
def holes (col : I → Fin 8) : Finset I := univ.filter fun x => col x = 7

/-- Number of scalar labels from the three classes of contributions. -/
def mass (col : I → Fin 8) : ℕ :=
  (ordinary col).card + (variableSites col).card + 3 * (holes col).card

private abbrev Slot (col : I → Fin 8) :=
  ↥(ordinary col) ⊕ (↥(variableSites col) ⊕ (↥(holes col) × Fin 3))

private def info (col : I → Fin 8) (v : Fin 3 → I → F) : Slot col → I × Option F
  | .inl x => (x.val, none)
  | .inr (.inl x) => (x.val, some (v (owner (col x.val)) x.val))
  | .inr (.inr (x, j)) => (x.val, some (v j x.val))

omit [Field F] [Fintype F] in
private theorem info_injective (col : I → Fin 8) (v : Fin 3 → I → F)
    (h7 : ∀ x, col x = 7 → Function.Injective (fun j => v j x)) :
    Function.Injective (info col v) := by
  have ne (x : ↥(variableSites col)) (y : ↥(holes col)) : x.val ≠ y.val := by
    intro e
    have hx := ((mem_filter.mp x.property).2).1
    have hy := (mem_filter.mp y.property).2
    rw [e, hy] at hx
    exact (by decide : (7 : Fin 8) ∉ ordinaryClasses) hx
  intro i j hij
  rcases i with x | x | ⟨x,r⟩ <;> rcases j with y | y | ⟨y,s⟩ <;>
    simp only [info, Option.some.injEq, and_true, Sum.inl.injEq, Sum.inr.injEq,
      Option.some_ne_none, reduceCtorEq, and_false, Prod.ext_iff] at hij ⊢
  · exact Subtype.ext hij
  · exact Subtype.ext hij.1
  · exact (ne x y hij.1).elim
  · exact (ne y x hij.1.symm).elim
  · obtain ⟨e,hv⟩ := hij
    obtain rfl := Subtype.ext e
    exact ⟨rfl, h7 _ (mem_filter.mp x.property).2 hv⟩

omit [Field F] in
private theorem avoid (v : Fin 3 → I → F) (hq : 3 * Fintype.card I < Fintype.card F) :
    ∃ c : F, ∀ j x, c ≠ v j x := by
  classical
  let vals (p : Fin 3 × I) := v p.1 p.2
  have hcard : (univ.image vals).card < (univ : Finset F).card := by
    apply card_image_le.trans_lt
    simpa using hq
  obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, fun j x e => hc (e ▸ mem_image_of_mem vals (mem_univ (j,x)))⟩

/-- A single denominator shift avoids every value, and a single projection parameter
makes all ordinary, owner and class-seven scalars distinct. -/
theorem exists_labels (D : I ↪ F) (col : I → Fin 8) (v : Fin 3 → I → F)
    (h7 : ∀ x, col x = 7 → Function.Injective (fun j => v j x))
    (hcField : 3 * Fintype.card I < Fintype.card F)
    (hField : (mass col) ^ 2 < Fintype.card F) :
    ∃ (a c : F) (G : Finset F), (∀ i x, c ≠ v i x) ∧ G.card = mass col ∧
      ∀ γ ∈ G, (∃ x ∈ ordinary col, γ = -D x) ∨
        (∃ x ∈ variableSites col, γ = -D x - a / (c - v (owner (col x)) x)) ∨
        (∃ x ∈ holes col, ∃ j, γ = -D x - a / (c - v j x)) := by
  classical
  obtain ⟨c,hc⟩ := avoid v hcField
  let slope : Option F → F := fun z => z.elim 0 (fun r => -(c-r)⁻¹)
  let key (i : Slot col) : F × F := (-D (info col v i).1, slope (info col v i).2)
  have valid (i : Slot col) : (info col v i).2 ≠ some c := by
    rcases i with x | x | ⟨x,j⟩ <;> simp [info, ne_comm, hc]
  have slope_inj {r s : Option F} (hr : r ≠ some c) (hs : s ≠ some c)
      (he : slope r = slope s) : r = s := by
    cases r <;> cases s <;> simp_all [slope, sub_eq_zero]
  have ki : Function.Injective key := by
    intro i j h
    apply info_injective col v h7
    exact Prod.ext (D.injective (neg_inj.mp (congrArg Prod.fst h)))
      (slope_inj (valid i) (valid j) (congrArg Prod.snd h))
  have hcard : Fintype.card (Slot col) = mass col := by
    simp [Slot, mass, Nat.add_assoc, Nat.mul_comm]
  let keys := univ.image key
  have hk : keys.card = mass col := by rw [card_image_of_injective _ ki, card_univ, hcard]
  obtain ⟨a,ha⟩ := FourHeadQuotient.exists_injective_affine_labels keys (by rwa [hk, ← pow_two])
  let label (i : Slot col) := (key i).1 + a * (key i).2
  have hi : Function.Injective label := fun i j h =>
    ki (ha (mem_image_of_mem key (mem_univ i)) (mem_image_of_mem key (mem_univ j)) h)
  refine ⟨a,c,univ.image label,hc,?_,?_⟩
  · rw [card_image_of_injective _ hi, card_univ, hcard]
  · intro γ h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    rcases i with x | x | ⟨x,j⟩
    · exact Or.inl ⟨x,x.property,by simp [label,key,info,slope]⟩
    · exact Or.inr (Or.inl ⟨x,x.property,by
        simp [label,key,info,slope,div_eq_mul_inv,sub_eq_add_neg]⟩)
    · exact Or.inr (Or.inr ⟨x,x.property,j,by
        simp [label,key,info,slope,div_eq_mul_inv,sub_eq_add_neg]⟩)

end ProximityGap.QuarterTransverseKeys
