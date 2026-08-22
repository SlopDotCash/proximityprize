/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R314KernelRelationMassDecomposition

/-!
# R327: endpoint fibers force many realized kernel relations

R326 reduces the field-energy upper bound to the cardinality of
`shadowKernelRelations`.  This file proves the opposite, unavoidable pigeonhole pressure.
Every evaluation fiber of the characteristic-zero shadow key set, after choosing one
basepoint, injects into the realized relation set by subtraction.  Consequently

```text
card(keysR) <= card(F) * (card(shadowKernelRelations) + 1).
```

This is an exact obstruction to trying to bound relation cardinality without also using
the highly non-uniform relation masses: at logarithmic depth the key set is already much
larger than the field.

Issue #466, round 327.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Translation away from a fixed left endpoint is injective. -/
theorem shadowDifference_fixed_left_injective {m : ℕ} (v : Fin m → ℤ) :
    Function.Injective (fun w ↦ shadowDifference (v, w)) := by
  intro w₁ w₂ h
  funext j
  have hj := congrFun h j
  simp only [shadowDifference] at hj
  omega

/-- A non-basepoint in one evaluation fiber produces a realized relation. -/
theorem shadowDifference_mem_kernelRelations_of_mem_fiber
    (g : F) (n m r : ℕ) (c : F) {v w : Fin m → ℤ}
    (hv : v ∈ (keysR n m r).filter (fun z ↦ evalVec g m z = c))
    (hw : w ∈ (keysR n m r).filter (fun z ↦ evalVec g m z = c))
    (hvw : w ≠ v) :
    shadowDifference (v, w) ∈ shadowKernelRelations g n m r := by
  classical
  unfold shadowKernelRelations
  apply Finset.mem_image_of_mem
  unfold shadowCollisionPairs
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_offDiag]
    exact ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hw).1, hvw.symm⟩
  · rw [(Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hw).2]

/-- Each evaluation fiber has at most one plus the number of realized differences. -/
theorem shadowFiber_card_le_relation_card_succ
    (g : F) (n m r : ℕ) (c : F) :
    ((keysR n m r).filter (fun v ↦ evalVec g m v = c)).card
      ≤ (shadowKernelRelations g n m r).card + 1 := by
  classical
  let S := (keysR n m r).filter (fun v ↦ evalVec g m v = c)
  rcases S.eq_empty_or_nonempty with hS | ⟨v, hv⟩
  · simp [S, hS]
  · have hcard : (S.erase v).card ≤ (shadowKernelRelations g n m r).card := by
      apply Finset.card_le_card_of_injOn
        (fun w ↦ shadowDifference (v, w))
      · intro w hw
        rw [Finset.mem_coe]
        have hw' := Finset.mem_erase.mp hw
        exact shadowDifference_mem_kernelRelations_of_mem_fiber g n m r c hv hw'.2 hw'.1
      · exact (shadowDifference_fixed_left_injective v).injOn
    have herase := Finset.card_erase_add_one hv
    change S.card ≤ _
    omega

/-- **FIBER LOWER BOUND.**  The whole shadow key set is at most the field cardinality times
one plus the realized relation count.  Equivalently, large endpoint entropy forces many
distinct sparse kernel relations before any resultant or recurrence classification enters. -/
theorem keysR_card_le_field_card_mul_relation_card_succ
    (g : F) (n m r : ℕ) :
    (keysR n m r).card ≤ Fintype.card F * ((shadowKernelRelations g n m r).card + 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (t := (Finset.univ : Finset F))
    (f := fun v ↦ evalVec g m v)
    (fun v _ ↦ Finset.mem_univ (evalVec g m v))]
  calc
    (∑ c : F, ((keysR n m r).filter (fun v ↦ evalVec g m v = c)).card)
        ≤ ∑ _c : F, ((shadowKernelRelations g n m r).card + 1) :=
      Finset.sum_le_sum (fun c _ ↦ shadowFiber_card_le_relation_card_succ g n m r c)
    _ = Fintype.card F * ((shadowKernelRelations g n m r).card + 1) := by simp

/-! ## A large explicit family of characteristic-zero endpoints -/

/-- The squarefree positive shadow endpoint attached to a subset of coordinates. -/
def positiveSubsetKey {m : ℕ} (S : Finset (Fin m)) : Fin m → ℤ :=
  fun j ↦ if j ∈ S then 1 else 0

/-- Enumerate a cardinality-`r` subset in the positive half of `Fin (2m)`. -/
noncomputable def positiveSubsetTuple {m r : ℕ} (S : Finset (Fin m))
    (hS : S.card = r) : Fin r → Fin (2 * m) :=
  fun i ↦
    let x : S := (S.equivFinOfCardEq hS).symm i
    ⟨(x : ℕ), by have := x.1.isLt; omega⟩

/-- Enumerating a subset once in the positive half realizes its indicator endpoint. -/
theorem tupleVec_positiveSubsetTuple {m r : ℕ} (S : Finset (Fin m))
    (hS : S.card = r) :
    tupleVec (2 * m) m r (positiveSubsetTuple S hS) = positiveSubsetKey S := by
  classical
  funext j
  unfold tupleVec positiveSubsetTuple positiveSubsetKey
  let e : Fin r ≃ S := (S.equivFinOfCardEq hS).symm
  have hsecond : ∀ i : Fin r, (e i : ℕ) ≠ (j : ℕ) + m := by
    intro i
    have hi := (e i).1.isLt
    omega
  change (∑ i : Fin r,
      ((if (e i : ℕ) = (j : ℕ) then (1 : ℤ) else 0) -
        (if (e i : ℕ) = (j : ℕ) + m then 1 else 0))) =
    (if j ∈ S then 1 else 0)
  have hzero : ∀ i : Fin r,
      (if (e i : ℕ) = (j : ℕ) + m then (1 : ℤ) else 0) = 0 := by
    intro i
    rw [if_neg (hsecond i)]
  simp_rw [hzero]
  simp only [sub_zero]
  have hfirst : ∀ i : Fin r,
      (if (e i : ℕ) = (j : ℕ) then (1 : ℤ) else 0) =
        (if (e i : Fin m) = j then 1 else 0) := by
    intro i
    congr 1
    simp only [Fin.ext_iff]
  simp_rw [hfirst]
  rw [e.sum_comp (fun x : S ↦ if (x : Fin m) = j then (1 : ℤ) else 0)]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    rw [Fintype.sum_eq_single (⟨j, hj⟩ : S)]
    · simp
    · intro x hx
      rw [if_neg]
      exact fun h ↦ hx (Subtype.ext h)
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro x _hx
    rw [if_neg]
    intro h
    exact hj (h ▸ x.property)

/-- Distinct subsets have distinct indicator endpoints. -/
theorem positiveSubsetKey_injective {m : ℕ} :
    Function.Injective (@positiveSubsetKey m) := by
  intro S T h
  ext j
  have hj := congrFun h j
  simp only [positiveSubsetKey] at hj
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp_all

/-- Every cardinality-`r` coordinate subset gives a distinct depth-`r` shadow key. -/
theorem choose_le_keysR_card (m r : ℕ) :
    m.choose r ≤ (keysR (2 * m) m r).card := by
  classical
  calc
    m.choose r = ((Finset.univ : Finset (Fin m)).powersetCard r).card := by simp
    _ ≤ (keysR (2 * m) m r).card := by
      apply Finset.card_le_card_of_injOn (@positiveSubsetKey m)
      · intro S hS
        rw [Finset.mem_coe]
        have hcard := (Finset.mem_powersetCard.mp hS).2
        rw [keysR, Finset.mem_image]
        exact ⟨positiveSubsetTuple S hcard, Finset.mem_univ _,
          tupleVec_positiveSubsetTuple S hcard⟩
      · exact positiveSubsetKey_injective.injOn

/-- **QUANTITATIVE COUNT OBSTRUCTION.**  At depth `r`, even just the squarefree positive
endpoints force the binomial lower pressure

`choose(m,r) <= card(F) * (card(shadowKernelRelations)+1)`.

Thus a count bound of size `C^r` can only hold where `choose(m,r) <= card(F)*(C^r+1)`;
in the prize saddle `r` grows logarithmically with `m`, and the left side has
`exp(Theta(r log(m/r)))` rather than merely `exp(O(r))` growth. -/
theorem choose_le_field_card_mul_relation_card_succ
    (g : F) (m r : ℕ) :
    m.choose r ≤
      Fintype.card F * ((shadowKernelRelations g (2 * m) m r).card + 1) :=
  (choose_le_keysR_card m r).trans
    (keysR_card_le_field_card_mul_relation_card_succ g (2 * m) m r)

/-- A proposed relation-count ceiling `D` is refuted whenever the squarefree positive
endpoint count exceeds the total capacity of `card(F)` fibers of size `D+1`. -/
theorem not_relation_card_le_of_field_mul_succ_lt_choose
    (g : F) (m r D : ℕ)
    (hlarge : Fintype.card F * (D + 1) < m.choose r) :
    ¬ (shadowKernelRelations g (2 * m) m r).card ≤ D := by
  intro hD
  have hforced := choose_le_field_card_mul_relation_card_succ g m r
  have hmono :
      Fintype.card F * ((shadowKernelRelations g (2 * m) m r).card + 1)
        ≤ Fintype.card F * (D + 1) := by
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hD 1)
  omega

end ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound.shadowFiber_card_le_relation_card_succ
#print axioms
  ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound.keysR_card_le_field_card_mul_relation_card_succ
#print axioms
  ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound.choose_le_keysR_card
#print axioms
  ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound.choose_le_field_card_mul_relation_card_succ
#print axioms
  ArkLib.ProximityGap.Frontier.R327RelationCountFiberLowerBound.not_relation_card_le_of_field_mul_succ_lt_choose
