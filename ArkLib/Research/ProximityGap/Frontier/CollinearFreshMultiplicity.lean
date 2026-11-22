/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.EighthCollinearOutlier

/-! # Weighted fresh-coordinate incidence on collinear polynomial heads -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.CollinearFreshMultiplicity
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantMultiplicity
open HalfPredecessorRateQuarterDeterminantCollapse HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterCollapsedClusterInjection
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open _root_.ProximityGap
variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [DecidableEq I]
variable [Nonempty I] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

abbrev core (dom : I ↪ F) (u : WordStack F (Fin 2) I) (z : LineParameter F) :=
  jointCore dom (u 0) (u 1) z.1 z.2

/-- Labels are assigned disjointly to heads. A head with a deficit of `a`
agreements charges each assigned scalar at least `max 1 a` times. Across all heads
the charges at a site owned by the same polynomial line occupy one scalar slot.
At a common site of all selected heads there are no charges. -/
theorem weighted {s k : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    (a b : LineParameter F) (ab : a ≠ b) (L : Fin s → LineParameter F)
    (G : Fin s → Finset F) (hl : ∀ i, L i ∈ lineParameters fam)
    (assign : ∀ i, G i ⊆ pointsOn fam (L i))
    (dis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (U D : Finset I) (owned : ∀ x ∈ U, ∃ w, x ∈ core dom u w ∧ lineDeterminant a b w = 0)
    (common : ∀ i, D ⊆ core dom u (L i)) :
    let t := ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊
    (∑ i, max 1 (t - (core dom u (L i)).card) * (G i).card) ≤
      (U \ D).card + (Fintype.card I - U.card) * s := by
  classical
  let t := ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊
  let J := (i : Fin s) × ↥(G i)
  let z (p : J) : F := p.2.val
  let w (p : J) := L p.1
  let S (p : J) := fullAgreement dom (u 0) (u 1) (z p) (fam.q (z p))
  let fresh (p : J) := S p \ core dom u (w p)
  have data (p : J) : z p ∈ fam.G ∧ fam.q (z p) = (w p).1 + C (z p) * (w p).2 :=
    (mem_pointsOn_iff fam _ _).mp (assign p.1 p.2.property)
  have mass (p : J) : max 1 (t - (core dom u (w p)).card) ≤ (fresh p).card := by
    have deg := lineParameter_degree_lt fam (hl p.1)
    have non := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
      _ (w p).1 (w p).2 deg.1 deg.2 (fam.noJoint _ (data p).1)
    obtain ⟨x,hx,hn⟩ := Finset.not_subset.mp non
    have hp : 0 < (fresh p).card := card_pos.mpr ⟨x,mem_sdiff.mpr ⟨hx,hn⟩⟩
    have hit : t ≤ (S p).card := fam.threshold_le _ (data p).1
    have hcut := card_sdiff_add_card_inter (S p) (core dom u (w p))
    have hlim := card_le_card (inter_subset_right (s₁ := S p) (s₂ := core dom u (w p)))
    dsimp only [fresh] at *
    omega
  have zinj : Function.Injective z := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    change x.val = y.val at eq
    have ij : i = j := by
      by_contra ne
      exact disjoint_left.mp (dis i j ne) x.property (show x.val ∈ G j from eq.symm ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext eq)
  let T (x : I) := univ.filter fun p : J => x ∈ fresh p
  have same (x : I) (xu : x ∈ U) : (T x).card ≤ 1 := by
    obtain ⟨r,xr,rc⟩ := owned x xu
    have fixed (p : J) (hp : p ∈ T x) : z p = primitiveScalarAt a b (dom x) := by
      obtain ⟨xs,xc⟩ := mem_sdiff.mp (mem_filter.mp hp).2
      change x ∈ fullAgreement dom (u 0) (u 1) (z p) (fam.q (z p)) at xs
      rw [(data p).2] at xs
      have ht := transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
        dom (u 0) (u 1) (w p) r (z p) xs xr xc
      have hp := pairEquation_of_mem_fullAgreement_of_mem_jointCore dom (u 0) (u 1) (w p) r (z p) xs xr
      exact gamma_eq_primitiveScalarAt_of_pairEquation a b (w p) r ab (coll p.1) rc ht hp
    exact card_le_one.mpr fun p hp q hq => zinj ((fixed p hp).trans (fixed q hq).symm)
  have outside (x : I) : (T x).card ≤ s := by
    apply le_trans (card_le_card_of_injOn (fun p : J => p.1) (fun _ _ => mem_univ _) ?_)
      (show (univ : Finset (Fin s)).card ≤ s by simp)
    rintro ⟨i,p⟩ hp ⟨j,q⟩ hq e
    change i = j at e
    subst j
    apply congrArg (Sigma.mk i)
    apply Subtype.ext
    by_contra ne
    have h1 := (mem_filter.mp hp).2
    have h2 := (mem_filter.mp hq).2
    dsimp only [fresh,S] at h1 h2
    rw [(data _).2] at h1 h2
    exact disjoint_left.mp (freshAgreement_disjoint dom (u 0) (u 1) (L i).1 (L i).2 ne) h1 h2
  have local_count (x : I) : (T x).card ≤
      (if x ∈ U \ D then 1 else 0) + (if x ∈ Uᶜ then s else 0) := by
    by_cases h : x ∈ D
    · have none : T x = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp =>
        (mem_sdiff.mp (mem_filter.mp hp).2).2 (common p.1 h)
      simp [none]
    by_cases hu : x ∈ U
    · simpa [h,hu] using same x hu
    · simpa [h,hu] using outside x
  have total := sum_le_sum (s := univ) fun x _ => local_count x
  have cut (D : Finset I) (m : ℕ) : (∑ x : I, if x ∈ D then m else 0) = D.card * m := by
    simp
  rw [sum_add_distrib,cut,cut,card_compl,mul_one] at total
  change (∑ x, _) ≤ _ at total
  have bound := sum_le_sum (s := univ) fun p _ => mass p
  rw [ArkLib.Coverage.sum_card_eq_sum_degree] at bound
  exact (by simpa only [Fintype.sum_sigma, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul,
    mul_comm, J, w, t, Nat.cast_id] using bound.trans total)

#print axioms weighted
end ArkLib.ProximityGap.Frontier.CollinearFreshMultiplicity
