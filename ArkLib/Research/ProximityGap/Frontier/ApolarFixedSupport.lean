/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarMcaSyndrome
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorSecantLines

/-! # A fixed apolar locator bounds the bad-parameter count

All genuine errors on each selected full agreement complement are roots of
a common locator over the coefficient extension. The complementary core fixes
a single polynomial line, whose fresh agreements pack into these roots.
-/

set_option autoImplicit false
open Finset Polynomial Code _root_.ProximityGap
open _root_.ProximityGap.ApolarDividedLocator _root_.ProximityGap.ApolarMcaSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open scoped NNReal BigOperators

namespace ArkLib.ProximityGap.Frontier.ApolarFixedSupport

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- If all selected full agreement sets contain a common \(k\)-point core,
the bad scalars use distinct fresh positions outside that core. -/
theorem count_le_complement_of_common_agreements (fam : BadScalarRichPointFamily dom k δ u)
    (G : Finset F) (hG : G ⊆ fam.G) (hpair : 1 < G.card)
    (C₀ : Finset ι) (hk : 1 ≤ k) (hsize : k ≤ C₀.card)
    (hcommon : ∀ t ∈ G, C₀ ⊆ fullAgreement dom (u 0) (u 1) t (fam.q t)) :
    G.card ≤ Fintype.card ι - C₀.card := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hpair
  let l := secantParameter fam a b
  let D := jointCore dom (u 0) (u 1) l.1 l.2
  have hl : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam (hG ha) (hG hb) hab
  have hal := (mem_pointsOn_iff fam l a).mp
    (first_point_mem_pointsOn_secant fam (beta := b) (hG ha)) |>.2
  have hbl := (mem_pointsOn_iff fam l b).mp
    (second_point_mem_pointsOn_secant fam (hG hb) hab) |>.2
  have hD : C₀ ⊆ D := by
    rw [show D = fullAgreement dom (u 0) (u 1) a (fam.q a) ∩
        fullAgreement dom (u 0) (u 1) b (fam.q b) by
      rw [hal,hbl]; exact (fullAgreement_inter_eq_jointCore dom (u 0) (u 1) l.1 l.2 hab).symm]
    exact Finset.subset_inter (hcommon a ha) (hcommon b hb)
  have hdeg := lineParameter_degree_lt fam hl
  have hline : G ⊆ pointsOn fam l := by
    intro t ht
    apply (mem_pointsOn_iff fam l t).mpr
    refine ⟨hG ht, ?_⟩
    by_contra hoff
    have hc := fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
      (fam.degree_lt t (hG ht)) hdeg.1 hdeg.2 hoff
    have hs := Finset.card_le_card (Finset.subset_inter (hcommon t ht) hD)
    dsimp only [D] at hs
    omega
  have hp := pointsOn_card_mul_max_add_core_le fam hl
  have hmul : (pointsOn fam l).card ≤ (pointsOn fam l).card *
      max 1 (⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊ - D.card) := by
    simpa using Nat.mul_le_mul_left (pointsOn fam l).card (le_max_left 1
      (⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊ - D.card))
  have hg := Finset.card_le_card hline
  have hd := Finset.card_le_card hD
  change (pointsOn fam l).card * max 1 (⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊ - D.card) + D.card ≤ _ at hp
  omega

omit [Fintype F] in
/-- Reduced error support is contained in the roots even when the common
locator is defined over a field extension of the evaluation alphabet. -/
private theorem root_of_reduced_over_extension {L : Type*} [Field L] (φ : F →+* L)
    (E : Finset F) (w : F → F) (f : L[X]) {a : ℕ} (hs : E.card ≤ a+1)
    (ha : ApolarThrough (weighted E φ w) f a)
    {y : F} (hy : y ∈ E) (hw : w y ≠ 0) : f.IsRoot (φ y) := by
  classical
  let B := Lagrange.nodal (E.erase y) φ
  have hb : B.natDegree ≤ a := by
    rw [show B.natDegree = (E.erase y).card from Lagrange.natDegree_nodal, card_erase_of_mem hy]
    omega
  have hn : B.eval (φ y) ≠ 0 := Lagrange.eval_nodal_not_at_node
    (fun z hz => φ.injective.ne (mem_erase.mp hz).1.symm)
  have h := ha B hb
  rw [weighted_apply, sum_eq_single_of_mem y hy (fun z hz hzy => by
    rw [eval_mul, show B.eval (φ z) = 0 from
      Lagrange.eval_nodal_at_node (mem_erase.mpr ⟨hzy,hz⟩), mul_zero, mul_zero])] at h
  rw [eval_mul] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ((map_ne_zero φ).mpr hw))).resolve_right hn

private theorem rowWeight_ne_zero {T : Type*} [Field T] (H : Finset T)
    (v : T → T) (x : T) (h : v x ≠ 0) : rowWeight H v x ≠ 0 := by
  classical
  unfold rowWeight
  apply div_ne_zero h
  exact Finset.prod_ne_zero_iff.mpr (fun _ hz => sub_ne_zero.mpr (Finset.mem_erase.mp hz).1.symm)

/-- A nonzero fixed locator over any field extension of degree at most \(n-k\)
bounds each selected genuinely bad family by its own degree. -/
theorem count_le_fixed_locator_degree {L : Type*} [Field L] [DecidableEq L] (φ : F →+* L)
    (fam : BadScalarRichPointFamily dom k δ u) (G : Finset F) (hG : G ⊆ fam.G)
    (hpair : 1 < G.card) (f : L[X]) (hf : f ≠ 0) (a e : ℕ) (hk : 1 ≤ k)
    (hroom : k + f.natDegree + a < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) (ha : e ≤ a+1)
    (hdual : ∀ t ∈ G, ApolarThrough (syndrome ((univ : Finset ι).map dom) φ
      (fun y => coordinateRow dom (u 0) y + t * coordinateRow dom (u 1) y)) f a) :
    G.card ≤ f.natDegree := by
  classical
  let H := (univ : Finset ι).map dom
  let emb : ι ↪ L := dom.trans ⟨φ,φ.injective⟩
  let roots := (univ : Finset ι).filter fun i => f.eval (emb i) = 0
  have hroots : roots.card ≤ f.natDegree := by
    by_contra! hsmall
    apply hf
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero f
      (f := fun i : roots => emb i.val) (emb.injective.comp Subtype.val_injective)
    · intro i
      exact (Finset.mem_filter.mp i.property).2
    · simpa using hsmall
  have hcard : rootsᶜ.card = Fintype.card ι - roots.card := Finset.card_compl roots
  have hcommon (t : F) (ht : t ∈ G) :
      rootsᶜ ⊆ fullAgreement dom (u 0) (u 1) t (fam.q t) := by
    let A := fullAgreement dom (u 0) (u 1) t (fam.q t)
    let E := Aᶜ.map dom
    let v (y : F) := coordinateRow dom (u 0) y + t * coordinateRow dom (u 1) y
    let w := rowWeight H (fun y => v y - (fam.q t).eval y)
    have hEH : E ⊆ H := Finset.map_subset_map.mpr (Finset.subset_univ _)
    have hEs : E.card ≤ e := by
      have hth := fam.threshold_le t (hG ht)
      change _ ≤ A.card at hth
      simp only [E,card_map,card_compl]
      omega
    have hoff : ∀ y ∈ H, y ∉ E → v y = (fam.q t).eval y := by
      rintro y hy hn
      obtain ⟨i,_,rfl⟩ := mem_map.mp hy
      have hi : i ∈ A := by
        by_contra h
        exact hn (Finset.mem_map.mpr ⟨i, Finset.mem_compl.mpr h,rfl⟩)
      symm
      simpa [A,fullAgreement,v] using hi
    have hred : ApolarThrough (weighted E φ w) f a := by
      intro B hb
      have hd := fam.degree_lt t (hG ht)
      have hprod : (f*B).natDegree ≤ f.natDegree+B.natDegree := natDegree_mul_le
      have hfit : (fam.q t).natDegree + (f*B).natDegree < H.card-1 := by
        simp only [H,card_map,card_univ]
        omega
      rw [← syndrome_reduced H E v (fam.q t) (f*B) φ hEH hoff hfit]
      exact hdual t ht B hb
    intro i hi
    by_contra hnot
    have hm : dom i ∈ E := Finset.mem_map.mpr ⟨i, Finset.mem_compl.mpr hnot, rfl⟩
    have hwrong : v (dom i) ≠ (fam.q t).eval (dom i) := by
      intro hv
      apply hnot
      simpa [fullAgreement,v] using hv.symm
    have hnz : w (dom i) ≠ 0 := rowWeight_ne_zero H _ _ (sub_ne_zero.mpr hwrong)
    have hroot := root_of_reduced_over_extension φ E w f (hEs.trans ha) hred hm hnz
    exact (Finset.mem_compl.mp hi) (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hroot⟩)
  have hbound := count_le_complement_of_common_agreements fam G hG hpair rootsᶜ hk
    (by omega) hcommon
  omega


/-- Monomial recurrence equations suffice for all the required multiples of
the fixed locator, by two coefficient expansions. -/
theorem apolar_of_moment_equations {L : Type*} [Field L]
    (A : L[X] →ₗ[L] L) (f : L[X]) (a : ℕ)
    (hm : ∀ j ≤ a, ∑ i ∈ range (f.natDegree+1), f.coeff i * A (X^(i+j)) = 0) :
    ApolarThrough A f a := by
  classical
  have hmon (j : ℕ) (hj : j ≤ a) : A (f * X^j) = 0 := by
    calc
      _ = A ((∑ i ∈ range (f.natDegree+1), C (f.coeff i) * X^i) * X^j) :=
        congrArg (fun z => A (z * X^j)) f.as_sum_range_C_mul_X_pow
      _ = ∑ i ∈ range (f.natDegree+1), f.coeff i * A (X^(i+j)) := by
        rw [Finset.sum_mul, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_assoc, ← pow_add, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      _ = 0 := hm j hj
  intro B hB
  calc
    _ = A (f * (∑ j ∈ range (B.natDegree+1), C (B.coeff j) * X^j)) :=
      congrArg (fun z => A (f * z)) B.as_sum_range_C_mul_X_pow
    _ = 0 := by
      rw [Finset.mul_sum, map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      have hh : j ≤ a := by have := Finset.mem_range.mp hj; omega
      rw [← mul_assoc, mul_comm f, mul_assoc, ← Polynomial.smul_eq_C_mul,
        map_smul, hmon j hh, smul_zero]

omit [Fintype F] [DecidableEq F] in
/-- A scalar chart of the project's polynomial moment pencil evaluated in an
extension is the actual syndrome of the corresponding affine received word. -/
theorem syndrome_monomial_eq_moment {L : Type*} [Field L] (φ : F →+* L)
    (H : Finset F) (v w : F → F) (t : F) (j : ℕ) :
    syndrome H φ (fun y => v y + t*w y) (X^j) =
      φ (((_root_.ProximityGap.ApolarHankelMinors.moment H v w) j).eval t) := by
  rw [syndrome_pencil]
  simp [ProximityGap.ApolarHankelMinors.moment, syndrome, weighted_apply, eval_finsetSum, add_comm]

/-- Fixed polynomial moment recurrences over an extension directly bound the
number of genuinely MCA-bad scalars by the coordinate degree of the locator. -/
theorem count_le_of_fixed_moment_equations {L : Type*} [Field L] [DecidableEq L] (φ : F →+* L)
    (fam : BadScalarRichPointFamily dom k δ u) (G : Finset F) (hG : G ⊆ fam.G)
    (hpair : 1 < G.card) (f : L[X]) (hf : f ≠ 0) (a e : ℕ) (hk : 1 ≤ k)
    (hroom : k + f.natDegree + a < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) (ha : e ≤ a+1)
    (heqs : let H := (univ : Finset ι).map dom
      let m := _root_.ProximityGap.ApolarHankelMinors.moment H (coordinateRow dom (u 0))
        (coordinateRow dom (u 1))
      ∀ t ∈ G, ∀ j ≤ a, ∑ i ∈ range (f.natDegree+1), f.coeff i * φ ((m (i+j)).eval t) = 0) :
    G.card ≤ f.natDegree := by
  apply count_le_fixed_locator_degree φ fam G hG hpair f hf a e hk hroom he ha
  intro t ht
  apply apolar_of_moment_equations
  intro j hj
  simpa only [syndrome_monomial_eq_moment] using heqs t ht j hj

end ArkLib.ProximityGap.Frontier.ApolarFixedSupport

#print axioms ArkLib.ProximityGap.Frontier.ApolarFixedSupport.count_le_complement_of_common_agreements
#print axioms ArkLib.ProximityGap.Frontier.ApolarFixedSupport.count_le_fixed_locator_degree

#print axioms ArkLib.ProximityGap.Frontier.ApolarFixedSupport.count_le_of_fixed_moment_equations
