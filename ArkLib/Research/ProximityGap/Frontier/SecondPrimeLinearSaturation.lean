/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeHeadDescent
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant

/-! # Saturation of a value-linear component by selected polynomial sections -/
namespace ArkLib.ProximityGap.Frontier.SecondPrimeLinearSaturation
open Finset Polynomial
open HalfPredecessorLineCoreGeometry HalfPredecessorBadEventRichPointBridge
open SecondPrimeActualPopulations
open scoped NNReal

private theorem transpose_count {α β : Type*} (M : Finset α) (N : Finset β) (p : α → β → Prop)
    [∀ z i, Decidable (p z i)] :
    ∑ z ∈ M, (N.filter (p z)).card = ∑ i ∈ N, (M.filter (p · i)).card := by
  simp_rw [Finset.card_filter]
  rw [sum_comm]

/-- At 185 labels, the per-site bounds 34 off the identity sites and 33 missed on them
force 35 rich labels whose every three agreement sets meet in more than the degree. -/
theorem triple_rich_subset {F I : Type*} [Fintype I] [DecidableEq I]
    (M : Finset F) (U : Finset I) (A : F → Finset I)
    (hn : Fintype.card I = 1073741824) (hm : M.card = 185)
    (ht : ∀ z ∈ M, 357913943 ≤ (A z).card)
    (hreg : ∀ i, i ∉ U → (M.filter fun z => i ∈ A z).card ≤ 34)
    (hsing : ∀ i ∈ U, (M.filter fun z => i ∉ A z).card ≤ 33) :
    ∃ H ⊆ M, 35 ≤ H.card ∧ ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H,
      67108863 < ((A x ∩ A y) ∩ A z).card := by
  classical
  have htotal : 185*357913943 ≤ ∑ i : I, (M.filter fun z => i ∈ A z).card := by
    rw [← transpose_count M univ (fun z i => i ∈ A z)]
    simpa [hm] using sum_le_sum ht
  have bound := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    show (M.filter fun z => i ∈ A z).card ≤ (if i ∈ U then 185 else 34) by
      split_ifs with hi
      · exact (card_filter_le _ _).trans_eq hm
      · exact hreg i hi)
  simp only [sum_ite, sum_const, smul_eq_mul] at bound
  have hset : (univ.filter fun i => i ∈ U) = U := by ext; simp
  rw [hset] at bound
  have hpart := (univ : Finset I).card_filter_add_card_filter_not (fun i => i ∈ U)
  rw [hset,card_univ,hn] at hpart
  let miss := fun z => (U.filter fun i => i ∉ A z).card
  have hmiss : ∑ z ∈ M, miss z ≤ U.card*33 := by
    change (∑ z ∈ M, (U.filter fun i => i ∉ A z).card) ≤ _
    rw [transpose_count M U (fun z i => i ∉ A z)]
    simpa only [sum_const,smul_eq_mul] using sum_le_sum hsing
  let H := M.filter fun z => 151*miss z ≤ 33*U.card
  have hH : 35 ≤ H.card := by
    by_contra! hsmall
    let T := M \ H
    have hT : 151 ≤ T.card := by
      have h := card_sdiff_add_card_eq_card (s := H) (t := M) (filter_subset _ _)
      change T.card + H.card = M.card at h
      omega
    have hlo (z : F) (hz : z ∈ T) : 33*U.card+1 ≤ 151 * miss z := by
      obtain ⟨hzM,hzH⟩ := mem_sdiff.mp hz
      exact Nat.succ_le_of_lt (lt_of_not_ge fun hc => hzH (mem_filter.mpr ⟨hzM,hc⟩))
    have hs := sum_le_sum hlo
    simp only [sum_const,smul_eq_mul,← mul_sum] at hs
    have hsub := sum_le_sum_of_subset_of_nonneg (sdiff_subset (s := M) (t := H))
      (f := miss) (fun _ _ _ => Nat.zero_le _)
    have hprod := Nat.mul_le_mul_right (33*U.card+1) hT
    change ∑ z ∈ T, miss z ≤ _ at hsub
    omega
  refine ⟨H,filter_subset _ _,hH,?_⟩
  intro x hx y hy z hz
  have ha := (mem_filter.mp hx).2
  have hb := (mem_filter.mp hy).2
  have hc := (mem_filter.mp hz).2
  have hcov : U ⊆ (((A x ∩ A y) ∩ A z ∪ (U.filter fun i => i ∉ A x)) ∪
      (U.filter fun i => i ∉ A y)) ∪ (U.filter fun i => i ∉ A z) := by
    intro i hi
    simp only [mem_union,mem_inter,mem_filter,hi,true_and]
    tauto
  have hunion := (card_le_card hcov).trans (card_union_le _ _)
  have h2 := card_union_le ((A x ∩ A y) ∩ A z ∪ (U.filter fun i => i ∉ A x))
    (U.filter fun i => i ∉ A y)
  have h1 := card_union_le ((A x ∩ A y) ∩ A z) (U.filter fun i => i ∉ A x)
  dsimp [miss] at ha hb hc
  omega

private theorem no_common_factor {K : Type} [Field K] {f : Factor K}
    (hi : Irreducible f) (hd : f.natDegree = 1) {d : Polynomial K[X]}
    (hnu : ¬ IsUnit d) (h1 : d ∣ f.coeff 1) (h0 : d ∣ f.coeff 0) : False := by
  apply hnu
  apply isPrimitive_iff_isUnit_of_C_dvd.mp (hi.isPrimitive (by omega)) d
  rw [eq_X_add_C_of_natDegree_le_one hd.le]
  exact dvd_add (dvd_mul_of_dvd_left (_root_.map_dvd C h1) _) (_root_.map_dvd C h0)

private theorem nonzero_fiber {K : Type} [Field K] {f : Factor K}
    (hi : Irreducible f) (hd : f.natDegree = 1) (x : K) :
    ¬ ((f.coeff 1).map (evalRingHom x) = 0 ∧ (f.coeff 0).map (evalRingHom x) = 0) := by
  rintro ⟨h1,h0⟩
  have dv (P : Polynomial K[X]) (hp : P.map (evalRingHom x) = 0) : C (X-C x) ∣ P := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro j
    apply dvd_iff_isRoot.mpr
    simpa using congrArg (fun g : K[X] => g.coeff j) hp
  exact no_common_factor hi hd (fun h => not_isUnit_X_sub_C x (isUnit_C.mp h))
    (dv _ h1) (dv _ h0)

open scoped Classical in
private theorem roots_le {K F : Type} [Field K] [Field F] (σ : F →+* K)
    (M : Finset F) (P : K[X]) (hP : P ≠ 0) (r : ℕ) (hd : P.natDegree ≤ r) :
    (M.filter fun z => P.eval (σ z) = 0).card ≤ r := by
  classical
  by_contra! h
  apply hP
  let S := M.filter fun z => P.eval (σ z) = 0
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : S => σ (z : F))
    (σ.injective.comp Subtype.val_injective)
  · exact fun z => (mem_filter.mp z.property).2
  · simpa only [Fintype.card_coe] using hd.trans_lt h

variable {F I K : Type} [Field F] [DecidableEq F] [Fintype I] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

private theorem root_equation (fam : Family dom δ u) (σ : F →+* K) (f : Factor K)
    (hd : f.natDegree = 1) {z : F} (hz : z ∈ population fam σ f) :
    (f.coeff 1).eval (C (σ z)) * (fam.q z).map σ + (f.coeff 0).eval (C (σ z)) = 0 := by
  classical
  have h := (mem_filter.mp hz).2
  change f.eval₂ _ _ = 0 at h
  conv_lhs at h => rw [eq_X_add_C_of_natDegree_le_one hd.le]
  simpa only [eval₂_add,eval₂_mul,eval₂_X,eval₂_C,coe_evalRingHom] using h

open scoped Classical in
/-- At any irreducible value-linear factor on the actual interpolation surface, 185 selected
labels yield at least 35 whose every triple agrees on more coordinates than the degree. -/
theorem rich_triples (fam : Family dom δ u) (σ : F →+* K) (f : Factor K)
    (hi_irred : Irreducible f) (hd : f.natDegree = 1)
    (tri : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hpop : 185 ≤ (population fam σ f).card) :
    ∃ H ⊆ population fam σ f, 35 ≤ H.card ∧ ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H,
      67108863 < ((fullAgreement dom (u 0) (u 1) x (fam.q x) ∩
        fullAgreement dom (u 0) (u 1) y (fam.q y)) ∩
        fullAgreement dom (u 0) (u 1) z (fam.q z)).card := by
  classical
  obtain ⟨M,hM,hm⟩ := exists_subset_card_eq hpop
  let A (i : I) := (f.coeff 1).map (evalRingHom (σ (dom i)))
  let B (i : I) := (f.coeff 0).map (evalRingHom (σ (dom i)))
  let R (i : I) := A i * (C (σ (u 0 i)) + X * C (σ (u 1 i))) + B i
  let U := univ.filter fun i => R i = 0
  let agree := fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)
  have hn1 : f.coeff 1 ≠ 0 := hd ▸ leadingCoeff_ne_zero.mpr hi_irred.ne_zero
  have hA (i : I) : (A i).natDegree ≤ 33 := by
    have hs := tri 1 hn1
    exact natDegree_map_le.trans (by omega)
  have hB (i : I) : (B i).natDegree ≤ 34 := by
    by_cases hh : f.coeff 0 = 0
    · simp [B,hh]
    · simpa using natDegree_map_le.trans (tri 0 hh : (f.coeff 0).natDegree + 0 ≤ _)
  have hR (i : I) : (R i).natDegree ≤ 34 := by
    have hline : (C (σ (u 0 i)) + X * C (σ (u 1 i)) : K[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) (by
        exact (natDegree_mul_le ..).trans (by simp)))
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_mul_le ..).trans ((Nat.add_le_add (hA i) hline).trans (by decide))) (hB i))
  have rel (i : I) (z : F) (hz : z ∈ M) :
      (A i).eval (σ z) * σ ((fam.q z).eval (dom i)) + (B i).eval (σ z) = 0 := by
    have h := congrArg (evalRingHom (σ (dom i))) (root_equation fam σ f hd (hM hz))
    have ev (P : Polynomial K[X]) : (P.eval (C (σ z))).eval (σ (dom i)) =
        (P.map (evalRingHom (σ (dom i)))).eval (σ z) := by
      simpa using (eval_map_apply (p := P) (evalRingHom (σ (dom i))) (C (σ z))).symm
    simpa only [map_add,map_zero,map_mul,coe_evalRingHom,ev,eval_map_apply] using h
  have counts (i : I) (z : F) (hz : z ∈ M) :
      (R i).eval (σ z) =
      (A i).eval (σ z) * σ (u 0 i + z * u 1 i - (fam.q z).eval (dom i)) := by
    have hh := rel i z hz
    simp only [R,eval_add,eval_mul,eval_C,eval_X,map_sub,map_add,map_mul]
    linear_combination hh
  obtain ⟨H,hHM,h35,htr⟩ := triple_rich_subset M U agree hn hm
    (fun z hz => ht.trans (fam.threshold_le z (mem_filter.mp (hM hz)).1))
    (fun i hi => (card_le_card (show _ ⊆ M.filter fun z => (R i).eval (σ z) = 0 from by
      intro z hz
      obtain ⟨hz,hfit⟩ := mem_filter.mp hz
      have hh := (mem_filter.mp hfit).2
      apply mem_filter.mpr
      exact ⟨hz,by rw [counts i z hz,hh,sub_self,map_zero,mul_zero]⟩)).trans
        (roots_le σ M _ (fun hh => hi (mem_filter.mpr ⟨mem_univ _,hh⟩)) _ (hR i)))
    (fun i hi => by
      have hzero := (mem_filter.mp hi).2
      have hAn : A i ≠ 0 := by
        intro hA0
        have hB0 : B i = 0 := by simpa [R,hA0] using hzero
        exact nonzero_fiber (f := f) hi_irred hd (σ (dom i)) ⟨hA0,hB0⟩
      apply le_trans _ (roots_le σ M _ hAn _ (hA i))
      apply card_le_card
      intro z hz
      obtain ⟨hz,hbad⟩ := mem_filter.mp hz
      refine mem_filter.mpr ⟨hz,?_⟩
      have heq := counts i z hz
      rw [hzero,eval_zero] at heq
      apply (mul_eq_zero.mp heq.symm).resolve_right
      intro he
      have hh : u 0 i + z * u 1 i - (fam.q z).eval (dom i) = 0 := σ.injective (by simpa using he)
      exact hbad (mem_filter.mpr ⟨mem_univ _, (sub_eq_zero.mp hh).symm⟩))
  exact ⟨H,hHM.trans hM,h35,htr⟩

/-- Every irreducible value-linear factor of the actual interpolant carrying 185 sections
is the affine line of a single bounded-degree polynomial head over the original field. -/
theorem saturated [Finite F] (fam : Family dom δ u) (σ : F →+* K) (f Q : Factor K)
    (hi : Irreducible f) (hd : f.natDegree = 1) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (triangle : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hpop : 185 ≤ (population fam σ f).card) :
    ∃ p : F[X] × F[X], valid p ∧ population fam σ f ⊆ carried fam p ∧
      Associated f (X - C (C (p.1.map σ) + X * C (p.2.map σ))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have tri := SecondPrimeSectionResultant.factor_triangle hQ hdiv triangle
  obtain ⟨H,hH,h35,htr⟩ := rich_triples fam σ f hi hd tri hn ht hpop
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < H.card by omega)
  have sub (z : F) (hz : z ∈ H) : z ∈ fam.G := (mem_filter.mp (hH hz)).1
  let b := slopePolynomial x y (fam.q x) (fam.q y)
  let a := fam.q x - C x * b
  have hb : b.natDegree < 67108864 :=
    slopePolynomial_natDegree_lt (fam.degree_lt _ (sub _ hx)) (fam.degree_lt _ (sub _ hy))
  have ha : a.natDegree < 67108864 := (natDegree_sub_le ..).trans_lt
    (max_lt (fam.degree_lt _ (sub _ hx)) ((natDegree_C_mul_le _ _).trans_lt hb))
  have on_line (z : F) (hz : z ∈ H) : fam.q z = a + C z*b := by
    by_cases he : x = z
    · subst z
      simp [a]
    apply third_point_on_secant_line_of_slope_eq he
    by_contra! hs
    have h := triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
      (by decide : 1 ≤ 67108864) hxy he (fam.degree_lt _ (sub _ hx))
      (fam.degree_lt _ (sub _ hy)) (fam.degree_lt _ (sub _ hz)) (Ne.symm hs)
    exact (not_le.mpr (htr x hx y hy z hz)) h
  let sec : Polynomial K[X] := C (a.map σ) + X * C (b.map σ)
  let g : Factor K := X - C sec
  have hg : g.natDegree = 1 := natDegree_X_sub_C _
  have hs : sec.natDegree ≤ 1 :=
    (natDegree_add_le ..).trans (max_le (by simp)
      ((natDegree_mul_le ..).trans (by simp)))
  have gtri : WeightedSylvesterDegree.TotalDegreeLe g 1 := by
    intro j hj
    have hj' : j ≤ 1 := hg ▸ le_natDegree_of_ne_zero hj
    interval_cases j
    · simpa [g] using hs
    · simp [g]
  have eval_sec (z : F) : sec.eval (C (σ z)) = (a + C z*b).map σ := by
    simp only [sec,eval_add,eval_C,eval_mul,eval_X,Polynomial.map_add,Polynomial.map_mul,map_C]
  have ev (z : F) : g.eval₂ (evalRingHom (C (σ z))) ((fam.q z).map σ) =
      (fam.q z).map σ - (a + C z*b).map σ := by simp [g,eval_sec]
  have hfg : f ∣ g := SecondPrimeSectionResultant.divides_of_many_sections σ f g hi (by omega)
    tri gtri H (fun z => (fam.q z).map σ) (fun z hz => ⟨(mem_filter.mp (hH hz)).2,by
      rw [ev,on_line z hz,sub_self]⟩) (by rw [hd,hg]; omega)
  have hass : Associated f g := hi.associated_of_dvd (irreducible_X_sub_C sec) hfg
  refine ⟨(a,b),⟨ha,hb⟩,?_,hass⟩
  intro z hz
  obtain ⟨hzG,hz0⟩ := mem_filter.mp hz
  let E := eval₂RingHom (evalRingHom (C (σ z))) ((fam.q z).map σ)
  have hz' : E f = 0 := hz0
  have he := (hass.map E).eq_zero_iff.mp hz'
  change g.eval₂ _ _ = 0 at he
  rw [ev,sub_eq_zero] at he
  exact mem_filter.mpr ⟨hzG,Polynomial.map_injective σ σ.injective he⟩

/-- The value-linear alternative disappears from the actual population theorem. The only
remaining cases are populated quartics, cubics, quadratics, or three to four large heads. -/
theorem actual_reduction [Finite F] (fam : Family dom δ u) (σ : F →+* K)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      ((∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 4 ∧ 2147483615 ≤ (population fam σ f).card) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population fam σ f).card) ∨
         (f.natDegree = 2 ∧ 4128 < (population fam σ f).card))) ∨
       ∃ heads : Finset (F[X] × F[X]), 3 ≤ heads.card ∧ heads.card ≤ 4 ∧
         (∀ p ∈ heads, valid p ∧ 512 < (carried fam p).card ∧
           (carried fam p).card ≤ 715827882 ∧
           356515842 ≤ (jointCore dom (u 0) (u 1) p.1 p.2).card) ∧
         fam.G.card ≤ (heads.biUnion (carried fam)).card + 4*4128 + 34) := by
  obtain ⟨Q,hQ,hshape,alt⟩ := actual_alternatives fam σ hn ht hbig
  refine ⟨Q,hQ,hshape,?_⟩
  rcases alt with ⟨f,hf,hd,hr⟩ | hheads
  · left
    refine ⟨f,hf,hd,?_⟩
    rcases hr with h4 | h3 | h2 | ⟨h1,h185,hnone⟩
    · exact Or.inl h4
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h2)
    · obtain ⟨p,hp,hinc,_⟩ := saturated fam σ f Q hf h1 hQ hd
        (fun j i a h => (hshape j i a h).2.1) hn ht h185
      exact False.elim (hnone ⟨p,hp,hinc⟩)
  · exact Or.inr hheads

#print axioms actual_reduction
#print axioms rich_triples
#print axioms saturated
end ArkLib.ProximityGap.Frontier.SecondPrimeLinearSaturation
