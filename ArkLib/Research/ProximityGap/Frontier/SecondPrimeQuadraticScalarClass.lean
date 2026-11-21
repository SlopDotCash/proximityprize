/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeLinearSaturation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight

/-! # Quadratic components whose discriminant has scalar square class -/
namespace ArkLib.ProximityGap.Frontier.SecondPrimeQuadraticScalarClass
open Finset Polynomial HalfPredecessorLineCoreGeometry SecondPrimeActualPopulations
open scoped NNReal
private theorem transpose_count {α β : Type*} (M : Finset α) (N : Finset β) (p : α → β → Prop)
    [∀ z i, Decidable (p z i)] :
    ∑ z ∈ M, (N.filter (p z)).card = ∑ i ∈ N, (M.filter (p · i)).card := by
  simp_rw [Finset.card_filter]
  rw [sum_comm]

private theorem quadratic_triples {F I : Type*} [Fintype I] [DecidableEq I]
    (M : Finset F) (U : Finset I) (A : F → Finset I)
    (hn : Fintype.card I = 1073741824) (hm : M.card = 2048)
    (ht : ∀ z ∈ M, 134217727 ≤ (A z).card)
    (hreg : ∀ i, i ∉ U → (M.filter fun z => i ∈ A z).card ≤ 34)
    (hsing : ∀ i ∈ U, (M.filter fun z => i ∉ A z).card ≤ 34) :
    ∃ H ⊆ M, 35 ≤ H.card ∧ ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H,
      67108863 < ((A x ∩ A y) ∩ A z).card := by
  classical
  have htotal : 2048*134217727 ≤ ∑ i : I, (M.filter fun z => i ∈ A z).card := by
    rw [← transpose_count M univ (fun z i => i ∈ A z)]
    simpa [hm] using sum_le_sum ht
  have bound := sum_le_sum (s := (univ : Finset I)) (fun i _ =>
    show (M.filter fun z => i ∈ A z).card ≤ (if i ∈ U then 2048 else 34) by
      split_ifs with hi
      · exact (card_filter_le _ _).trans_eq hm
      · exact hreg i hi)
  simp only [sum_ite, sum_const, smul_eq_mul] at bound
  have hset : (univ.filter fun i => i ∈ U) = U := by ext; simp
  rw [hset] at bound
  have hpart := (univ : Finset I).card_filter_add_card_filter_not (fun i => i ∈ U)
  rw [hset,card_univ,hn] at hpart
  let miss := fun z => (U.filter fun i => i ∉ A z).card
  have hmiss : ∑ z ∈ M, miss z ≤ U.card*34 := by
    change (∑ z ∈ M, (U.filter fun i => i ∉ A z).card) ≤ _
    rw [transpose_count M U (fun z i => i ∉ A z)]
    simpa only [sum_const,smul_eq_mul] using sum_le_sum hsing
  let H := M.filter fun z => 2014*miss z ≤ 34*U.card
  have hH : 35 ≤ H.card := by
    by_contra! hsmall
    let T := M \ H
    have hT : 2014 ≤ T.card := by
      have h := card_sdiff_add_card_eq_card (s := H) (t := M) (filter_subset _ _)
      change T.card + H.card = M.card at h
      omega
    have hlo (z : F) (hz : z ∈ T) : 34*U.card+1 ≤ 2014 * miss z := by
      obtain ⟨hzM,hzH⟩ := mem_sdiff.mp hz
      exact Nat.succ_le_of_lt (lt_of_not_ge fun hc => hzH (mem_filter.mpr ⟨hzM,hc⟩))
    have hs := sum_le_sum hlo
    simp only [sum_const,smul_eq_mul,← mul_sum] at hs
    have hsub := sum_le_sum_of_subset_of_nonneg (sdiff_subset (s := M) (t := H))
      (f := miss) (fun _ _ _ => Nat.zero_le _)
    have hprod := Nat.mul_le_mul_right (34*U.card+1) hT
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

variable {K : Type} [Field K]

/-- The coordinate-scalar polynomial discriminant of the three value coefficients. -/
noncomputable def disc (f : K[X][X][X]) : Polynomial K[X] :=
  (f.coeff 1)^2 - 4 * f.coeff 2 * f.coeff 0

private theorem expand_two (f : K[X][X][X]) (hd : f.natDegree = 2) :
    f = C (f.coeff 0) + C (f.coeff 1)*X + C (f.coeff 2)*X^2 := by
  simpa [sum_range_succ] using (f.as_sum_range_C_mul_X_pow' (n := 3) (by omega))

set_option synthInstance.maxSize 1024 in
private theorem nonsquare_scalar (f : K[X][X][X]) (hi : Irreducible f) (hd : f.natDegree = 2)
    (hchar : (2 : K) ≠ 0) (s : K[X]) (V : Polynomial K[X])
    (hdisc : disc f = s.map C * V ^ 2) {A B : K[X]} (hrel : A ^ 2 = s * B ^ 2) : B = 0 := by
  classical
  by_contra hB
  let r := B.map (C : K →+* K[X])
  let w := A.map (C : K →+* K[X]) * V
  let _ : CommRing (K[X][X]) := Polynomial.commRing
  let _ : CommRing (K[X][X][X]) := Polynomial.commRing
  have hr : r ≠ 0 := fun hr => hB (Polynomial.map_injective C C_injective (by simpa [r] using hr))
  have h2 : f.coeff 2 ≠ 0 := hd ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have hR2 : (2 : Polynomial K[X]) ≠ 0 := by
    simpa only [map_ofNat] using (C_ne_zero.mpr (C_ne_zero.mpr hchar))
  have hw : w^2 = r^2 * disc f := by
    have hA := congrArg (Polynomial.map (C : K →+* K[X])) hrel
    simp only [Polynomial.map_pow,Polynomial.map_mul] at hA
    rw [hdisc]
    dsimp [r,w]
    rw [mul_pow,hA]
    ring
  let L : K[X][X][X] := C (r*f.coeff 1) + C (2*r*f.coeff 2)*X
  have hmul : (L-C w)*(L+C w) = C (4*r^2*f.coeff 2)*f := by
    have he := congrArg (C : Polynomial K[X] →+* K[X][X][X]) hw
    simp only [disc,map_sub,map_mul,map_pow,map_ofNat] at he
    conv_rhs => arg 2; rw [expand_two f hd]
    dsimp [L]
    simp only [map_mul,map_pow,map_ofNat]
    linear_combination -he
  have dv : f ∣ (L-C w)*(L+C w) := by rw [hmul]; exact dvd_mul_left _ _
  have hL : L.natDegree ≤ 1 := (natDegree_add_le ..).trans
    (max_le (by rw [natDegree_C]; omega) ((natDegree_mul_le ..).trans (by
      rw [natDegree_C,natDegree_X])))
  have hc : (C w : K[X][X][X]).natDegree = 0 := natDegree_C w
  have hn (v : Polynomial K[X]) : (C (2*r*f.coeff 2)*X+C v : K[X][X][X]) ≠ 0 := by
    intro hz
    have hh := congrArg (fun g : K[X][X][X] => g.coeff 1) hz
    simp [mul_ne_zero (mul_ne_zero hR2 hr) h2] at hh
  rcases hi.prime.dvd_or_dvd dv with hm | hp
  · have hne : L-C w ≠ 0 := by
      convert hn (r*f.coeff 1-w) using 1
      simp only [L,map_sub]
      ring
    have hh := (natDegree_le_of_dvd hm hne).trans
      ((natDegree_sub_le ..).trans (max_le hL (by omega)))
    omega
  · have hne : L+C w ≠ 0 := by
      convert hn (r*f.coeff 1+w) using 1
      simp only [L,map_add]
      ring
    have hh := (natDegree_le_of_dvd hp hne).trans
      ((natDegree_add_le ..).trans (max_le hL (by omega)))
    omega

private theorem unique_root_on_identity (s a b c v h : K[X]) (hn : ∀ w v : K[X], w^2=s*v^2 → v=0)
    (hdisc : b^2-4*a*c = s*v^2) (hid : a*h^2+b*h+c=0) (x y : K)
    (ha : a.eval x ≠ 0) (hy : a.eval x*y^2+b.eval x*y+c.eval x=0) : y=h.eval x := by
  have hh : (2*a*h+b)^2=s*v^2 := by linear_combination 4*a*hid+hdisc
  have hzero := hn _ _ hh
  simp only [hzero,zero_pow (by decide : 2 ≠ 0),mul_zero,pow_eq_zero_iff (by decide : 2 ≠ 0)] at hh
  have eq₁ := congrArg (evalRingHom x) hh
  have eq₂ := congrArg (evalRingHom x) hid
  simp only [map_zero,map_add,map_mul,map_ofNat,map_pow,coe_evalRingHom] at eq₁ eq₂
  have hv : a.eval x*(y-h.eval x)^2=0 := by
    linear_combination hy - eq₂ - (y-h.eval x)*eq₁
  apply sub_eq_zero.mp
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hv).resolve_left ha)

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

open scoped Classical in
private theorem no_rich_triples [Finite F] (fam : Family dom δ u) (σ : F →+* K) (f : K[X][X][X])
    (hi : Irreducible f) (hd : f.natDegree = 2) (tri : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (hn : Fintype.card I = 1073741824) (H : Finset F) (hH : H ⊆ population fam σ f)
    (h35 : 35 ≤ H.card) (htr : ∀ x ∈ H, ∀ y ∈ H, ∀ z ∈ H,
      67108863 < ((fullAgreement dom (u 0) (u 1) x (fam.q x) ∩
        fullAgreement dom (u 0) (u 1) y (fam.q y)) ∩
        fullAgreement dom (u 0) (u 1) z (fam.q z)).card) : False := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp (show 1 < H.card by omega)
  have sub (z : F) (hz : z ∈ H) : z ∈ fam.G := (mem_filter.mp (hH hz)).1
  let b := slopePolynomial x y (fam.q x) (fam.q y)
  let a := fam.q x - C x * b
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
  let g : K[X][X][X] := X - C sec
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
  have hle := natDegree_le_of_dvd hfg (X_sub_C_ne_zero sec)
  omega

private theorem leading_degree (f Q : K[X][X][X]) (hf : f ≠ 0) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (hw : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → a + j * 67108863 < 357913943)
    (i : ℕ) (hi : (f.coeff 2).coeff i ≠ 0) :
    ((f.coeff 2).coeff i).natDegree ≤ 223696216 := by
  obtain ⟨g,he⟩ := hdiv
  have hg : g ≠ 0 := fun hz => hQ (by simp [he,hz])
  have h := SecondPrimeCoordinateWeight.weight_le_of_coeff 67108863 Q (W := 357913942)
    (fun j i a hh => Nat.le_of_lt_succ (hw j i a hh))
  rw [he,SecondPrimeCoordinateWeight.weight_mul _ _ _ hf hg] at h
  have hv := SecondPrimeCoordinateWeight.coeff_weight_le 67108863 f (leadingCoeff_ne_zero.mpr hi)
  omega

/-- When the coordinate-dependent part of the discriminant is a square, 2048 genuine
labels on the irreducible quadratic give a contradiction. All scalar signs are handled
together, since a globally square discriminant would contradict irreducibility. -/
theorem population_le [Finite F] (fam : Family dom δ u) (σ : F →+* K) (f Q : K[X][X][X])
    (hi : Irreducible f) (hd : f.natDegree = 2) (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (shape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hchar : (2 : K) ≠ 0) (s : K[X]) (V : Polynomial K[X])
    (hdisc : disc f = s.map C * V ^ 2) : (population fam σ f).card ≤ 2047 := by
  classical
  by_contra! hpop
  obtain ⟨M,hM,hm⟩ := exists_subset_card_eq (show 2048 ≤ (population fam σ f).card by omega)
  let site (i : I) (P : Polynomial K[X]) := P.map (evalRingHom (σ (dom i)))
  let a := fun i => site i (f.coeff 2)
  let b := fun i => site i (f.coeff 1)
  let c := fun i => site i (f.coeff 0)
  let h := fun i => (C (σ (u 0 i)) + X*C (σ (u 1 i)) : K[X])
  let R := fun i => a i*(h i)^2+b i*h i+c i
  let dropped := univ.filter fun i => a i = 0
  let U := univ.filter fun i => a i ≠ 0 ∧ R i = 0
  let agrees := fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)
  let A := fun z => agrees z \ dropped
  have tri := SecondPrimeSectionResultant.factor_triangle hQ hdiv
    (fun j i a hh => (shape j i a hh).2.1)
  have hlead : f.coeff 2 ≠ 0 := hd ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have hcoef (j : ℕ) (hj : j ≤ 2) (i : I) : (site i (f.coeff j)).natDegree ≤ 34-j := by
    by_cases hzero : f.coeff j = 0
    · simp [site,hzero]
    · have hh := tri j hzero
      exact natDegree_map_le.trans (by omega)
  have dh (i : I) : (h i).natDegree ≤ 1 := (natDegree_add_le ..).trans
    (max_le (by simp) ((natDegree_mul_le ..).trans (by simp)))
  have dr (i : I) : (R i).natDegree ≤ 34 := by
    have ha := hcoef 2 (by decide) i
    have hb := hcoef 1 (by decide) i
    have hc := hcoef 0 (by decide) i
    apply (natDegree_add_le ..).trans (max_le _ hc)
    apply (natDegree_add_le ..).trans (max_le _ _)
    · exact (natDegree_mul_le ..).trans (by
        have hsq : ((h i)^2).natDegree ≤ 2*(h i).natDegree := natDegree_pow_le
        change (site i (f.coeff 2)).natDegree + ((h i)^2).natDegree ≤ 34
        have hh := dh i
        omega)
    · exact (natDegree_mul_le ..).trans (by
        change (site i (f.coeff 1)).natDegree + (h i).natDegree ≤ 34
        have hh := dh i
        omega)
  let j := (f.coeff 2).natDegree
  have hj : (f.coeff 2).coeff j ≠ 0 := leadingCoeff_ne_zero.mpr hlead
  have hdrop : dropped.card ≤ 223696216 := by
    have hld := leading_degree f Q hi.ne_zero hQ hdiv (fun v l x hw => (shape v l x hw).2.2) j hj
    by_contra! hgreater
    apply hj
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun i : dropped => σ (dom (i : I)))
      (σ.injective.comp (dom.injective.comp Subtype.val_injective))
    · intro i
      have hh := congrArg (fun p : K[X] => p.coeff j) (mem_filter.mp i.property).2
      simpa [a,site] using hh
    · simpa using hld.trans_lt hgreater
  have rel (i : I) (z : F) (hz : z ∈ M) :
      (a i).eval (σ z) * (σ ((fam.q z).eval (dom i)))^2 +
      (b i).eval (σ z) * σ ((fam.q z).eval (dom i)) + (c i).eval (σ z) = 0 := by
    have hf := (mem_filter.mp (hM hz)).2
    change f.eval₂ _ _ = 0 at hf
    conv_lhs at hf => rw [expand_two f hd]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, coe_evalRingHom] at hf
    have he := congrArg (evalRingHom (σ (dom i))) hf
    have ev (P : Polynomial K[X]) : (P.eval (C (σ z))).eval (σ (dom i)) =
        (site i P).eval (σ z) := by
      simpa [site] using (eval_map_apply (p := P) (evalRingHom (σ (dom i))) (C (σ z))).symm
    simp only [map_add,map_zero,map_mul,map_pow,coe_evalRingHom,ev,eval_map_apply] at he
    dsimp only [a,b,c]
    linear_combination he
  have dsite (i : I) : (b i)^2-4*a i*c i = s*(site i V)^2 := by
    have hs : site i (s.map C) = s := by ext j; simp [site]
    have he := congrArg (site i) hdisc
    dsimp only [disc,site] at he hs
    simpa only [site,a,b,c,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_ofNat,hs] using he
  have good (i : I) (z : F) : i ∈ agrees z ↔ σ ((fam.q z).eval (dom i)) = (h i).eval (σ z) := by
    simp only [agrees,fullAgreement,mem_filter,mem_univ,true_and,h,eval_add,eval_C,eval_mul,
      eval_X,← map_mul,← map_add,σ.injective.eq_iff]
  have hreg (i : I) (hiU : i ∉ U) : (M.filter fun z => i ∈ A z).card ≤ 34 := by
    by_cases hah : a i = 0
    · have he : (M.filter fun z => i ∈ A z) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact (mem_sdiff.mp (mem_filter.mp hz).2).2 (mem_filter.mpr ⟨mem_univ _,hah⟩)
      simp [he]
    · have hr : R i ≠ 0 := fun zero => hiU (mem_filter.mpr ⟨mem_univ _,hah,zero⟩)
      apply le_trans _ (roots_le σ M _ hr _ (dr i))
      apply card_le_card
      intro z hz
      obtain ⟨hz,hzA⟩ := mem_filter.mp hz
      have he := rel i z hz
      rw [(good i z).mp (mem_sdiff.mp hzA).1] at he
      exact mem_filter.mpr ⟨hz,by simpa [R] using he⟩
  have hsing (i : I) (hiU : i ∈ U) : (M.filter fun z => i ∉ A z).card ≤ 34 := by
    obtain ⟨_,ha,hr⟩ := mem_filter.mp hiU
    have haD := (hcoef 2 (by decide) i).trans (by decide : 34-2 ≤ 34)
    apply le_trans _ (roots_le σ M _ ha 34 haD)
    apply card_le_card
    intro z hz
    obtain ⟨hz,hnfit⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨hz,?_⟩
    by_contra hnon
    apply hnfit
    apply mem_sdiff.mpr
    refine ⟨(good i z).mpr ?_,fun hd => ha (mem_filter.mp hd).2⟩
    exact unique_root_on_identity s (a i) (b i) (c i) (site i V) (h i)
      (fun _ _ he => nonsquare_scalar f hi hd hchar s V hdisc he)
      (dsite i) hr _ _ hnon (rel i z hz)
  obtain ⟨H,hHM,h35,htr⟩ := quadratic_triples M U A hn hm (fun z hz => by
    have hthreshold := ht.trans (fam.threshold_le z (mem_filter.mp (hM hz)).1)
    have hle := card_le_card_sdiff_add_card (s := agrees z) (t := dropped)
    change 357913943 ≤ (agrees z).card at hthreshold
    change 134217727 ≤ (agrees z \ dropped).card
    omega) hreg hsing
  apply no_rich_triples fam σ f hi hd tri hn H (hHM.trans hM) h35
  intro x hx y hy z hz
  exact (htr x hx y hy z hz).trans_le (card_le_card
    (inter_subset_inter (inter_subset_inter sdiff_subset sdiff_subset) sdiff_subset))

end ArkLib.ProximityGap.Frontier.SecondPrimeQuadraticScalarClass
