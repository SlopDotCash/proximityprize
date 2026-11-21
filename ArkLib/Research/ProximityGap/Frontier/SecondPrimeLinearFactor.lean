/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount
import ArkLib.Data.Polynomial.Bivariate

/-! # Linear-in-value factors at the second-prime predecessor -/

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open scoped NNReal

namespace ProximityGap.SecondPrimeLinearFactor

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
private abbrev Family (dom : I ↪ F) (δ : ℝ≥0) (u : WordStack F (Fin 2) I) :=
  BadScalarRichPointFamily dom 67108864 δ u

/-- A site-incidence inequality forces 35 actual decoded labels onto a common secant. -/
theorem extraction_of_geometry {k t m n : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 0 < k) (hmpos : 0 < m) (hgeom : ∀ c a b l v : ℕ, c ≤ n → (m + 34) * t ≤ c * (m + 34) + (n - c) * 34 →
      c ≤ a + b + l + v → m * a ≤ 33 * c → m * b ≤ 33 * c → m * l ≤ 33 * c → k ≤ v)
    (M : Finset F)
    (hM : M ⊆ fam.G) (hm : M.card = m + 34) (U : Finset I)
    (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hoff : ∀ x ∉ U, (M.filter fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 34)
    (hon : ∀ x ∈ U, (M.filter fun z => x ∉ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 33) :
    ∃ p ∈ lineParameters fam, 35 ≤ (M ∩ pointsOn fam p).card := by
  classical
  let A (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let miss (z : F) := (U \ A z).card
  have hx (x : I) : (M.filter fun z => x ∈ A z).card ≤ if x ∈ U then M.card else 34 := by
    split_ifs with h
    · exact card_filter_le _ _
    · exact hoff x h
  have hag (z : F) (hz : z ∈ M) : t ≤ (A z).card := ht.trans (fam.threshold_le z (hM hz))
  have hab := sum_le_sum hag
  have hre : (∑ z ∈ M, (A z).card) = ∑ x : I, (M.filter fun z => x ∈ A z).card := by
    have hcard (z : F) : (A z).card = ∑ x : I, if x ∈ A z then 1 else 0 := by simp
    simp_rw [hcard, card_filter]
    rw [sum_comm]
  rw [hre] at hab
  have hinc := hab.trans (sum_le_sum (fun x _ => hx x))
  simp only [sum_const, nsmul_eq_mul, Finset.sum_ite, Finset.filter_mem_eq_inter, univ_inter] at hinc
  have hUc : (univ.filter fun x : I => x ∉ U).card = Fintype.card I - U.card := by
    rw [filter_notMem_eq_sdiff, card_sdiff_of_subset (subset_univ U), card_univ]
  simp only [hUc, hn, hm, Nat.cast_id] at hinc
  have hUle := card_le_univ U
  rw [hn] at hUle

  have hmre : ∑ z ∈ M, miss z = ∑ x ∈ U, (M.filter fun z => x ∉ A z).card := by
    have he (z : F) : miss z = ∑ x ∈ U, if x ∉ A z then 1 else 0 := by
      rw [← card_filter, filter_notMem_eq_sdiff]
    simp_rw [he, card_filter]
    rw [sum_comm]
  have hmsum : ∑ z ∈ M, miss z ≤ 33*U.card :=
    hmre.le.trans ((sum_le_sum hon).trans_eq (by simp [Nat.mul_comm]))
  let good := M.filter fun z => m*miss z ≤ 33*U.card
  have hg : 35 ≤ good.card := by
    by_contra! hsmall
    let bad := M \ good
    have hb := card_sdiff_add_card_eq_card (show good ⊆ M from filter_subset _ _)
    change bad.card+good.card = M.card at hb
    have hs (z : F) (hz : z ∈ bad) : 33*U.card+1 ≤ m*miss z := by
      obtain ⟨hmz,hg'⟩ := mem_sdiff.mp hz
      have hh : ¬m*miss z ≤ 33*U.card := fun he => hg' (mem_filter.mpr ⟨hmz,he⟩)
      omega
    have hsum := sum_le_sum hs
    rw [sum_const, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at hsum
    have hsub : ∑ z ∈ bad, miss z ≤ ∑ z ∈ M, miss z :=
      sum_le_sum_of_subset_of_nonneg (sdiff_subset) (by simp)
    have hbound := hsum.trans (Nat.mul_le_mul_left m (hsub.trans hmsum))
    have impossible := (Nat.mul_le_mul_right (33*U.card+1) (show m ≤ bad.card by omega)).trans hbound
    exact (not_le.mpr (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) hmpos)) impossible
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < good.card by omega)
  let p := secantParameter fam a b
  have hme : good ⊆ M := filter_subset _ _
  have hpa := first_point_mem_pointsOn_secant fam (hM (hme ha)) (beta := b)
  have hpb := second_point_mem_pointsOn_secant fam (hM (hme hb)) hab
  have hpar : p ∈ lineParameters fam := secantParameter_mem_lineParameters fam (hM (hme ha)) (hM (hme hb)) hab
  have hpair : A a ∩ A b = jointCore dom (u 0) (u 1) p.1 p.2 := by
    have heA := (mem_pointsOn_iff fam p a).mp hpa
    have heB := (mem_pointsOn_iff fam p b).mp hpb
    simpa only [A, heA.2, heB.2] using fullAgreement_inter_eq_jointCore dom (u 0) (u 1) p.1 p.2 hab
  refine ⟨p, hpar, hg.trans (card_le_card ?_)⟩
  intro z hz
  refine mem_inter.mpr ⟨hme hz,(mem_pointsOn_iff fam p z).mpr ⟨hM (hme hz),?_⟩⟩
  by_contra hnq
  have hpd := lineParameter_degree_lt fam hpar
  have htcap := fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
    (fam.degree_lt z (hM (hme hz))) hpd.1 hpd.2 hnq
  let S := A z ∩ (A a ∩ A b)
  have hcap : S.card ≤ k-1 := by simpa only [S,A,hpair] using htcap
  have hcov : U ⊆ (U \ A a) ∪ (U \ A b) ∪ (U \ A z) ∪ S := by
    intro x hx
    simp only [S, mem_union, mem_sdiff, mem_inter, hx, true_and]
    tauto
  have h1 := card_union_le (U \ A a) (U \ A b)
  have h2 := card_union_le ((U \ A a) ∪ (U \ A b)) (U \ A z)
  have h3 := (card_le_card hcov).trans (card_union_le _ _)
  have hmass : U.card ≤ miss a + miss b + miss z + S.card := by dsimp only [miss]; omega
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  have hz' := (mem_filter.mp hz).2
  change m*miss a ≤ 33*U.card at ha'
  change m*miss b ≤ 33*U.card at hb'
  change m*miss z ≤ 33*U.card at hz'
  have hlarge := hgeom U.card (miss a) (miss b) (miss z) S.card hUle hinc hmass ha' hb' hz'
  omega

private abbrev Factor (K : Type) [Field K] := Polynomial (Polynomial K[X])

/-- The extraction property used by the linear and quadratic component bounds. -/
def SecantExtraction {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) (m : ℕ) : Prop :=
  ∀ M : Finset F, M ⊆ fam.G → M.card = m → ∀ U : Finset I,
    (∀ x ∉ U, (M.filter fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 34) →
    (∀ x ∈ U, (M.filter fun z => x ∉ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 33) →
    ∃ p ∈ lineParameters fam, 35 ≤ (M ∩ pointsOn fam p).card

/-- At the second-prime predecessor, 185 labels suffice. -/
theorem many_on_secant (fam : Family dom δ u) (M : Finset F)
    (hM : M ⊆ fam.G) (hm : M.card = 185) (U : Finset I)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hoff : ∀ x ∉ U, (M.filter fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 34)
    (hon : ∀ x ∈ U, (M.filter fun z => x ∉ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ 33) :
    ∃ p ∈ lineParameters fam, 35 ≤ (M ∩ pointsOn fam p).card := by
  apply extraction_of_geometry (m := 151) fam (by decide) (by decide) _ M hM hm U hn ht hoff hon
  intro c a b l v hc hinc hcover ha hb hl
  omega

/-- Evaluating first at the scalar and then at the domain coordinate commutes with
specializing the coordinate coefficients before evaluating the scalar. -/
theorem at_site (A : Polynomial K[X]) (x z : K) :
    (A.eval (C z)).eval x = (A.map (evalRingHom x)).eval z := by
  symm
  simpa using (eval_map_apply (p := A) (evalRingHom x) (C z))

omit [Fintype F] [DecidableEq F] in
/-- A nonzero polynomial over an extension vanishes at at most its degree in base labels. -/
theorem root_bound {S : Finset F} (φ : F →+* K) (p : K[X]) (hn : p ≠ 0)
    (hroot : ∀ z ∈ S, p.eval (φ z) = 0) : S.card ≤ p.natDegree := by
  classical
  by_contra! hgt
  apply hn
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun z : S => φ z.val) (φ.injective.comp Subtype.val_injective)
  · exact fun z => hroot z.val z.property
  · simpa using hgt

/-- Specializing a primitive linear-in-value surface at a coordinate leaves at least
one nonzero scalar coefficient polynomial. -/
private theorem nonzero_site (f : Factor K) {A B : Polynomial K[X]}
    (hf : f.IsPrimitive) (hlin : f = C A * Polynomial.X + C B) (x : K)
    (ha : A.map (evalRingHom x) = 0) : B.map (evalRingHom x) ≠ 0 := by
  intro hb
  have div (p : Polynomial K[X]) (hp : p.map (evalRingHom x) = 0) :
      C (Polynomial.X - C x) ∣ p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro i
    apply dvd_iff_isRoot.mpr
    have he := congrArg (fun s : K[X] => s.coeff i) hp
    simpa [IsRoot, coeff_map] using he
  have hdiv : C (C (Polynomial.X - C x)) ∣ f := by
    obtain ⟨v, hv⟩ := div A ha
    obtain ⟨w, hw⟩ := div B hb
    refine ⟨C v * Polynomial.X + C w, ?_⟩
    rw [hlin, hv, hw, C_mul, C_mul]
    ring
  exact not_isUnit_X_sub_C x (isUnit_C.mp (isPrimitive_iff_isUnit_of_C_dvd.mp hf _ hdiv))

open Classical in
/-- Extracting 35 collinear sections on a populous irreducible value-linear factor forces
every section on it onto one determined base-field secant. The coefficients of the factor
may lie over an arbitrary extension of the field of labels. -/
theorem linear_factor_is_head_of_extraction {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u) (φ : F →+* K) (f : Factor K)
    (hf : Irreducible f) (hdeg : f.natDegree = 1) (hweight : Bivariate.totalDegree f ≤ 34)
    {m : ℕ} (extract : SecantExtraction fam (m+1)) :
    let pop := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
    m < pop.card → ∃ p ∈ lineParameters fam, pop ⊆ pointsOn fam p := by
  classical
  let A := f.coeff 1
  let B := f.coeff 0
  have hlin : f = C A * Polynomial.X + C B := eq_X_add_C_of_natDegree_le_one hdeg.le
  have hA : A.natDegree ≤ 33 := by
    rcases Bivariate.coeff_totalDegree_le' f 1 with h | he
    · dsimp [A]; omega
    · simp [A,he]
  have hB : B.natDegree ≤ 34 := by
    rcases Bivariate.coeff_totalDegree_le' f 0 with h | he
    · dsimp [B]; omega
    · simp [B,he]
  have hp := hf.isPrimitive (by omega : f.natDegree ≠ 0)
  let pop := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
  change m < pop.card → _
  intro hpop
  obtain ⟨M, hsub, hm⟩ := exists_subset_card_eq (show m + 1 ≤ pop.card by omega)
  have hspec (z : F) (hz : z ∈ pop) :
      A.eval (C (φ z)) * (fam.q z).map φ + B.eval (C (φ z)) = 0 := by
    have he := (mem_filter.mp hz).2
    simpa only [hlin, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, coe_evalRingHom] using he
  let Ar (i : I) := A.map (evalRingHom (φ (dom i)))
  let Br (i : I) := B.map (evalRingHom (φ (dom i)))
  let L (i : I) : K[X] := C (φ (u 0 i)) + Polynomial.X * C (φ (u 1 i))
  let R (i : I) := Ar i * L i + Br i
  let U := univ.filter fun i => R i = 0
  have degL (i : I) : (L i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have degR (i : I) : (R i).natDegree ≤ 34 := by
    apply natDegree_add_le_of_degree_le _ (natDegree_map_le.trans hB)
    have h1 : (Ar i).natDegree ≤ 33 := natDegree_map_le.trans hA
    exact natDegree_mul_le.trans (by have := degL i; omega)
  have at_val (i : I) (z : F) (hz : z ∈ pop) :
      (Ar i).eval (φ z) * φ ((fam.q z).eval (dom i)) + (Br i).eval (φ z) = 0 := by
    have he := congrArg (fun w : K[X] => w.eval (φ (dom i))) (hspec z hz)
    simpa only [Ar, Br, eval_add, eval_mul, at_site, eval_map_apply, eval_zero] using he
  obtain ⟨p,hpLine,h35⟩ := extract M (hsub.trans (filter_subset _ _)) hm U (by
    intro i hi
    have hne : R i ≠ 0 := fun he => hi (mem_filter.mpr ⟨mem_univ _,he⟩)
    apply (root_bound φ (R i) hne ?_).trans (degR i)
    intro z hz
    obtain ⟨hzM,hfit⟩ := mem_filter.mp hz
    have he := at_val i z (hsub hzM)
    have hy := (mem_filter.mp hfit).2
    simp only [R,L,eval_add,eval_mul,eval_C,eval_X]
    simpa only [hy,map_add,map_mul] using he) (by
    intro i hi
    have hr : R i = 0 := (mem_filter.mp hi).2
    have hne : Ar i ≠ 0 := by
      intro hz
      apply nonzero_site f hp hlin (φ (dom i)) hz
      change Ar i * L i + Br i = 0 at hr
      simpa [hz, Br] using hr
    apply (root_bound φ (Ar i) hne ?_).trans (natDegree_map_le.trans hA)
    intro z hz
    obtain ⟨hzM,hmiss⟩ := mem_filter.mp hz
    have he := at_val i z (hsub hzM)
    have hl := congrArg (fun v : K[X] => v.eval (φ z)) hr
    simp only [R,L,eval_add,eval_mul,eval_C,eval_X,eval_zero] at hl
    have heq : (Ar i).eval (φ z) *
        (φ ((fam.q z).eval (dom i)) - (φ (u 0 i) + φ z * φ (u 1 i))) = 0 := by
      linear_combination he - hl
    apply (mul_eq_zero.mp heq).resolve_right
    intro hy
    apply hmiss
    apply mem_filter.mpr
    refine ⟨mem_univ _, φ.injective ?_⟩
    simpa only [map_add,map_mul] using sub_eq_zero.mp hy)
  let head : Polynomial K[X] := C (p.1.map φ) + Polynomial.X*C (p.2.map φ)
  have dh : head.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have degline : (A*head+B).natDegree ≤ 34 := by
    apply natDegree_add_le_of_degree_le _ hB
    exact natDegree_mul_le.trans (by omega)
  have el (z : F) : head.eval (C (φ z)) = (p.1+C z*p.2).map φ  := by
    simp [head]
    exact mul_comm _ _
  have hident : A*head+B = 0 := by
    let S := M ∩ pointsOn fam p
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : S => C (φ z.val))
      (C_injective.comp (φ.injective.comp Subtype.val_injective))
    · intro z
      obtain ⟨hzM,hzp⟩ := mem_inter.mp z.property
      have he := hspec z.val (hsub hzM)
      have hzq := ((mem_pointsOn_iff fam p z.val).mp hzp).2
      simpa only [eval_add,eval_mul,el,hzq] using he
    · change 35 ≤ S.card at h35
      simpa only [Fintype.card_coe] using (show (A*head+B).natDegree < S.card by omega)
  have hfac : f = C A * (Polynomial.X - C head) := by
    have hB' : B = -(A*head) := by linear_combination hident
    rw [hlin,hB',C_neg,C_mul]
    ring
  have hunit : IsUnit A := isPrimitive_iff_isUnit_of_C_dvd.mp hp A ⟨_,hfac⟩
  refine ⟨p,hpLine,?_⟩
  intro z hz
  refine (mem_pointsOn_iff fam p z).mpr ⟨(mem_filter.mp hz).1,?_⟩
  have he := (mem_filter.mp hz).2
  rw [hfac] at he
  simp only [eval₂_mul,eval₂_sub,eval₂_C,eval₂_X,coe_evalRingHom, el] at he
  have hne := (hunit.map (evalRingHom (C (φ z)))).ne_zero
  exact (map_injective φ φ.injective) (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hne))

open Classical in
/-- The 185-label specialization at the second-prime sixteenth-rate step. -/
theorem linear_factor_is_head (fam : Family dom δ u) (φ : F →+* K) (f : Factor K)
    (hf : Irreducible f) (hdeg : f.natDegree = 1) (hweight : Bivariate.totalDegree f ≤ 34)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    let pop := fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0
    184 < pop.card → ∃ p ∈ lineParameters fam, pop ⊆ pointsOn fam p := by
  apply linear_factor_is_head_of_extraction fam φ f hf hdeg hweight
  intro M hM hm U
  exact many_on_secant fam M hM hm U hn ht

/-- Every factor of an interpolant whose scalar and value indices sum to at most
34 inherits that bound. This accepts the coefficient statement of the actual
quartic interpolation theorem. -/
theorem factor_totalDegree_le {Q f : Factor K} (hQ : Q ≠ 0) (hdiv : f ∣ Q)
    (hshape : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i+j ≤ 34) :
    Bivariate.totalDegree f ≤ 34 := by
  classical
  have hmax : Bivariate.totalDegree Q ≤ 34 := by
    unfold Bivariate.totalDegree
    apply Finset.sup_le
    intro j hj
    have hqj : Q.coeff j ≠ 0 := mem_support_iff.mp hj
    let i := (Q.coeff j).natDegree
    have hqi : (Q.coeff j).coeff i ≠ 0 := leadingCoeff_ne_zero.mpr hqj
    exact hshape j i ((Q.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr hqi)
  obtain ⟨r, hqr⟩ := hdiv
  rw [hqr] at hQ hmax
  rw [Bivariate.totalDegree_mul (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at hmax
  omega

#print axioms factor_totalDegree_le
#print axioms linear_factor_is_head

end ProximityGap.SecondPrimeLinearFactor
