/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorSecantLines
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic

/-! # Value-linear components of the terminal second-prime interpolant -/

open Finset Polynomial
open scoped BigOperators NNReal
namespace ProximityGap.TerminalLinearComponent

variable {I J : Type*} [Fintype I]

/-- On 185 rich sections of a value-linear component, 35 sections have enough mutual
agreements in every triple to force all 35 onto one secant. -/
theorem common_triples [DecidableEq I] (M : Finset J) (S : J → Finset I) (U : Finset I)
    (hn : Fintype.card I = 1073741824) (hm : M.card = 185)
    (ht : ∀ j ∈ M, 357913943 ≤ (S j).card)
    (hoff : ∀ i ∉ U, (M.filter (fun j => i ∈ S j)).card ≤ 34)
    (hon : ∀ i ∈ U, (M.filter (fun j => i ∉ S j)).card ≤ 33) :
    ∃ W ⊆ M, 35 ≤ W.card ∧ ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      67108863 < (S a ∩ S b ∩ S c).card := by
  classical
  let miss (j : J) := (U \ S j).card
  have hm0 : 185 * 357913943 ≤ ∑ j ∈ M, (S j).card := by
    simpa [hm] using (sum_le_sum ht)
  have hs : ∑ j ∈ M, (S j).card = ∑ i, (M.filter fun j => i ∈ S j).card := by
    have eq (j : J) : (S j).card = (univ.filter fun i => i ∈ S j).card := by simp
    simp_rw [eq, card_filter]
    rw [sum_comm]
  have inc : ∑ i, (M.filter fun j => i ∈ S j).card ≤ U.card * 185 + Uᶜ.card * 34 := by
    calc
      _ = ∑ i ∈ U, (M.filter fun j => i ∈ S j).card +
          ∑ i ∈ Uᶜ, (M.filter fun j => i ∈ S j).card :=
        (sum_add_sum_compl U _).symm
      _ ≤ (∑ _i ∈ U, 185) + (∑ _i ∈ Uᶜ, 34) :=
        Nat.add_le_add (sum_le_sum fun _ _ => (card_filter_le ..).trans_eq hm)
          (sum_le_sum fun i hi => hoff i (mem_compl.mp hi))
      _ = _ := by simp
  have hcompl := card_add_card_compl U
  have hU : 185 * 357913943 ≤ U.card * 151 + 34 * 1073741824 := by
    rw [hs] at hm0
    omega
  have hmiss : ∑ j ∈ M, miss j ≤ U.card * 33 := by
    calc
      _ = ∑ i ∈ U, (M.filter fun j => i ∉ S j).card := by
        simp only [miss, sdiff_eq_filter, card_filter]
        rw [sum_comm]
      _ ≤ ∑ _i ∈ U, 33 := sum_le_sum hon
      _ = _ := by simp
  let W := M.filter fun j => 151 * miss j ≤ 33 * U.card
  have hW : 35 ≤ W.card := by
    by_contra! bad
    have hc := card_sdiff_of_subset (show W ⊆ M from filter_subset ..)
    have hmany : 151 ≤ (M \ W).card := by omega
    have hlow : ∑ j ∈ M \ W, (33 * U.card + 1) ≤ ∑ j ∈ M \ W, 151 * miss j := by
      apply sum_le_sum
      intro j hj
      have hnot := (mem_sdiff.mp hj).2
      simp only [W, mem_filter, (mem_sdiff.mp hj).1, true_and, not_le] at hnot
      omega
    have hsum := sum_le_sum_of_subset_of_nonneg (s := M \ W) (t := M)
      (sdiff_subset ..) (fun j _ _ => Nat.zero_le (151 * miss j))
    rw [sum_const, smul_eq_mul] at hlow
    simp only [← mul_sum] at hsum hlow
    have last := (Nat.mul_le_mul_right (33 * U.card + 1) hmany).trans
      (hlow.trans (hsum.trans (Nat.mul_le_mul_left 151 hmiss)))
    omega
  refine ⟨W, filter_subset .., hW, ?_⟩
  intro a ha b hb c hc
  have hA := (mem_filter.mp ha).2
  have hB := (mem_filter.mp hb).2
  have hC := (mem_filter.mp hc).2
  let V := S a ∩ S b ∩ S c
  have hsub : U ⊆ V ∪ (((U \ S a) ∪ (U \ S b)) ∪ (U \ S c)) := by grind
  have hcost : U.card ≤ V.card + (miss a + miss b + miss c) :=
    (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left
      ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)) _))
  change 67108863 < V.card
  omega

section PolynomialBounds

variable {K R : Type*} [Field K] [CommRing R] [IsDomain R]

private theorem root_count {L : Type*} (φ : L → R) (hi : Function.Injective φ)
    (W : Finset L) (p : R[X]) (hp : p ≠ 0) (hz : ∀ j ∈ W, p.eval (φ j) = 0) :
    W.card ≤ p.natDegree := by
  classical
  by_contra! bad
  exact hp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun j : W => φ j) (hi.comp Subtype.val_injective)
    (fun j => hz j j.property) (by simpa using bad))

omit [IsDomain R] in
private theorem eval_degree (Q : Polynomial R[X]) (y : R[X]) {H : ℕ}
    (hy : y.natDegree ≤ 1)
    (hQ : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j ≤ H) :
    (Q.eval y).natDegree ≤ H := by
  classical
  rw [Q.as_sum_range_C_mul_X_pow, eval_finsetSum]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [eval_mul, eval_C, eval_pow, eval_X]
  by_cases h : Q.coeff j = 0
  · simp [h]
  · exact (natDegree_mul_le ..).trans ((Nat.add_le_add_left
      ((natDegree_pow_le ..).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left j hy))
      _).trans (hQ j h))

/-- Total scalar/value degree at most 34 passes to the two coefficients of any value-linear
factor. Two generic scalar slopes recover its leading coefficient without cancellation. -/
theorem factor_degrees [Infinite R] (Q f : Polynomial R[X]) (hQ : Q ≠ 0) (hf : f ∣ Q)
    (hlinear : f.natDegree = 1)
    (hsupp : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j ≤ 34) :
    (f.coeff 0).natDegree ≤ 34 ∧ (f.coeff 1).natDegree ≤ 33 := by
  classical
  let y (a : R) := C a * X
  have hinj : Function.Injective y := by
    intro a b h
    simpa [y] using congrArg (fun p : R[X] => p.coeff 1) h
  obtain ⟨L, hL⟩ := Infinite.exists_subset_card_eq R (Q.natDegree + 2)
  let bad := L.filter fun a => Q.eval (y a) = 0
  let W := L \ bad
  have hcnt : bad.card ≤ Q.natDegree := root_count y hinj bad Q hQ
    (fun a ha => (mem_filter.mp ha).2)
  have hgood : 1 < W.card := by
    have hpart : W.card = L.card - bad.card := card_sdiff_of_subset (filter_subset ..)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hgood
  let A := f.coeff 1
  let B := f.coeff 0
  have form := f.eq_X_add_C_of_natDegree_le_one hlinear.le
  have hbound (a : R) (ha : a ∈ W) : (A * y a + B).natDegree ≤ 34 := by
    have hne : Q.eval (y a) ≠ 0 := fun h =>
      (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1, h⟩)
    have hd := natDegree_le_of_dvd (map_dvd (evalRingHom (y a)) hf) hne
    have hQd := eval_degree Q (y a) (natDegree_C_mul_le .. |>.trans (by simp)) hsupp
    have hval : f.eval (y a) = A * y a + B := by
      conv_lhs => rw [form]
      simp only [eval_add, eval_mul, eval_C, eval_X, A, B]
    simpa only [coe_evalRingHom, hval] using hd.trans hQd
  have hsub := (natDegree_sub_le (A * y a + B) (A * y b + B)).trans
    (max_le (hbound a ha) (hbound b hb))
  have he : A * y a + B - (A * y b + B) = C (a - b) * (A * X) := by
    simp only [y, C_sub]; ring
  have hA : A ≠ 0 := by
    change f.coeff 1 ≠ 0
    rw [← hlinear, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hlinear)
  rw [he, natDegree_C_mul (sub_ne_zero.mpr hab), natDegree_mul_X hA] at hsub
  have hdA : A.natDegree ≤ 33 := by omega
  have hAy : (A * y a).natDegree ≤ 34 :=
    (natDegree_mul_le ..).trans (Nat.add_le_add hdA
      ((natDegree_C_mul_le ..).trans (by simp : (X : R[X]).natDegree ≤ 1)))
  have hB := (natDegree_sub_le (A * y a + B) (A * y a)).trans (max_le (hbound a ha) hAy)
  rw [add_sub_cancel_left] at hB
  exact ⟨hB, hdA⟩

/-- A genuinely value-dependent irreducible component cannot vanish identically at a
coordinate site in every scalar/value coefficient. -/
private theorem no_vertical_site (f : Polynomial (Polynomial K[X])) (hf : Irreducible f)
    (hl : f.natDegree = 1) (x : K)
    (hA : (f.coeff 1).map (evalRingHom x) = 0) (hB : (f.coeff 0).map (evalRingHom x) = 0) :
    False := by
  classical
  have hdiv (p : Polynomial K[X]) (h : p.map (evalRingHom x) = 0) :
      C (X - C x) ∣ p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro j
    apply dvd_iff_isRoot.mpr
    simpa only [IsRoot, coeff_map, coe_evalRingHom, coeff_zero] using congrArg (·.coeff j) h
  have all : C (C (X - C x)) ∣ f := by
    conv_rhs => rw [f.eq_X_add_C_of_natDegree_le_one hl.le]
    exact dvd_add (dvd_mul_of_dvd_left (_root_.map_dvd C (hdiv _ hA)) _)
      (_root_.map_dvd C (hdiv _ hB))
  exact not_isUnit_X_sub_C x (isUnit_C.mp ((hf.isPrimitive (by omega)) _ all))

private theorem affine_degree (a b : R) : (C a + X * C b).natDegree ≤ 1 := by
  apply (natDegree_add_le ..).trans
  apply max_le (by simp)
  rw [mul_comm]
  exact (natDegree_C_mul_le ..).trans (le_of_eq natDegree_X)

end PolynomialBounds

open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open Code

section Actual
variable {F K ι : Type} [Field F] [Field K] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {δ : ℝ≥0}
  {u : WordStack F (Fin 2) ι}

private theorem site_scalar (p : Polynomial K[X]) (x t : K) :
    (p.map (evalRingHom x)).eval t = (p.eval (C t)).eval x := by
  simpa only [coe_evalRingHom, eval_C] using
    (eval_map_apply (p := p) (evalRingHom x) (C t))

private theorem secant_of_triples (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (W : Finset F) (hW : 35 ≤ W.card) (hG : W ⊆ fam.G)
    (htr : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      67108863 < (fullAgreement dom (u 0) (u 1) a (fam.q a) ∩
        fullAgreement dom (u 0) (u 1) b (fam.q b) ∩
        fullAgreement dom (u 0) (u 1) c (fam.q c)).card) :
    ∃ l ∈ lineParameters fam, W ⊆ pointsOn fam l := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < W.card by omega)
  refine ⟨secantParameter fam a b, secantParameter_mem_lineParameters fam (hG ha) (hG hb) hab, ?_⟩
  intro c hc
  by_cases hac : a = c
  · subst c
    exact first_point_mem_pointsOn_secant fam (hG ha)
  apply (mem_pointsOn_iff ..).mpr
  refine ⟨hG hc, third_point_on_secant_line_of_slope_eq hac ?_⟩
  by_contra hne
  have hcap := triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
    (by decide : 1 ≤ 67108864) hab hac (fam.degree_lt a (hG ha)) (fam.degree_lt b (hG hb))
    (fam.degree_lt c (hG hc)) (Ne.symm hne)
  exact (htr a ha b hb c hc).not_ge hcap

/-- A value-linear irreducible factor covering 185 or more actual terminal witnesses
is an affine line determined over the base field. Every selected section on that component
lies on this single genuine secant. -/
theorem actual_linear (φ : F →+* K) (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (hn : Fintype.card ι = 1073741824) (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (Q f : Polynomial (Polynomial K[X])) (hQ : Q ≠ 0) (hf : Irreducible f)
    (hfQ : f ∣ Q) (hl : f.natDegree = 1)
    (hsupp : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943)
    (G : Finset F) (hG : G ⊆ fam.G) (hlarge : 185 ≤ G.card)
    (hcarries : ∀ z ∈ G,
      f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    ∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l := by
  classical
  have hweight (j : ℕ) (hj : Q.coeff j ≠ 0) : (Q.coeff j).natDegree + j ≤ 34 := by
    let i := (Q.coeff j).natDegree
    have hi : (Q.coeff j).coeff i ≠ 0 := by simpa [i] using leadingCoeff_ne_zero.mpr hj
    exact (hsupp j i ((Q.coeff j).coeff i).natDegree
      (by simpa using leadingCoeff_ne_zero.mpr hi)).2.1
  obtain ⟨hB, hA⟩ := factor_degrees Q f hQ hfQ hl hweight
  let A := f.coeff 1
  let B := f.coeff 0
  have hform := f.eq_X_add_C_of_natDegree_le_one hl.le
  let ax (i : ι) := A.map (evalRingHom (φ (dom i)))
  let bx (i : ι) := B.map (evalRingHom (φ (dom i)))
  let row (i : ι) : K[X] := C (φ (u 0 i)) + X * C (φ (u 1 i))
  let R (i : ι) := ax i * row i + bx i
  let S (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let U := univ.filter fun i => R i = 0
  obtain ⟨M, hMG, hM⟩ := exists_subset_card_eq hlarge
  have hsec (i : ι) (z : F) (hz : z ∈ G) :
      (ax i).eval (φ z) * φ ((fam.q z).eval (dom i)) + (bx i).eval (φ z) = 0 := by
    have he := hcarries z hz
    rw [hform] at he
    simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, coe_evalRingHom] at he
    simpa only [ax, bx, site_scalar, A, B, eval_add, eval_mul, eval_map_apply, eval_zero]
      using congrArg (eval (φ (dom i))) he
  have hrow (i : ι) (z : F) : (row i).eval (φ z) = φ (u 0 i + z * u 1 i) := by
    simp only [row, eval_add, eval_mul, eval_X, eval_C, map_add, map_mul]
  have hdeg (i : ι) : (R i).natDegree ≤ 34 := by
    show (ax i * row i + bx i).natDegree ≤ 34
    apply (natDegree_add_le ..).trans
    exact max_le ((natDegree_mul_le ..).trans (Nat.add_le_add (natDegree_map_le.trans hA)
      (affine_degree (φ (u 0 i)) (φ (u 1 i))))) (natDegree_map_le.trans hB)
  have off (i : ι) (hi : i ∉ U) : (M.filter fun z => i ∈ S z).card ≤ 34 := by
    have hne : R i ≠ 0 := by simpa [U] using hi
    have sub : M.filter (fun z => i ∈ S z) ⊆ M.filter (fun z => (R i).eval (φ z) = 0) := by
      intro z hz
      obtain ⟨hzM, hh⟩ := mem_filter.mp hz
      apply mem_filter.mpr ⟨hzM, ?_⟩
      rw [show R i = ax i * row i + bx i from rfl, eval_add, eval_mul, hrow,
        ← (mem_filter.mp hh).2]
      exact hsec i z (hMG hzM)
    exact (card_le_card sub).trans
      ((root_count φ φ.injective _ _ hne (fun _ hz => (mem_filter.mp hz).2)).trans (hdeg i))
  have onI (i : ι) (hi : i ∈ U) : (M.filter fun z => i ∉ S z).card ≤ 33 := by
    have hzero : R i = 0 := (mem_filter.mp hi).2
    have hax : ax i ≠ 0 := by
      intro hbad
      have hbx : bx i = 0 := by simpa only [R, hbad, zero_mul, zero_add] using hzero
      exact no_vertical_site f hf hl _ hbad hbx
    have sub : M.filter (fun z => i ∉ S z) ⊆ M.filter (fun z => (ax i).eval (φ z) = 0) := by
      intro z hz
      obtain ⟨hzM, hh⟩ := mem_filter.mp hz
      apply mem_filter.mpr ⟨hzM, ?_⟩
      have hne : φ ((fam.q z).eval (dom i)) ≠ φ (u 0 i + z * u 1 i) := by
        intro he
        exact hh (mem_filter.mpr ⟨mem_univ _, φ.injective he⟩)
      have eq := congrArg (eval (φ z)) hzero
      simp only [R, eval_add, eval_mul, hrow, eval_zero] at eq
      exact (mul_eq_zero.mp (show (ax i).eval (φ z) *
        (φ ((fam.q z).eval (dom i)) - φ (u 0 i + z * u 1 i)) = 0 by
          linear_combination hsec i z (hMG hzM) - eq)).resolve_right (sub_ne_zero.mpr hne)
    exact (card_le_card sub).trans
      ((root_count φ φ.injective _ _ hax (fun _ hz => (mem_filter.mp hz).2)).trans
        (natDegree_map_le.trans hA))
  obtain ⟨W, hWM, hW, htr⟩ := common_triples M S U hn hM
    (fun z hz => ht.trans (fam.threshold_le z (hG (hMG hz)))) off onI
  obtain ⟨l, hlFam, hWL⟩ := secant_of_triples fam W hW (hWM.trans (hMG.trans hG)) htr
  let y : Polynomial K[X] := C (l.1.map φ) + X * C (l.2.map φ)
  have hy : y.natDegree ≤ 1 := affine_degree ..
  have hval : f.eval y = A * y + B := by
    conv_lhs => rw [hform]
    simp only [eval_add, eval_mul, eval_C, eval_X, A, B]
  have hdegY : (f.eval y).natDegree ≤ 34 := hval ▸
    (natDegree_add_le ..).trans (max_le ((natDegree_mul_le ..).trans (Nat.add_le_add hA hy)) hB)
  have hY (z : F) : y.eval (C (φ z)) = (l.1 + C z * l.2).map φ := by
    simp [y, mul_comm (l.2.map φ)]
  have hscalar (z : F) : f.eval₂ (evalRingHom (C (φ z))) (y.eval (C (φ z))) =
      (f.eval y).eval (C (φ z)) := eval₂_at_apply (evalRingHom _) y
  have hline : f.eval y = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f.eval y)
      (f := fun z : W => C (φ (z : F)))
      (C_injective.comp (φ.injective.comp Subtype.val_injective))
    · intro z
      rw [← hscalar, hY, ← ((mem_pointsOn_iff ..).mp (hWL z.property)).2]
      exact hcarries z (hMG (hWM z.property))
    · simpa using hdegY.trans_lt hW
  have hassoc := (irreducible_X_sub_C y).associated_of_dvd hf (dvd_iff_isRoot.mpr hline)
  refine ⟨l, hlFam, ?_⟩
  intro z hz
  apply (mem_pointsOn_iff ..).mpr
  refine ⟨hG hz, map_injective φ φ.injective ?_⟩
  have hv := (hassoc.map (eval₂RingHom (evalRingHom (C (φ z))) ((fam.q z).map φ))).eq_zero_iff.mpr
    (hcarries z hz)
  simpa only [coe_eval₂RingHom, eval₂_sub, eval₂_X, eval₂_C, coe_evalRingHom, hY,
    sub_eq_zero] using hv

end Actual

#print axioms actual_linear
#print axioms common_triples
#print axioms factor_degrees
end ProximityGap.TerminalLinearComponent
