import ArkLib.Data.Polynomial.FiniteDomainQuotient
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The cross-ratio of four rate-half lists at the unique-radius successor

Four distinct message polynomials of degree below `2*h` matching one word on
at least `3*h-1` of `4*h` points have a nonconstant cross-ratio of degree
at most two. Pair differences, multiplied by the two error locators, give
affine quotients by the domain polynomial. A constant cross-ratio would force
every pair collision to be at least a triple collision. The six pair-root
bounds and the four agreement counts exclude that distribution.
-/

open Finset Polynomial
namespace ProximityGap.FourHeadCrossRatio
variable {F : Type*} [Field F]

private theorem collision_branches {a b c d z : F} (hz : z ≠ 0) (h1 : z ≠ 1)
    (he : (a-b)*(c-d) = z*(a-c)*(b-d)) :
    ((a=b ∨ c=d) ↔ (a=c ∨ b=d)) ∧ ((a=c ∨ b=d) ↔ (a=d ∨ b=c)) := by
  have ht : (a-d)*(b-c) = (1-z)*((a-c)*(b-d)) := by
    linear_combination -he
  have hz1 : (1:F)-z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have ha := congrArg (fun v : F ↦ v=0) he
  have hb := congrArg (fun v : F ↦ v=0) ht
  simp only [mul_eq_zero, sub_eq_zero, hz, false_or, hz1, eq_iff_iff] at ha hb
  exact ⟨ha,hb.symm⟩

private def counter (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

private def kind [DecidableEq F] (a b c d : F) : Fin 6 :=
  if a=b then
    if a=c then if a=d then 0 else 4 else if a=d then 3 else 5
  else if a=c then if a=d then 2 else 5 else if b=c then if b=d then 1 else 5 else 5

omit [Field F] in
private theorem classified [DecidableEq F] (a b c d y : F)
    (he : ((a=b ∨ c=d) ↔ (a=c ∨ b=d)) ∧ ((a=c ∨ b=d) ↔ (a=d ∨ b=c))) :
    let t := kind a b c d
    (counter (a=b)=counter (t=0)+counter (t=3)+counter (t=4)) ∧
    (counter (a=c)=counter (t=0)+counter (t=2)+counter (t=4)) ∧
    (counter (a=d)=counter (t=0)+counter (t=2)+counter (t=3)) ∧
    (counter (b=c)=counter (t=0)+counter (t=1)+counter (t=4)) ∧
    (counter (b=d)=counter (t=0)+counter (t=1)+counter (t=3)) ∧
    (counter (c=d)=counter (t=0)+counter (t=1)+counter (t=2)) ∧
    (counter (a=y)+counter (b=y)+counter (c=y)+counter (d=y) + 2*counter (t=5) ≤
      3 + counter (t=0)) := by
  rcases he with ⟨he,hf⟩
  dsimp only
  by_cases hab : a=b <;> by_cases hac : a=c <;> by_cases had : a=d <;>
    by_cases hbc : b=c <;> by_cases hbd : b=d <;> by_cases hcd : c=d <;>
    simp_all [kind,counter] <;> split_ifs <;> simp_all


/-- Four boundary candidates cannot have a constant rational cross-ratio. -/
theorem not_constant_cross_ratio [DecidableEq F] (D : Finset F) (w : F → F)
    (P : Fin 4 → F[X]) (h : ℕ) (hd : D.card = 4*h) (hi : Function.Injective P)
    (hk : ∀ i, (P i).natDegree < 2*h)
    (ha : ∀ i, 3*h ≤ (D.filter (fun x ↦ (P i).eval x = w x)).card + 1) :
    ¬ ∃ z : F, (P 0-P 1)*(P 2-P 3) = C z*(P 0-P 2)*(P 1-P 3) := by
  classical
  rintro ⟨z,hz⟩
  have ne (i j : Fin 4) (hij : i ≠ j) : P i-P j ≠ 0 := sub_ne_zero.mpr (hi.ne hij)
  have hzero : z ≠ 0 := by
    rintro rfl
    simp [ne 0 1 (by decide), ne 2 3 (by decide)] at hz
  have hone : z ≠ 1 := by
    rintro rfl
    simp only [map_one,one_mul] at hz
    have he : (P 0-P 3)*(P 1-P 2)=0 := by linear_combination -hz
    simp [ne 0 3 (by decide), ne 1 2 (by decide)] at he
  let A (i : Fin 4) (x : F) := counter ((P i).eval x = w x)
  let B (i j : Fin 4) (x : F) := counter ((P i).eval x = (P j).eval x)
  let K (i : Fin 6) (x : F) := counter (kind ((P 0).eval x) ((P 1).eval x)
    ((P 2).eval x) ((P 3).eval x) = i)
  let N (i : Fin 6) := ∑ x ∈ D, K i x
  have local_counts (x : F) :
      B 0 1 x = K 0 x + K 3 x + K 4 x ∧ B 0 2 x = K 0 x + K 2 x + K 4 x ∧
      B 0 3 x = K 0 x + K 2 x + K 3 x ∧ B 1 2 x = K 0 x + K 1 x + K 4 x ∧
      B 1 3 x = K 0 x + K 1 x + K 3 x ∧ B 2 3 x = K 0 x + K 1 x + K 2 x ∧
      A 0 x + A 1 x + A 2 x + A 3 x + 2*K 5 x ≤ 3 + K 0 x := by
    have he := congrArg (fun p : F[X] ↦ p.eval x) hz
    simp only [eval_mul,eval_sub,eval_C] at he
    exact classified _ _ _ _ _ (collision_branches hzero hone he)
  have hc_pair (i j : Fin 4) (s t : Fin 6) (hij : i ≠ j)
      (he : ∀ x, B i j x = K 0 x + K s x + K t x) : N 0+N s+N t < 2*h := by
    have hsum : (∑ x ∈ D, B i j x) = N 0+N s+N t := by simp [he,N,sum_add_distrib]
    rw [← hsum]
    let S := D.filter (fun x ↦ (P i).eval x = (P j).eval x)
    have hh : (∑ x ∈ D, B i j x) = S.card := by simp [B,counter,S]
    rw [hh]
    by_contra! h'
    apply hij (hi ?_)
    apply eq_of_natDegree_lt_card_of_eval_eq (P i) (P j)
      (f := fun x : S ↦ x.val) Subtype.val_injective
    · exact fun x ↦ (mem_filter.mp x.property).2
    · rw [Fintype.card_coe]
      have hki := hk i
      have hkj := hk j
      omega
  have h01 := hc_pair 0 1 3 4 (by decide) (fun x ↦ (local_counts x).1)
  have h02 := hc_pair 0 2 2 4 (by decide) (fun x ↦ (local_counts x).2.1)
  have h03 := hc_pair 0 3 2 3 (by decide) (fun x ↦ (local_counts x).2.2.1)
  have h12 := hc_pair 1 2 1 4 (by decide) (fun x ↦ (local_counts x).2.2.2.1)
  have h13 := hc_pair 1 3 1 3 (by decide) (fun x ↦ (local_counts x).2.2.2.2.1)
  have h23 := hc_pair 2 3 1 2 (by decide) (fun x ↦ (local_counts x).2.2.2.2.2.1)
  have hsum : N 0+N 1+N 2+N 3+N 4+N 5 = 4*h := by
    have hclass (i : Fin 6) :
        counter (i=0)+counter (i=1)+counter (i=2)+counter (i=3)+counter (i=4)+counter (i=5)
          = 1 := by fin_cases i <;> decide
    simpa [N,← sum_add_distrib,K,hclass] using hd
  have hagr (i : Fin 4) : 3*h ≤ (∑ x ∈ D, A i x)+1 := by simpa [A,counter] using ha i
  have htot := Finset.sum_le_sum (s := D) (fun x _ ↦ (local_counts x).2.2.2.2.2.2)
  simp only [sum_add_distrib,← mul_sum, sum_const, nsmul_eq_mul, hd, Nat.cast_id] at htot
  change (∑ x ∈ D, A 0 x) + (∑ x ∈ D, A 1 x) + (∑ x ∈ D, A 2 x) + (∑ x ∈ D, A 3 x) + 2*N 5 ≤ 4*h*3+N 0 at htot
  have h0 := hagr 0
  have h1 := hagr 1
  have h2 := hagr 2
  have h3 := hagr 3
  omega


/-- The cross-ratio of four radius-`h+1` candidates has a nonconstant
representation by two polynomials of degree at most two. -/
theorem degree_one_or_two [DecidableEq F] (D : Finset F) (w : F → F)
    (P : Fin 4 → F[X]) (h : ℕ) (hd : D.card = 4*h) (hi : Function.Injective P)
    (hk : ∀ i, (P i).natDegree < 2*h)
    (ha : ∀ i, 3*h ≤ (D.filter (fun x ↦ (P i).eval x = w x)).card + 1) :
    ∃ A B : F[X], A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ 2 ∧ B.natDegree ≤ 2 ∧
      (P 0-P 1)*(P 2-P 3)*B = (P 0-P 2)*(P 1-P 3)*A ∧ ¬ ∃ z : F, A = C z*B := by
  classical
  let E (i : Fin 4) := D.filter (fun x ↦ (P i).eval x ≠ w x)
  let L (i : Fin 4) := Lagrange.nodal (E i) id
  let M := Lagrange.nodal D id
  have hL (i : Fin 4) : L i ≠ 0 := Lagrange.nodal_ne_zero
  have hdegL (i : Fin 4) : (L i).natDegree ≤ h+1 := by
    have hcounts := D.card_filter_add_card_filter_not (fun x ↦ (P i).eval x = w x)
    have haa := ha i
    simp only [L,Lagrange.natDegree_nodal,E,ne_eq]
    have hc : (D.filter (fun x ↦ (P i).eval x = w x)).card + (D.filter (fun x ↦ ¬ (P i).eval x = w x)).card = D.card := hcounts
    omega
  have factor_pair (i j : Fin 4) (hij : i ≠ j) :
      ∃ Q : F[X], Q ≠ 0 ∧ Q.natDegree ≤ 1 ∧ (P i-P j)*L i*L j=Q*M := by
    let f := (P i-P j)*L i*L j
    have hbound : f.natDegree ≤ 4*h+1 := by
      have hb := natDegree_mul_le (p := (P i-P j)*L i) (q := L j)
      have hc := natDegree_mul_le (p := P i-P j) (q := L i)
      have he := natDegree_sub_le (P i) (P j)
      have hi' := hk i
      have hj' := hk j
      have hli := hdegL i
      have hlj := hdegL j
      dsimp only [f]
      omega
    have hz : ZeroOn D f := by
      intro x hx
      dsimp only [f]
      simp only [eval_mul,eval_sub]
      by_cases hx1 : (P i).eval x = w x
      · by_cases hx2 : (P j).eval x = w x
        · simp [hx1,hx2]
        · have hroot : (L j).eval x = 0 := Lagrange.eval_nodal_at_node (v := id)
              (show x ∈ E j from mem_filter.mpr ⟨hx,hx2⟩)
          simp [hroot]
      · have hroot : (L i).eval x = 0 := Lagrange.eval_nodal_at_node (v := id)
            (show x ∈ E i from mem_filter.mpr ⟨hx,hx1⟩)
        simp [hroot]
    obtain ⟨Q, ⟨he,hq⟩, _⟩ := (zeroOn_iff_existsUnique_quotient_natDegree_le hbound).mp hz
    have hf : f ≠ 0 := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hi.ne hij)) (hL i)) (hL j)
    refine ⟨Q,fun hQ ↦ hf (by simpa [hQ] using he), ?_, he⟩
    rw [hd] at hq
    omega
  obtain ⟨q01,hn01,hd01,h01⟩ := factor_pair 0 1 (by decide)
  obtain ⟨q23,hn23,hd23,h23⟩ := factor_pair 2 3 (by decide)
  obtain ⟨q02,hn02,hd02,h02⟩ := factor_pair 0 2 (by decide)
  obtain ⟨q13,hn13,hd13,h13⟩ := factor_pair 1 3 (by decide)
  have hB := mul_ne_zero hn02 hn13
  refine ⟨q01*q23,q02*q13,mul_ne_zero hn01 hn23,hB, ?_, ?_, ?_⟩
  · exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)
  have hM : M ≠ 0 := Lagrange.nodal_ne_zero
  have he : (P 0-P 1)*(P 2-P 3)*(q02*q13) = (P 0-P 2)*(P 1-P 3)*(q01*q23) := by
    apply mul_right_cancel₀ (mul_ne_zero hM hM)
    calc
      _ = (P 0-P 1)*(P 2-P 3)*((q02*M)*(q13*M)) := by ring
      _ = (P 0-P 2)*(P 1-P 3)*((q01*M)*(q23*M)) := by rw [← h02,← h13,← h01,← h23]; ring
      _ = _ := by ring
  refine ⟨he,?_⟩
  rintro ⟨z,hz⟩
  apply not_constant_cross_ratio D w P h hd hi hk ha
  refine ⟨z,mul_right_cancel₀ hB ?_⟩
  calc
    _ = (P 0-P 2)*(P 1-P 3)*(q01*q23) := he
    _ = _ := by rw [hz]; ring


/-- A cross-ratio pulled back from a polynomial classifier of degree at least
three cannot occur at the four-head boundary. The numerator and denominator
of the rational function on the classifier are given in lowest terms. -/
theorem no_high_degree_pullback [DecidableEq F] (D : Finset F) (w : F → F)
    (P : Fin 4 → F[X]) (h : ℕ) (hd : D.card = 4*h) (hi : Function.Injective P)
    (hk : ∀ i, (P i).natDegree < 2*h)
    (ha : ∀ i, 3*h ≤ (D.filter (fun x ↦ (P i).eval x = w x)).card + 1)
    (H U V : F[X]) (hH : 2 < H.natDegree) (hc : IsCoprime U V) (hV : V ≠ 0) :
    (P 0-P 1)*(P 2-P 3)*(V.comp H) ≠ (P 0-P 2)*(P 1-P 3)*(U.comp H) := by
  intro hcomp
  obtain ⟨A,B,ha0,hb0,ha2,hb2,hab,hn⟩ := degree_one_or_two D w P h hd hi hk ha
  have hdif (i j : Fin 4) (hne : i ≠ j) := sub_ne_zero.mpr (hi.ne hne)
  have hbase := mul_ne_zero (hdif 0 2 (by decide)) (hdif 1 3 (by decide))
  have he : (V.comp H)*A = (U.comp H)*B := by
    apply mul_left_cancel₀ hbase
    calc
      _ = ((P 0-P 2)*(P 1-P 3)*A)*(V.comp H) := by ring
      _ = ((P 0-P 1)*(P 2-P 3)*(V.comp H))*B := by rw [← hab]; ring
      _ = _ := by rw [hcomp]; ring
  have cop : IsCoprime (U.comp H) (V.comp H) := hc.map (compRingHom H)
  have hUdiv : U.comp H ∣ A := cop.dvd_of_dvd_mul_left (he ▸ dvd_mul_right _ _)
  have hVdiv : V.comp H ∣ B := cop.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_right _ _)
  have dU := natDegree_le_of_dvd hUdiv ha0
  have dV := natDegree_le_of_dvd hVdiv hb0
  rw [natDegree_comp] at dU dV
  have hu : U.natDegree = 0 := by
    by_contra! hh
    have hmul := Nat.mul_le_mul_right H.natDegree (show 1 ≤ U.natDegree by omega)
    simp only [one_mul] at hmul
    omega
  have hv : V.natDegree = 0 := by
    by_contra! hh
    have hmul := Nat.mul_le_mul_right H.natDegree (show 1 ≤ V.natDegree by omega)
    simp only [one_mul] at hmul
    omega
  have eu := eq_C_of_natDegree_eq_zero hu
  have ev := eq_C_of_natDegree_eq_zero hv
  have hv0 : V.coeff 0 ≠ 0 := fun hh ↦ hV (by simpa [hh] using ev)
  apply hn
  refine ⟨U.coeff 0 / V.coeff 0,?_⟩
  rw [eu,ev, C_comp,C_comp] at he
  apply mul_left_cancel₀ (show C (V.coeff 0) ≠ 0 from C_ne_zero.mpr hv0)
  calc
    _ = C (U.coeff 0) * B := he
    _ = _ := by rw [← mul_assoc,← map_mul,mul_div_cancel₀ _ hv0]

#print axioms degree_one_or_two
#print axioms no_high_degree_pullback
end ProximityGap.FourHeadCrossRatio
