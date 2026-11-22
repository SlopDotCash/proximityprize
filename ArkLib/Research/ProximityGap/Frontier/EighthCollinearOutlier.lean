/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FiveHeadTrianglePacking
import ArkLib.Research.ProximityGap.Frontier.FirstPrimeQuarterSuccessor

/-! # One transverse head against a cluster on a polynomial line -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.EighthCollinearOutlier
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantMultiplicity
open HalfPredecessorRateQuarterDeterminantCollapse HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open _root_.ProximityGap
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
private abbrev core (dom : I ↪ F) (u v : I → F) (z : F[X] × F[X]) :=
  jointCore dom u v z.1 z.2

omit [Fintype F] in
private theorem factor_degree {P Q G : F[X]} {h d : ℕ} (ng : G ≠ 0)
    (nz : P ≠ 0 ∨ Q ≠ 0) (hd : h = max P.natDegree Q.natDegree)
    (hb : (P * G).natDegree ≤ d) (hc : (Q * G).natDegree ≤ d) :
    G.natDegree + h ≤ d := by
  rw [hd]
  by_cases p : P = 0
  · have q := nz.resolve_left (not_not.mpr p)
    rw [natDegree_mul q ng] at hc
    simp [p]; omega
  by_cases q : Q = 0
  · rw [natDegree_mul p ng] at hb
    simp [q]; omega
  rw [natDegree_mul p ng] at hb
  rw [natDegree_mul q ng] at hc
  omega

/-- Clear the denominator of a rational head against the primitive direction
of a polynomial line. This determinant is nonzero exactly when the rational
point with the given numerators and nonzero denominator is off that line. -/
def rationalDet {K : Type*} [Field K] (φ : F →+* K) (a b : F[X] × F[X])
    (denom num0 num1 : K[X]) : K[X] :=
  (primitiveIntercept a b).map φ * (num1-denom*a.2.map φ) -
    (primitiveSlope a b).map φ * (num0-denom*a.1.map φ)

/-- A rational transverse head of height `c` has at most `d+c+h` simultaneous
agreement sites in the whole cluster union. Each pair of polynomial cluster
heads has overlap at most `d-h` for the same primitive direction degree `h`. -/
theorem rational_overlap {K : Type*} [Field K] (φ : F →+* K) {s d c : ℕ}
    (dom : I ↪ F) (u v : I → F)
    (a b : F[X] × F[X]) (ab : a ≠ b) (L : Fin s → F[X] × F[X]) (inj : Function.Injective L)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (degA : a.1.natDegree ≤ d ∧ a.2.natDegree ≤ d)
    (deg : ∀ i, (L i).1.natDegree ≤ d ∧ (L i).2.natDegree ≤ d)
    (denom num0 num1 : K[X]) (degZ : denom.natDegree ≤ c)
    (degN : num0.natDegree ≤ d+c ∧ num1.natDegree ≤ d+c)
    (trans : rationalDet φ a b denom num0 num1 ≠ 0)
    (S : Finset I) (agree : ∀ x ∈ S, num0.eval (φ (dom x)) = φ (u x) * denom.eval (φ (dom x)) ∧
      num1.eval (φ (dom x)) = φ (v x) * denom.eval (φ (dom x))) :
    let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
    (∀ i j, i ≠ j → (core dom u v (L i) ∩ core dom u v (L j)).card + h ≤ d) ∧
      ((univ.biUnion fun i => core dom u v (L i)) ∩ S).card ≤ d+c+h := by
  classical
  let P := primitiveIntercept a b
  let Q := primitiveSlope a b
  let h := max P.natDegree Q.natDegree
  choose f hf hg using fun i => exists_polynomial_factor_of_lineDeterminant_eq_zero a b (L i) ab (coll i)
  have nz : P ≠ 0 ∨ Q ≠ 0 := by
    rcases primitiveDirection_eval_ne_zero ab (0 : F) with hp | hq
    · exact .inl (fun e => hp (by change P.eval 0 = 0; simp [e]))
    · exact .inr (fun e => hq (by change Q.eval 0 = 0; simp [e]))
  have slope (i j : Fin s) :
      (L i).1 - (L j).1 = P * (f i - f j) ∧ (L i).2 - (L j).2 = Q * (f i - f j) := by
    constructor
    · unfold P; linear_combination hf i - hf j
    · unfold Q; linear_combination hg i - hg j
  constructor
  · intro i j ij
    obtain ⟨h₁,h₂⟩ := slope i j
    have nonzero : f i - f j ≠ 0 := by
      intro e
      simp only [e,mul_zero] at h₁ h₂
      exact ij (inj (Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)))
    have cap := factor_degree nonzero nz (rfl : h = _)
      (h₁ ▸ (natDegree_sub_le ..).trans (max_le (deg i).1 (deg j).1))
      (h₂ ▸ (natDegree_sub_le ..).trans (max_le (deg i).2 (deg j).2))
    have count : (core dom u v (L i) ∩ core dom u v (L j)).card ≤ (f i - f j).natDegree := by
      apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero nonzero dom.injective.injOn
      intro x hx
      obtain ⟨hi,hj⟩ := mem_inter.mp hx
      obtain ⟨hxi,hyi⟩ := (mem_filter.mp hi).2
      obtain ⟨hxj,hyj⟩ := (mem_filter.mp hj).2
      rcases primitiveDirection_eval_ne_zero ab (dom x) with hp | hq
      · have hh := congrArg (fun w : F[X] => w.eval (dom x)) h₁
        simp only [eval_sub,eval_mul,hxi,hxj,sub_self] at hh
        simpa only [eval_sub] using (mul_eq_zero.mp hh.symm).resolve_left hp
      · have hh := congrArg (fun w : F[X] => w.eval (dom x)) h₂
        simp only [eval_sub,eval_mul,hyi,hyj,sub_self] at hh
        simpa only [eval_sub] using (mul_eq_zero.mp hh.symm).resolve_left hq
    exact (Nat.add_le_add_right count _).trans cap
  · have coord {N A : K[X]} (hn : N.natDegree≤d+c) (ha : A.natDegree≤d) :
        (N-denom*A).natDegree≤d+c := by
      have hz := natDegree_mul_le (p:=denom) (q:=A)
      exact (natDegree_sub_le ..).trans (max_le hn (by omega))
    have bv := coord degN.2 (natDegree_map_le.trans degA.2 : (a.2.map φ).natDegree ≤ d)
    have br := coord degN.1 (natDegree_map_le.trans degA.1 : (a.1.map φ).natDegree ≤ d)
    have pdeg : ((primitiveIntercept a b).map φ).natDegree ≤ h :=
      natDegree_map_le.trans (le_max_left ..)
    have qdeg : ((primitiveSlope a b).map φ).natDegree ≤ h :=
      natDegree_map_le.trans (le_max_right ..)
    have bound : (rationalDet φ a b denom num0 num1).natDegree≤d+c+h := by
      apply (natDegree_sub_le ..).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le ..).trans (by omega)
      · exact (natDegree_mul_le ..).trans (by omega)
    apply le_trans _ bound
    apply Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero trans
      (φ.injective.comp dom.injective).injOn
    intro x hx
    obtain ⟨xU,xS⟩ := mem_inter.mp hx
    obtain ⟨i,_,xi⟩ := mem_biUnion.mp xU
    obtain ⟨ru,rv⟩ := agree x xS
    obtain ⟨iu,iv⟩ := (mem_filter.mp xi).2
    have eq := congrArg (fun w : F[X] => w.eval (dom x))
      (primitive_relation_of_lineDeterminant_eq_zero a b (L i) ab (coll i))
    simp only [eval_mul,eval_sub,iu,iv] at eq
    have mapped := congrArg φ eq
    simp only [map_mul, map_sub] at mapped
    change (rationalDet φ a b denom num0 num1).eval (φ (dom x)) = 0
    simp only [rationalDet,eval_sub,eval_mul,eval_map_apply,ru,rv]
    linear_combination denom.eval (φ (dom x)) * mapped

/-- The same primitive-direction degree is subtracted from every pair-overlap
budget and added once to the transverse-intersection budget for the whole union. -/
theorem overlap {s d : ℕ} (dom : I ↪ F) (u v : I → F)
    (a b z : F[X] × F[X]) (ab : a ≠ b) (out : threeLineDeterminant a b z ≠ 0)
    (L : Fin s → F[X] × F[X]) (inj : Function.Injective L)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (degA : a.1.natDegree ≤ d ∧ a.2.natDegree ≤ d)
    (degZ : z.1.natDegree ≤ d ∧ z.2.natDegree ≤ d)
    (deg : ∀ i, (L i).1.natDegree ≤ d ∧ (L i).2.natDegree ≤ d) :
    let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
    (∀ i j, i ≠ j → (core dom u v (L i) ∩ core dom u v (L j)).card + h ≤ d) ∧
      ((univ.biUnion fun i => core dom u v (L i)) ∩ core dom u v z).card ≤ d + h := by
  have trans : rationalDet (RingHom.id F) a b 1 z.1 z.2 ≠ 0 := by
    intro e
    apply out
    unfold threeLineDeterminant
    rw [referenceIntercept_eq_content_mul_primitive ab, referenceSlope_eq_content_mul_primitive ab]
    simp only [rationalDet,Polynomial.map_id,one_mul] at e
    linear_combination referenceContent a b * e
  have h := rational_overlap (RingHom.id F) dom u v a b ab L inj coll degA deg 1 z.1 z.2
    (c:=0) (by simp) (by simpa using degZ) trans (core dom u v z) (fun x hx => by
      simpa using (mem_filter.mp hx).2)
  simpa using h

omit [Fintype I] in
private theorem union_degree {s : ℕ} (C : Fin s → Finset I) (c b : ℕ)
    (big : ∀ i, c ≤ (C i).card) (pair : ∀ i j, i ≠ j → (C i ∩ C j).card ≤ b) (a : ℕ) :
    2 * a * (s * c) ≤ s * (s - 1) * b + a * (a + 1) * (univ.biUnion C).card := by
  classical
  let U := univ.biUnion C
  let S (i : Fin s) := (C i).subtype (fun x => x ∈ U)
  have sub (i : Fin s) : C i ⊆ U := fun _ hx => mem_biUnion.mpr ⟨i,mem_univ i,hx⟩
  have size (i : Fin s) : (S i).card = (C i).card := by
    rw [card_subtype]; simp [filter_true_of_mem (fun _ hx => sub i hx)]
  have inter (i j : Fin s) : S i ∩ S j = (C i ∩ C j).subtype (fun x => x ∈ U) := by
    ext; simp [S]
  have e := RateHalfRichHeadCensus.incidence_bound S (fun i => (size i).symm ▸ big i)
    (fun i j ij => by rw [inter,card_subtype]; exact (card_le_card (filter_subset ..)).trans (pair i j ij)) a
  simpa only [Fintype.card_coe] using e

/-- An off-line rational head must pay for the gap between the union lower
bound and the available regular agreements in denominator height or lost sites.
The primitive direction degree cancels for every moment order `a < j`. -/
theorem rational_tangent_cost {K : Type*} [Field K] (φ : F →+* K) {j d C c t ell : ℕ}
    (dom : I ↪ F) (u v : I → F)
    (base dir : F[X] × F[X]) (ab : base ≠ dir)
    (L : Fin j → F[X] × F[X]) (inj : Function.Injective L)
    (coll : ∀ i, lineDeterminant base dir (L i) = 0)
    (degA : base.1.natDegree ≤ d ∧ base.2.natDegree ≤ d)
    (deg : ∀ i, (L i).1.natDegree ≤ d ∧ (L i).2.natDegree ≤ d)
    (big : ∀ i, C ≤ (core dom u v (L i)).card)
    (denom num0 num1 : K[X]) (degZ : denom.natDegree ≤ c)
    (degN : num0.natDegree ≤ d+c ∧ num1.natDegree ≤ d+c)
    (trans : rationalDet φ base dir denom num0 num1 ≠ 0)
    (S : Finset I) (agree : ∀ x ∈ S, num0.eval (φ (dom x)) = φ (u x) * denom.eval (φ (dom x)) ∧
      num1.eval (φ (dom x)) = φ (v x) * denom.eval (φ (dom x)))
    (enough : t ≤ S.card+ell) (a : ℕ) (aj : a<j) :
    a*(a+1)*t + 2*a*(j*C) ≤
      a*(a+1)*(Fintype.card I+d+c+ell) + j*(j-1)*d := by
  classical
  by_cases az : a=0
  · simp [az]
  let h := max (primitiveIntercept base dir).natDegree (primitiveSlope base dir).natDegree
  let U := univ.biUnion fun i => core dom u v (L i)
  obtain ⟨pairs,cap⟩ := rational_overlap φ dom u v base dir ab L inj coll degA deg
    denom num0 num1 degZ degN trans S agree
  change (U ∩ S).card≤d+c+h at cap
  have hd : h≤d := by
    let i : Fin j := ⟨0,by omega⟩
    let k : Fin j := ⟨1,by omega⟩
    have ne : i≠k := by simp [i,k]
    have hpair := pairs i k ne
    change _ + h ≤ d at hpair
    omega
  have pu := union_degree (fun i => core dom u v (L i)) C (d-h) big
    (fun i k ne => Nat.le_sub_of_add_le (pairs i k ne)) a
  change 2*a*(j*C) ≤ j*(j-1)*(d-h)+a*(a+1)*U.card at pu
  have sum := card_union_add_card_inter U S
  have full := card_le_univ (U ∪ S)
  have su : U.card+t ≤ Fintype.card I+d+c+ell+h := by omega
  have times := Nat.mul_le_mul_left (a*(a+1)) su
  have coeff : a*(a+1)≤j*(j-1) := by
    rw [Nat.mul_comm j (j-1)]
    exact Nat.mul_le_mul (by omega) (by omega)
  have cancel := Nat.mul_le_mul_right h coeff
  have restore : j*(j-1)*(d-h)+j*(j-1)*h=j*(j-1)*d := by
    rw [← Nat.mul_add,Nat.sub_add_cancel hd]
  rw [Nat.mul_add (a*(a+1)) U.card t, Nat.mul_add (a*(a+1)) (Fintype.card I+d+c+ell) h] at times
  omega

/-- Aggregate the off-line inequalities over a family with one global
denominator-height budget and one global regular-agreement loss budget.
A positive gap yields an integer population cap even when some sections
have more regular agreements than the requested threshold. -/
theorem off_line_population {α : Type*} (T : Finset α) (sites height : α → ℕ)
    {A coreTerm baseCost t gap C loss : ℕ}
    (gap_pos : 0<gap) (gap_bound : baseCost+gap≤A*t+coreTerm)
    (per : ∀ z ∈ T, A*sites z+coreTerm≤baseCost+A*height z)
    (budget : ∑ z ∈ T, height z ≤ C)
    (enough : T.card*t ≤ (∑ z ∈ T, sites z)+loss) :
    T.card ≤ A*(C+loss)/gap := by
  have summ := Finset.sum_le_sum per
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at summ
  change A*(∑ z ∈ T, sites z) + T.card*coreTerm ≤
    T.card*baseCost + A*(∑ z ∈ T, height z) at summ
  have priced := Nat.mul_le_mul_left T.card gap_bound
  have regular := Nat.mul_le_mul_left A enough
  have cap := Nat.mul_le_mul_left A budget
  simp only [Nat.mul_add] at priced regular ⊢
  have rearrange : A*(T.card*t) = T.card*(A*t) := by ring
  rw [rearrange] at regular
  apply (Nat.le_div_iff_mul_le gap_pos).mpr
  omega

/-- Population of any finite family of off-line rational tangents, using actual
polynomial heads, regular agreement sets, and aggregate height and loss bounds.
Distinct labels may have the same tangent data. -/
theorem rational_tangent_population {K α : Type*} [Field K] (φ : F →+* K)
    {j d C t gap totalHeight loss : ℕ}
    (dom : I ↪ F) (u v : I → F) (base dir : F[X] × F[X]) (ab : base ≠ dir)
    (L : Fin j → F[X] × F[X]) (inj : Function.Injective L)
    (coll : ∀ i, lineDeterminant base dir (L i) = 0)
    (degA : base.1.natDegree ≤ d ∧ base.2.natDegree ≤ d)
    (deg : ∀ i, (L i).1.natDegree ≤ d ∧ (L i).2.natDegree ≤ d)
    (big : ∀ i, C ≤ (core dom u v (L i)).card)
    (T : Finset α) (denom num0 num1 : α → K[X]) (height : α → ℕ) (S : α → Finset I)
    (degZ : ∀ z ∈ T, (denom z).natDegree ≤ height z)
    (degN : ∀ z ∈ T, (num0 z).natDegree ≤ d+height z ∧ (num1 z).natDegree ≤ d+height z)
    (trans : ∀ z ∈ T, rationalDet φ base dir (denom z) (num0 z) (num1 z) ≠ 0)
    (agree : ∀ z ∈ T, ∀ x ∈ S z,
      (num0 z).eval (φ (dom x)) = φ (u x) * (denom z).eval (φ (dom x)) ∧
      (num1 z).eval (φ (dom x)) = φ (v x) * (denom z).eval (φ (dom x)))
    (budget : ∑ z ∈ T, height z ≤ totalHeight)
    (enough : T.card*t ≤ (∑ z ∈ T, (S z).card)+loss)
    (a : ℕ) (aj : a<j) (gap_pos : 0<gap)
    (gap_bound : a*(a+1)*(Fintype.card I+d) + j*(j-1)*d + gap ≤ a*(a+1)*t + 2*a*(j*C)) :
    T.card ≤ a*(a+1)*(totalHeight+loss)/gap := by
  apply off_line_population T (fun z => (S z).card) height gap_pos gap_bound _ budget enough
  intro z hz
  have cost := rational_tangent_cost φ dom u v base dir ab L inj coll degA deg big (denom z)
    (num0 z) (num1 z) (degZ z hz) (degN z hz) (trans z hz) (S z) (agree z hz)
    (ell:=0) (Nat.le_refl (S z).card) a aj
  simp only [Nat.add_zero] at cost
  rw [Nat.mul_add (a*(a+1)) (Fintype.card I+d) (height z)] at cost
  omega

/-- Five collinear heads and one transverse head cannot all have cores above
the common threshold `(3n + 13d)/13`. Four collinear heads give the separate bound
`5c ≤ n + 7d`. Both estimates count intersections of actual received cores. -/
theorem cluster_cap {s d c : ℕ} (dom : I ↪ F) (u v : I → F)
    (a b z : F[X] × F[X]) (ab : a ≠ b) (out : threeLineDeterminant a b z ≠ 0)
    (L : Fin s → F[X] × F[X]) (inj : Function.Injective L)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (degA : a.1.natDegree ≤ d ∧ a.2.natDegree ≤ d)
    (degZ : z.1.natDegree ≤ d ∧ z.2.natDegree ≤ d)
    (deg : ∀ i, (L i).1.natDegree ≤ d ∧ (L i).2.natDegree ≤ d)
    (big : ∀ i, c ≤ (core dom u v (L i)).card) (bigZ : c ≤ (core dom u v z).card) :
    (s = 5 → 13 * c ≤ 3 * Fintype.card I + 13 * d) ∧
      (s = 4 → 5 * c ≤ Fintype.card I + 7 * d) := by
  classical
  let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
  let C (i : Fin s) := core dom u v (L i)
  let U := univ.biUnion C
  let outCore := core dom u v z
  obtain ⟨hp, hz⟩ := overlap dom u v a b z ab out L inj coll degA degZ deg
  have pair (i j : Fin s) (ij : i ≠ j) : (C i ∩ C j).card ≤ d - h :=
    Nat.le_sub_of_add_le (hp i j ij)
  have add : U.card + c ≤ Fintype.card I + (d + h) := by
    have e := card_union_add_card_inter U outCore
    have bnd := card_le_univ (U ∪ outCore)
    change (U ∩ outCore).card ≤ d + h at hz
    change c ≤ outCore.card at bigZ
    omega
  constructor
  · rintro rfl
    have le := hp (0 : Fin 5) 1 (by decide)
    change _ + h ≤ d at le
    have bnd := union_degree C c (d - h) big pair 2
    change 4 * (5 * c) ≤ 20 * (d - h) + 6 * U.card at bnd
    omega
  · rintro rfl
    have le := hp (0 : Fin 4) 1 (by decide)
    change _ + h ≤ d at le
    have bnd := union_degree C c (d - h) big pair 1
    change 2 * (4 * c) ≤ 12 * (d - h) + 2 * U.card at bnd
    omega

variable [Nonempty I] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private theorem rich_core (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 394264576)
    {z : LineParameter F} (hz : z ∈ lineParameters fam) {m c : ℕ}
    (cap : ∀ w : ℕ, m * max 1 (394264576 - w) + w ≤ 1073741824 → c ≤ w)
    (big : m ≤ (pointsOn fam z).card) : c ≤ (core dom (u 0) (u 1) z).card := by
  have h := pointsOn_card_mul_max_add_core_le fam hz
  rw [ht,hn] at h
  exact cap _ ((Nat.add_le_add_right (Nat.mul_le_mul_right _ big) _).trans h)

/-- Five collinear heads with at least 57 labels each force every further
head carrying 57 labels onto their line at the eighth-rate attack count. -/
theorem five_force (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 394264576)
    (L : Fin 5 → LineParameter F) (inj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam) (big : ∀ i, 57 ≤ (pointsOn fam (L i)).card)
    (coll : ∀ i, threeLineDeterminant (L 0) (L 1) (L i) = 0)
    {z : LineParameter F} (hz : z ∈ lineParameters fam) (zb : 57 ≤ (pointsOn fam z).card) :
    threeLineDeterminant (L 0) (L 1) z = 0 := by
  by_contra outside
  have deg {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      w.1.natDegree ≤ 134217727 ∧ w.2.natDegree ≤ 134217727 := by
    have ⟨h, h'⟩ := lineParameter_degree_lt fam hw
    exact ⟨Nat.le_of_lt_succ h, Nat.le_of_lt_succ h'⟩
  have rich {w : LineParameter F} (hw : w ∈ lineParameters fam) (hb : 57 ≤ (pointsOn fam w).card) :
      382004302 ≤ (core dom (u 0) (u 1) w).card :=
    rich_core fam hn ht hw (fun _ _ => by omega) hb
  have h := (cluster_cap dom (u 0) (u 1) (L 0) (L 1) z (inj.ne (by decide)) outside L inj
    (fun i => by simpa only [lineDeterminant,threeLineDeterminant,mul_comm] using coll i)
    (deg (hl 0)) (deg hz) (fun i => deg (hl i)) (fun i => rich (hl i) (big i)) (rich hz zb)).1 rfl
  rw [hn] at h
  omega

omit [Nonempty I] in
/-- At 5/8 errors four collinear saturated cores and one transverse saturated
core would already exceed the available degree by two. -/
theorem saturated_four (dom : I ↪ F) (u v : I → F) (hn : Fintype.card I = 1073741824)
    (L : Fin 4 → LineParameter F) (inj : Function.Injective L) (z : LineParameter F)
    (coll : ∀ i, lineDeterminant (L 0) (L 1) (L i) = 0)
    (deg : ∀ i, (L i).1.natDegree ≤ 134217727 ∧ (L i).2.natDegree ≤ 134217727)
    (degZ : z.1.natDegree ≤ 134217727 ∧ z.2.natDegree ≤ 134217727)
    (big : ∀ i, 402653183 ≤ (core dom u v (L i)).card)
    (bigZ : 402653183 ≤ (core dom u v z).card) : threeLineDeterminant (L 0) (L 1) z = 0 := by
  by_contra outside
  have h := (cluster_cap dom u v (L 0) (L 1) z (inj.ne (by decide)) outside L inj coll
    (deg 0) degZ deg big bigZ).2 rfl
  rw [hn] at h
  omega

private def reorder (q : Fin 5) : Fin 6 → Fin 6 :=
  ![(q.succAbove 0).castSucc, (q.succAbove 1).castSucc, (q.succAbove 2).castSucc,
    (q.succAbove 3).castSucc, q.castSucc, 5]

private theorem reorder_inj : ∀ q, Function.Injective (reorder q) := by decide

/-- Six heads carrying 1,216 labels force *all* heads carrying 57 labels onto a
single polynomial line. The six heads may come from any injective domain. -/
theorem six (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 394264576)
    (L : Fin 6 → LineParameter F) (inj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam) (big : ∀ i, 1216 ≤ (pointsOn fam (L i)).card) :
    ∃ a b : LineParameter F, a ≠ b ∧ ∀ z ∈ lineParameters fam, 57 ≤ (pointsOn fam z).card →
      threeLineDeterminant a b z = 0 := by
  classical
  obtain ⟨q,hq⟩ := FiveHeadTrianglePacking.eighth fam hn ht (L ∘ Fin.castSucc)
    (inj.comp (Fin.castSucc_injective _)) (fun _ => hl _) (fun _ => big _)
  let A := L ∘ reorder q
  have ai : Function.Injective A := inj.comp (reorder_inj q)
  have ac (i : Fin 4) : threeLineDeterminant (A 0) (A 1) (A i.castSucc.castSucc) = 0 := by
    fin_cases i
    · simp [threeLineDeterminant]
    · simp [threeLineDeterminant]; ring
    · exact hq (Equiv.refl _)
    · simpa [A,reorder,FiveHeadTrianglePacking.four, Equiv.swap_apply_def, Fin.reduceEq] using hq (Equiv.swap 2 3)
  let j : Fin 5 → Fin 6 := ![0,1,2,4,5]
  have one := FiveHeadTrianglePacking.eighth_outlier fam hn ht (A ∘ j)
    (ai.comp (by decide : Function.Injective j)) (fun _ => hl _) (fun _ => big _) (ac 2)
  refine ⟨A 0, A 1, ai.ne (by decide), ?_⟩
  intro z hz hb
  have lift (aux : Fin 5 → Fin 6) (key : Function.Injective aux)
      (h0 : aux 0 = 0) (h1 : aux 1 = 1)
      (h : ∀ i, threeLineDeterminant (A 0) (A 1) (A (aux i)) = 0) :
      threeLineDeterminant (A 0) (A 1) z = 0 := by
    simpa only [Function.comp_apply, h0, h1] using five_force fam hn ht (A ∘ aux)
      (ai.comp key) (fun _ => hl _) (fun i => (by decide : 57 ≤ 1216).trans (big _))
      (by simpa only [Function.comp_apply,h0,h1] using h) hz hb
  rcases one with off | off
  · apply lift ![0,1,2,3,4] (by decide) rfl rfl
    intro i
    fin_cases i
    · exact ac 0
    · exact ac 1
    · exact ac 2
    · exact ac 3
    · exact off
  · apply lift ![0,1,2,3,5] (by decide) rfl rfl
    intro i
    fin_cases i
    · exact ac 0
    · exact ac 1
    · exact ac 2
    · exact ac 3
    · exact off

private theorem enumerate {J : Type} (H : Finset J) {m : ℕ} (enough : m ≤ H.card) :
    ∃ f : Fin m → J, Function.Injective f ∧ ∀ i, f i ∈ H := by
  obtain ⟨S,sub,k⟩ := exists_subset_card_eq enough
  let e := S.equivFinOfCardEq k
  exact ⟨fun i => (e.symm i).val, fun _ _ h => e.symm.injective (Subtype.ext h),
    fun i => sub (e.symm i).property⟩

private theorem packing_table {s w c B : ℕ} (size : w ≤ 1073741824)
    (mode : (c = 393705336 ∧ s ≤ 24 ∧ B = 2066952976) ∨
            (c = 389880852 ∧ s ≤ 33 ∧ B = 2147267140))
    (tan : let a := (s + 2) / 3
      2 * a * (s * c) ≤ s * (s - 1) * 134217727 + a * (a + 1) * w) :
    w + (1073741824 - w) * s ≤ B := by
  rcases mode with ⟨rfl, hs, rfl⟩ | ⟨rfl, hs, rfl⟩ <;>
    interval_cases s <;> norm_num at tan ⊢ <;> omega

/-- If six heads reach population 1,216, all heads with at least 156 points
together still fit the length-doubled security budget. At the higher population
threshold the same incidence argument leaves over eighty million unused labels. -/
theorem covered (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (hn : Fintype.card I = 1073741824) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 394264576)
    (H : Finset (LineParameter F)) (hH : H ⊆ lineParameters fam)
    (six_rich : 6 ≤ (H.filter fun z => 1216 ≤ (pointsOn fam z).card).card)
    {m B : ℕ} (branch : (m = 1216 ∧ B = 2066952976) ∨ (m = 156 ∧ B = 2147267140))
    (pop : ∀ z ∈ H, m ≤ (pointsOn fam z).card) :
    (H.biUnion (pointsOn fam)).card ≤ B := by
  classical
  obtain ⟨L,inj,member⟩ := enumerate _ six_rich
  have selected (i : Fin 6) := mem_filter.mp (member i)
  obtain ⟨a,b,ab,col⟩ := six fam hn ht L inj (fun i => hH (selected i).1) (fun i => (selected i).2)
  have loc := TerminalCollinearHeadCount.collinear_card fam H hH a b ab (fun z hz => by
    simpa only [lineDeterminant,threeLineDeterminant,mul_comm] using
      col z (hH hz) ((show 57 ≤ m by rcases branch with h|h <;> omega).trans (pop z hz)))
  rw [hn] at loc
  let c := if m = 1216 then 393705336 else 389880852
  let maxHeads := if m = 1216 then 24 else 33
  let S (z : LineParameter F) := core dom (u 0) (u 1) z
  have core_size {z : LineParameter F} (hz : z ∈ H) : c ≤ (S z).card := by
    apply rich_core fam hn ht (hH hz) _ (pop z hz)
    dsimp only [c]; rcases branch with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num <;> intro _ h <;> omega
  have pair {x y : LineParameter F} (hx : x ∈ H) (hy : y ∈ H) (ne : x ≠ y) :
      (S x ∩ S y).card ≤ 134217727 := by
    have ⟨xd,xs⟩ := lineParameter_degree_lt fam (hH hx)
    have ⟨yd,ys⟩ := lineParameter_degree_lt fam (hH hy)
    apply FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le dom _ _ (by decide) xd xs yd ys
    by_contra! h
    exact ne (Prod.ext h.1 h.2)
  have hmax : H.card ≤ maxHeads := by
    by_contra! larger
    obtain ⟨f,fi,fh⟩ := enumerate H (Nat.succ_le_of_lt larger)
    let a := if m = 1216 then 9 else 12
    have bound := RateHalfRichHeadCensus.incidence_bound (fun i => S (f i))
      (fun i => core_size (fh i)) (fun i j ij => pair (fh i) (fh j) (fi.ne ij)) a
    rw [hn] at bound
    dsimp only [c,maxHeads,a] at bound
    rcases branch with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num at bound
  let e := H.equivFin
  let f (i : Fin H.card) := (e.symm i).val
  have fi : Function.Injective f := fun _ _ h => e.symm.injective (Subtype.ext h)
  let Zs := H.biUnion S
  have uni : (univ.biUnion fun i => S (f i)) = Zs := by
    ext x
    simp only [Zs,mem_biUnion,mem_univ,true_and]
    exact ⟨fun ⟨i,hi⟩ => ⟨f i,(e.symm i).property,hi⟩,
      fun ⟨z,hz,hx⟩ => ⟨e ⟨z,hz⟩,by simpa [f] using hx⟩⟩
  have tt := union_degree (fun i => S (f i)) c 134217727
    (fun i => core_size (e.symm i).property)
    (fun i j ij => pair (e.symm i).property (e.symm j).property (fi.ne ij)) ((H.card+2)/3)
  rw [uni] at tt
  change _ ≤ Zs.card + (1073741824 - Zs.card)*H.card at loc
  apply loc.trans (packing_table (by rw [←hn]; exact card_le_univ Zs) _ tt)
  rcases branch with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .inl ⟨rfl,hmax,rfl⟩
  · exact .inr ⟨rfl,hmax,rfl⟩

#print axioms rational_tangent_population
#print axioms rational_overlap
#print axioms rational_tangent_cost
#print axioms off_line_population
#print axioms covered
#print axioms six
#print axioms saturated_four
#print axioms overlap
#print axioms cluster_cap
end ArkLib.ProximityGap.Frontier.EighthCollinearOutlier
