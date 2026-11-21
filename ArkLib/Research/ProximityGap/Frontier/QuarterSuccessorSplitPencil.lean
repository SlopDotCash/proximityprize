/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-! # The first unresolved quarter-rate step and three disjoint full fibers -/
namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitPencil
open Polynomial Finset Code _root_.ProximityGap
open SmoothFourHeadFibers SmoothFourHeadColored SecondPrimeQuarticInterpolation
open scoped NNReal ENNReal

/-- A double interpolant of value degree three still has positive surplus at the successor. -/
theorem double_capacity : 1073741824*50 <
    Fintype.card (Monomials 16 3 268435455 (2*626349396)) := by
  simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- The seven units of slack permit only one direction degree, three total
pair-root deficits and zero common sites when the direction is nonconstant. -/
theorem root_deficits (L D R direction u : ℕ) (bad : 1073741824<L) (pos : 1≤direction)
    (deg : 3*direction≤D)
    (count : 6*(626349396-1)+L+178956965*u+2*D+3*R ≤ 3*1073741824+6*268435455) :
    direction=1 ∧ D=3 ∧ R=0 ∧ u=0 ∧ L≤1073741826 := by omega

private def project : Fin 4 → Fin 3 := ![0,1,2,0]

/-- Three degree-bounded polynomials with the full pair-fiber pattern supply at
least n+2 actual bad labels in a single received stack at the successor step. -/
theorem pencil_mass {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (fieldRoom : 1073741826^2 < Fintype.card F)
    (raw : I → Fin 4) (f : Fin 3 → F[X])
    (degree : ∀ i, (f i).natDegree≤268435454)
    (counts : ∀ j, (univ.filter (fun x => raw x = j)).card =
      (![268435454,268435454,268435454,268435462] : Fin 4 → ℕ) j)
    (pairs : ∀ x i j, (f i).eval (dom x) = (f j).eval (dom x) ↔ coincide (raw x) i j) :
    (1073741826 : ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F)
      (ReedSolomon.code dom 268435456 : Set (I → F)) (447392428/1073741824) := by
  classical
  obtain ⟨col,hf,hc⟩ := refine_fibers raw 268435454 0 89478487 1 counts
  let select (s : Finset (Fin 8)) := univ.filter fun x => col x ∈ s
  have scard (s : Finset (Fin 8)) : (select s).card = ∑ i ∈ s, weight 268435454 0 89478487 1 i := by
    rw [← sum_card_fiberwise_eq_card_filter univ s col]
    exact Finset.sum_congr rfl (fun j _ => hc j)
  have ccard (i : Fin 3) : (select (coreClasses i)).card=626349395 := by
    rw [scard]
    fin_cases i <;> decide
  have no_three (x : I) : col x≠3 := by
    intro bad
    have h := hc 3
    have hpos := card_pos.mpr (show (univ.filter fun y => col y=3).Nonempty from ⟨x,mem_filter.mpr ⟨mem_univ _,bad⟩⟩)
    change _ = 0 at h
    omega
  let A : FourHeadWitness.CoreAllocation dom 268435456 (447392428/1073741824) := {
    head := fun h => f (project h)
    background := fun x => (f (owner (col x))).eval (dom x)
    ordinary := select ordinaryClasses
    special := univ.filter (fun x => col x=7)
    core := fun h => select (coreClasses (project h))
    degree_head := fun j => (degree_le_natDegree).trans_lt (by exact_mod_cast (show (f (project j)).natDegree<268435456 from (degree _).trans_lt (by decide)))
    degree_first := fun j => by
      have h := natDegree_mul_le (p:=(Polynomial.X : F[X])) (q:=f (project j))
      rw [natDegree_X] at h
      have bound := h.trans_lt (show 1 + (f (project j)).natDegree<268435456 by have := degree (project j);omega)
      exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr bound)
    disjoint := disjoint_left.mpr (fun x ho hs => by
      have hm := (mem_filter.mp ho).2
      rw [(mem_filter.mp hs).2] at hm
      exact (by decide : (7:Fin 8)∉ordinaryClasses) hm)
    core_disjoint := fun h => disjoint_left.mpr (fun x hc hs => by
      have hm := (mem_filter.mp hc).2
      rw [(mem_filter.mp hs).2] at hm
      exact (by decide : ∀ i, (7:Fin 8)∉coreClasses i) _ hm)
    core_agrees := fun j x hx => by
      apply (pairs x _ _).2
      rw [← hf]
      exact (by decide : ∀ i c, c∈coreClasses i → c≠3 → coincide (coarse c) i (owner c))
        _ _ (mem_filter.mp hx).2 (no_three x)
    core_rank := fun j => by rw [ccard];decide
    core_size := fun j => by
      rw [ccard,hn]
      change (1-(447392428:ℝ≥0)/1073741824)*1073741824 ≤ 626349396
      rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by norm_num)]
      norm_num
    ordinary_mismatch := fun x hx => by
      let j := miss (col x)
      have hj : project j.castSucc=j := (by decide : ∀ j:Fin 3, project j.castSucc=j) j
      refine ⟨j.castSucc,?_⟩
      rw [hj]
      exact fun h => (by decide : ∀ c, c∈ordinaryClasses → ¬coincide (coarse c) (miss c) (owner c)) _
        (mem_filter.mp hx).2 (hf x ▸ (pairs x _ _).1 h) }
  have ocard : A.ordinary.card=1073741823 := (scard ordinaryClasses).trans (by decide)
  have spec : A.special.card=1 := hc 7
  have roots (x : ↥A.special) : (univ.image fun h => (A.head h).eval (dom x.val)).card=3 := by
    let v (j : Fin 3) := (f j).eval (dom x.val)
    have hx : raw x.val=3 := by rw [← hf,(mem_filter.mp x.property).2];rfl
    have inj : Function.Injective v := by
      intro i j h
      have h' := (pairs x.val i j).1 h
      rw [hx] at h'
      exact (by decide : ∀ i j, coincide 3 i j → i=j) _ _ h'
    have eq : (univ.image (fun h => (A.head h).eval (dom x.val)))=univ.image v := by
      ext z
      simp only [mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨h,rfl⟩; exact ⟨project h,rfl⟩
      · rintro ⟨j,rfl⟩
        exact ⟨j.castSucc,congrArg v ((by decide : ∀ t:Fin 3,project t.castSucc=t) j)⟩
    rw [eq,card_image_of_injective _ inj,card_univ,Fintype.card_fin]
  have count : A.count=1073741826 := by
    simp only [FourHeadWitness.CoreAllocation.count,ocard,roots,sum_const,card_univ,Fintype.card_coe,spec]
    decide
  obtain ⟨u,G,hG,hit⟩ := FourHeadWitness.exists_bad_scalar_set_of_values A (by omega) (by rw [count];simpa [pow_two] using fieldRoom)
  have mass := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ _ u G hit
  rwa [hG,count] at mass
/-- Numeric nonlinear populations from the weighted variance bound, with K=81/100. -/
theorem variance_numbers :
    ∀ b : Fin 2,
      let m : ℚ := 16
      let d : ℚ := 268435455
      let n : ℚ := 1073741824
      let t : ℚ := 626349396
      let K : ℚ := 81/100
      let v : ℚ := b.val+2
      let x := (2*v-2)*m-v*(v-1)+1
      let z := (2*v-2)*(2*t-1)-v*(v-1)*d+1
      let den := (5*K^4-4*K^5)*t-d
      let num := 2*K^5*v*(4*m*x*z+m*n+x*z)+(n-d)*(m+1)
      0<den ∧ (x+num/den)<(![27057,132663] : Fin 2 → ℚ) b := by
  intro b
  fin_cases b <;> norm_num

/-- A literal pair of split polynomials of degree d−1 and their difference
give the sufficient construction directly on the supplied evaluation domain. -/
theorem mass_of_split_polynomials {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (fieldRoom : 1073741826^2 < Fintype.card F)
    (P Q : F[X]) (dp : P.natDegree≤268435454) (dq : Q.natDegree≤268435454)
    (hp : (univ.filter fun x => P.eval (dom x)=0).card=268435454)
    (hq : (univ.filter fun x => Q.eval (dom x)=0).card=268435454)
    (hr : (univ.filter fun x => P.eval (dom x)=Q.eval (dom x)).card=268435454)
    (cop : ∀ x, P.eval (dom x)=0 → Q.eval (dom x)≠0) :
    (1073741826 : ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F)
      (ReedSolomon.code dom 268435456 : Set (I → F)) (447392428/1073741824) := by
  classical
  let raw (x : I) : Fin 4 := if P.eval (dom x)=0 then 2 else if Q.eval (dom x)=0 then 1
    else if P.eval (dom x)=Q.eval (dom x) then 0 else 3
  have tab (x : I) : (raw x=2 ↔ P.eval (dom x)=0) ∧ (raw x=1 ↔ Q.eval (dom x)=0) ∧
      (raw x=0 ↔ P.eval (dom x)=Q.eval (dom x)) := by
    by_cases p : P.eval (dom x)=0
    · simp [raw,p,cop x p,Ne.symm (cop x p)]
    by_cases q : Q.eval (dom x)=0
    · simp [raw,p,q]
    by_cases r : P.eval (dom x)=Q.eval (dom x) <;> simp [raw,p,q,r]
  have c₂ : (univ.filter fun x => raw x=2).card=268435454 := by simpa only [fun x => (tab x).1] using hp
  have c₁ : (univ.filter fun x => raw x=1).card=268435454 := by simpa only [fun x => (tab x).2.1] using hq
  have c₀ : (univ.filter fun x => raw x=0).card=268435454 := by simpa only [fun x => (tab x).2.2] using hr
  have total := sum_card_fiberwise_eq_card_filter (univ : Finset I) (univ : Finset (Fin 4)) raw
  simp [Fin.sum_univ_succ,hn] at total
  apply pencil_mass dom hn fieldRoom raw (![0,P,Q] : Fin 3 → F[X]) ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [dp,dq]
  · intro i; fin_cases i
    · exact c₀
    · exact c₁
    · exact c₂
    · change (univ.filter fun x => raw x=3).card=268435462
      change (univ.filter fun x => raw x=0).card + ((univ.filter fun x => raw x=1).card +
        ((univ.filter fun x => raw x=2).card + ((univ.filter fun x => raw x=3).card+0)))=1073741824 at total
      rw [c₀,c₁,c₂] at total
      omega
  · intro x i j
    by_cases p : P.eval (dom x)=0
    · have q := cop x p
      fin_cases i <;> fin_cases j <;> simp [coincide,raw,p,q,Ne.symm q]
    by_cases q : Q.eval (dom x)=0
    · fin_cases i <;> fin_cases j <;> simp [coincide,raw,p,q,Ne.symm p]
    by_cases r : P.eval (dom x)=Q.eval (dom x)
    · fin_cases i <;> fin_cases j <;> simp [coincide,raw,q,Ne.symm q,r]
    · fin_cases i <;> fin_cases j <;> simp [coincide,raw,p,q,Ne.symm p,Ne.symm q,r,Ne.symm r]

/-- A split pencil cannot be too close to three disjoint cosets when the
cleared numerators have degree below the coset order. The witness site is a
hole of the first coset, outside the other denominator and numerator roots. -/
theorem near_coset_impossible {K : Type*} [Field K] {k : ℕ} (a b c x : K)
    (P Q A B D E G H : K[X])
    (p : P*A=(Polynomial.X^k-C a)*E)
    (q : Q*B=(Polynomial.X^k-C b)*G)
    (r : (P-Q)*D=(Polynomial.X^k-C c)*H)
    (deg₁ : (E*B*D).natDegree<k) (deg₂ : (G*A*D).natDegree<k) (deg₃ : (H*A*B).natDegree<k)
    (zero : A.eval x=0) (hb : B.eval x≠0) (hd : D.eval x≠0) (he : E.eval x≠0) : False := by
  let U := E*B*D
  let V := G*A*D
  let W := H*A*B
  have eq : Polynomial.X^k*(U-V-W)=C a*U-C b*V-C c*W := by
    dsimp only [U,V,W]
    linear_combination -B*D*p + A*D*q + A*B*r
  have le₁ := (natDegree_C_mul_le a U).trans_lt deg₁
  have le₂ := (natDegree_C_mul_le b V).trans_lt deg₂
  have le₃ := (natDegree_C_mul_le c W).trans_lt deg₃
  have small : (C a*U-C b*V-C c*W).natDegree < k := by
    apply (natDegree_sub_le ..).trans_lt
    exact max_lt ((natDegree_sub_le ..).trans_lt (max_lt le₁ le₂)) le₃
  have van : U-V-W=0 := by
    by_contra non
    rw [← eq,natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) non,natDegree_X_pow] at small
    omega
  have atx := congrArg (Polynomial.eval x) van
  simp [U,V,W,zero,he,hb,hd] at atx

#print axioms near_coset_impossible
#print axioms variance_numbers
#print axioms mass_of_split_polynomials
#print axioms pencil_mass
#print axioms root_deficits
end ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitPencil
