/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation

/-! # The Johnson obstruction to a positive dimension count

Prefix sums of the available coordinate exponents are majorized by prefix sums
of the jet costs when `t² ≤ n*d`. Summing prefixes incorporates the triangular
cutoff on scalar/value degree. This comparison is independent of multiplicity.
-/
set_option autoImplicit false
open Finset
namespace ArkLib.ProximityGap.Frontier.JohnsonJetDimension
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

private theorem triangle (c : ℕ) : 2*∑ j ∈ range c, (c-j) = c*(c+1) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.mul_add,ih]
    ring

private theorem prefix_linear (c r : ℕ) (h : c ≤ r) :
    c*r ≤ 2*∑ j ∈ range c, (r-j) := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h
  have he : ∑ j ∈ range c, (c+b-j) = (∑ j ∈ range c, (c-j))+c*b := by
    calc _ = ∑ j ∈ range c, ((c-j)+b) := by
            apply sum_congr rfl
            intro j hj; have := mem_range.mp hj; omega
         _ = _ := by simp [sum_add_distrib]
  rw [he]
  nlinarith [triangle c,Nat.zero_le (c*b)]

private theorem columns_head (r d e c : ℕ) (hc : c ≤ r) :
    ∑ j ∈ range c, (r*(d+e)-j*d) = (∑ j ∈ range c, (r-j))*d+c*(r*e) := by
  rw [Finset.sum_mul]
  calc _ = ∑ j ∈ range c, ((r-j)*d + r*e) := by
          apply sum_congr rfl
          intro j hj
          have hle := Nat.mul_le_mul_right d ((mem_range.mp hj).le.trans hc)
          rw [Nat.sub_mul,Nat.mul_add]; omega
       _ = _ := by simp [sum_add_distrib]

private theorem clipped_triangle (x d l : ℕ) :
    2*d*(∑ j ∈ range l, (x-(j+1)*d))+(x-l*d)^2 ≤ x^2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [sum_range_succ,Nat.mul_add]
    have hstep : 2*d*(x-(l+1)*d)+(x-(l+1)*d)^2 ≤ (x-l*d)^2 := by
      by_cases h : x ≤ (l+1)*d
      · simp [Nat.sub_eq_zero_of_le h]
      · have hg : x-l*d = x-(l+1)*d+d := by rw [Nat.add_mul] at *; omega
        rw [hg]; nlinarith
    omega

private theorem tail (x d l : ℕ) :
    2*d*(∑ j ∈ range l, (x-j*d)) ≤ 2*d*x+x^2 := by
  cases l with
  | zero => simp
  | succ l =>
    rw [sum_range_succ']
    simp only [zero_mul,Nat.sub_zero,Nat.mul_add]
    have := clipped_triangle x d l
    omega

private theorem prefix_bound (n d t r c : ℕ) (hd : 0<d) (hdt : d≤t) (hJ : t^2≤n*d) :
    ∑ j ∈ range c, (r*t-j*d) ≤ n*∑ j ∈ range c, (r-j) := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hdt
  have hn : d+2*e ≤ n := by
    by_contra! h
    have := Nat.mul_lt_mul_of_pos_right h hd
    nlinarith
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
  have he : e^2 ≤ b*d := by nlinarith
  by_cases h : c ≤ r
  · rw [columns_head r d e c h]
    have hp := Nat.mul_le_mul_right e (prefix_linear c r h)
    nlinarith [Nat.zero_le (b*∑ j ∈ range c, (r-j))]
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le (by omega : r ≤ c)
    rw [sum_range_add,sum_range_add,columns_head r d e r le_rfl]
    have hzero : (∑ j ∈ range l, (r-(r+j))) = 0 := by simp
    have hrest : ∑ j ∈ range l, (r*(d+e)-(r+j)*d) = ∑ j ∈ range l, (r*e-j*d) := by
      apply sum_congr rfl
      intro j _
      rw [Nat.add_mul,Nat.mul_add]; omega
    rw [hzero,Nat.add_zero,hrest]
    have he' := Nat.mul_le_mul_left (r*(r+1)) he
    have ht := tail (r*e) d l
    have htr := triangle r
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<2*d)
    calc _ ≤ 2*d*((∑ j ∈ range r, (r-j))*d+r*(r*e))+ (2*d*(r*e)+(r*e)^2) := by
                rw [Nat.mul_add]; omega
         _ ≤ _ := by
           rw [show 2*d*((d+2*e+b)*∑ j ∈ range r, (r-j)) = d*(d+2*e+b)*(2*∑ j ∈ range r, (r-j)) by ring,htr]
           rw [show 2*d*((∑ j ∈ range r, (r-j))*d+r*(r*e)) = d*d*(2*∑ j ∈ range r, (r-j))+2*d*(r*(r*e)) by ring,htr]
           nlinarith

private def mass (m : ℕ) (f : ℕ → ℕ) := ∑ j ∈ range m, (m-j)*f j

private theorem mass_succ (m : ℕ) (f : ℕ → ℕ) :
    mass (m+1) f = mass m f + ∑ j ∈ range (m+1), f j := by
  unfold mass
  rw [sum_range_succ,sum_range_succ (f:=f)]
  simp only [Nat.add_sub_cancel_left,one_mul]
  have he : ∑ j ∈ range m, (m+1-j)*f j = ∑ j ∈ range m, ((m-j)*f j+f j) := by
    apply sum_congr rfl
    intro j hj
    have h := mem_range.mp hj
    rw [show m+1-j = (m-j)+1 by omega,Nat.add_mul,one_mul]
  rw [he,sum_add_distrib,Nat.add_assoc]

private theorem finite_support (c b : ℕ) (f : ℕ → ℕ) (hb : ∀ j, b ≤ j → f j=0) :
    ∑ j ∈ range c, f j ≤ ∑ j ∈ range b, f j := by
  by_cases h : c ≤ b
  · exact sum_le_sum_of_subset_of_nonneg (range_mono h) (by intros; omega)
  · apply le_of_eq
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    exact hb j (by simpa using hj)

/-- In the list-decoding regime `d ≤ t`, a strict excess of columns over the
received-line jet equations requires `n*d < t²`. This implication holds for every
multiplicity and every set of degree cutoffs in the triangular monomial family. -/
theorem card_monomials_le_rows (n d t r m v : ℕ) (hd : 0<d) (hdt : d≤t) (hJ : t^2≤n*d) :
    Fintype.card (Monomials m v d (r*t)) ≤ n*Fintype.card (JetRows m r) := by
  let f := fun j => r*t-j*d
  let g := fun j => r-j
  have hmass (b : ℕ) : mass b f ≤ n*mass b g := by
    induction b with
    | zero => simp [mass]
    | succ b ih =>
      rw [mass_succ,mass_succ,Nat.mul_add]
      exact Nat.add_le_add ih (prefix_bound n d t r (b+1) hd hdt hJ)
  have hcol : Fintype.card (Monomials m v d (r*t)) ≤ mass (m+1) f := by
    simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => (m+1-j)*(r*t-j*d))]
    exact finite_support _ _ _ (fun j hj => by simp [Nat.sub_eq_zero_of_le hj])
  have hrow : mass (m+1) g ≤ Fintype.card (JetRows m r) := by
    simp only [JetRows,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => (r-j)*(m+1-j))]
    calc mass (m+1) g ≤ ∑ j ∈ range r, (m+1-j)*(r-j) :=
           finite_support _ _ _ (fun j hj => by simp [g,Nat.sub_eq_zero_of_le hj])
         _ = _ := by apply sum_congr rfl; intros; rw [Nat.mul_comm]
  exact hcol.trans ((hmass _).trans (Nat.mul_le_mul_left n hrow))

/-- Every integer agreement strictly above Johnson gives a strict dimension surplus at
some explicit multiplicity. Taking a multiple of `d` makes the coordinate triangle
end exactly at a lattice point. -/
theorem exists_surplus (n d t : ℕ) (hd : 0<d) (hJ : n*d<t^2) :
    let r := d*(n+1)
    let v := (n+1)*t
    ∃ m, r ≤ m ∧ v ≤ m ∧ 2 ≤ m ∧
      n*Fintype.card (JetRows m r) < Fintype.card (Monomials m v d (r*t)) := by
  let L := n+1
  let r := d*L
  let v := L*t
  let A := (∑ j ∈ range v, (v-j))*d
  let B := n*∑ j ∈ range r, (r-j)
  let m := v*A+r+v+2
  have hL : 0<L := Nat.succ_pos _
  have hlarge : L*(n*d)+n < L*t^2+t := by
    have := Nat.mul_le_mul_left L (show n*d+1≤t^2 by omega)
    dsimp [L] at *; nlinarith
  have hAB : B<A := by
    have h₁ := Nat.mul_lt_mul_of_pos_left hlarge (Nat.mul_pos hd hL)
    have h₂ : 2*A=v*(v+1)*d := by dsimp [A]; rw [← Nat.mul_assoc,triangle]
    have h₃ : 2*B=n*(r*(r+1)) := by dsimp [B]; rw [Nat.mul_left_comm,triangle]
    dsimp [r,v] at h₂ h₃
    nlinarith only [h₁,h₂,h₃]
  have hcol : (m+1-v)*A ≤ Fintype.card (Monomials m v d (r*t)) := by
    simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => (m+1-j)*(r*t-j*d))]
    have he : r*t=v*d := by dsimp [r,v]; ring
    have hsum : ∑ j ∈ range (v+1), (r*t-j*d) = A := by
      rw [sum_range_succ,he,Nat.sub_self,Nat.add_zero]
      simp only [← Nat.sub_mul,← sum_mul,A]
    rw [← hsum,Finset.mul_sum]
    apply sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (by have := mem_range.mp hj; omega) _)
  have hrow : n*Fintype.card (JetRows m r) ≤ (m+1)*B := by
    simp only [JetRows,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => (r-j)*(m+1-j))]
    calc _ ≤ n*∑ j ∈ range r, (r-j)*(m+1) := by
              apply Nat.mul_le_mul_left; exact sum_le_sum fun _ _ => Nat.mul_le_mul_left _ (Nat.sub_le ..)
         _ = _ := by rw [← sum_mul]; dsimp [B]; ring
  have hgap : (m+1)*B < (m+1-v)*A := by
    have h₁ := Nat.mul_le_mul_left (m+1) (show B+1≤A by omega)
    have hv : v*A<m+1 := by dsimp [m]; omega
    have h₂ := congrArg (fun q : ℕ => q*A) (Nat.sub_add_cancel (by dsimp [m]; omega : v≤m+1))
    nlinarith only [h₁,hv,h₂]
  exact ⟨m,by dsimp [m,r,L]; omega,by dsimp [m,v,L]; omega,by dsimp [m]; omega,
    hrow.trans_lt (hgap.trans_le hcol)⟩

/-- Optimizing over all multiplicities and scalar/value degrees recovers the strict
Johnson threshold, with no asymptotic qualification. -/
theorem surplus_iff (n d t : ℕ) (hd : 0<d) (hdt : d≤t) :
    (∃ r m v, n*Fintype.card (JetRows m r) < Fintype.card (Monomials m v d (r*t))) ↔ n*d<t^2 := by
  constructor
  · rintro ⟨r,m,v,h⟩
    by_contra! hJ
    exact h.not_ge (card_monomials_le_rows n d t r m v hd hdt hJ)
  · intro hJ
    obtain ⟨m,_,_,_,h⟩ := exists_surplus n d t hd hJ
    exact ⟨_,m,_,h⟩

#print axioms card_monomials_le_rows
#print axioms surplus_iff
end ArkLib.ProximityGap.Frontier.JohnsonJetDimension
