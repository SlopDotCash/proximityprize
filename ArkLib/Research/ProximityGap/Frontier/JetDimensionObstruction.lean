/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation

/-! # An obstruction to changing the multiplicity in the jet dimension argument

If `t ≤ h*d`, every admissible monomial can be assigned a distinct jet equation
on `h²*d` sites. This includes every choice of multiplicity and of scalar/value
degree cutoffs. A particular received word can still create dependent equations.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.JetDimensionObstruction
open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- Division with remainder on the value and coordinate exponents embeds the
monomial indices into the available jet rows on `h*h*d` sites. -/
theorem card_monomials_le_rows (m v d t r h : ℕ) (hh : 0<h) (hd : 0<d) (ht : t ≤ h*d) :
    Fintype.card (Monomials m v d (r*t)) ≤ (h*(h*d))*Fintype.card (JetRows m r) := by
  let T := Fin h × Fin (h*d) × JetRows m r
  let assign (x : Monomials m v d (r*t)) : T := by
    let j := x.1.val
    let a := x.2.2.val
    have hw : a+j*d < r*t := Nat.lt_sub_iff_add_lt.mp x.2.2.isLt
    have hlow : (j/h)*(h*d) ≤ j*d := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right d (Nat.div_mul_le_self j h)
    have hs : a+(j/h)*(h*d)<r*(h*d) :=
      (Nat.add_le_add_left hlow _).trans_lt (hw.trans_le (Nat.mul_le_mul_left r ht))
    have hj : j/h<r := by
      by_contra! hn
      have := Nat.mul_le_mul_right (h*d) hn
      omega
    have ha : a/(h*d)<r-j/h := by
      apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hh hd)).mpr
      rw [Nat.sub_mul]
      omega
    have hi : x.2.1.val < m+1-j/h :=
      x.2.1.isLt.trans_le (Nat.sub_le_sub_left (Nat.div_le_self j h) _)
    exact (⟨j%h,Nat.mod_lt _ hh⟩,⟨a%(h*d),Nat.mod_lt _ (Nat.mul_pos hh hd)⟩,
      ⟨⟨j/h,hj⟩,⟨a/(h*d),ha⟩,⟨x.2.1.val,hi⟩⟩)
  have inj : Function.Injective assign := by
    rintro ⟨⟨j,hj⟩,⟨i,hi⟩,⟨a,ha⟩⟩ ⟨⟨j',hj'⟩,⟨i',hi'⟩,⟨a',ha'⟩⟩ he
    have hjm := congrArg (fun x : T => x.1.val) he
    have hjd := congrArg (fun x : T => x.2.2.1.val) he
    have ham := congrArg (fun x : T => x.2.1.val) he
    have had := congrArg (fun x : T => x.2.2.2.1.val) he
    have hei := congrArg (fun x : T => x.2.2.2.2.val) he
    change j%h=j'%h at hjm
    change j/h=j'/h at hjd
    change a%(h*d)=a'%(h*d) at ham
    change a/(h*d)=a'/(h*d) at had
    change i=i' at hei
    have ej : j=j' := by rw [← Nat.mod_add_div j h,hjm,hjd,Nat.mod_add_div]
    have ea : a=a' := by rw [← Nat.mod_add_div a (h*d),ham,had,Nat.mod_add_div]
    subst j'; subst i'; subst a'; rfl
  simpa only [T,Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc] using Fintype.card_le_of_injective assign inj

/-- For quarter rate, once the agreement is at most `2k−2`, no choice of these
monomials or jets gives a strict surplus by dimension counting. -/
theorem quarter_no_surplus (k t m v r : ℕ) (hk : 2 ≤ k) (ht : t ≤ 2*(k-1)) :
    Fintype.card (Monomials m v (k-1) (r*t)) ≤ 4*k*Fintype.card (JetRows m r) :=
  (card_monomials_le_rows m v (k-1) t r 2 (by decide) (by omega) ht).trans
    (Nat.mul_le_mul_right _ (by omega))

#print axioms card_monomials_le_rows
#print axioms quarter_no_surplus
end ArkLib.ProximityGap.Frontier.JetDimensionObstruction
