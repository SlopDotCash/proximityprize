/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarSparseSpecialization
import ArkLib.Research.ProximityGap.Frontier.ApolarSparseRankBound
import ArkLib.Research.ProximityGap.Frontier.ApolarFixedPencil

/-! # Counting sparse fibers with moving evaluation sites -/

open Finset Polynomial Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarFixedFactors
open ProximityGap.ApolarSparseSpecialization
open ArkLib.ProximityGap.Frontier.ApolarSparseRankBound

namespace ProximityGap.ApolarMovingCount

variable {K : Type*} [Field K] [Infinite K]

/-- Eliminate the positive trimmed rank from the two degree estimates. -/
theorem cancel_rank {M D R N l : ℕ} (hR : 0 < R) (h₁ : D*l ≤ R)
    (h₂ : M*R ≤ N*l+R) : (M-1)*D ≤ N := by
  by_cases hm : M=0
  · simp [hm]
  have hM : M-1+1=M := by omega
  have hh : (M-1)*R ≤ N*l := by
    rw [←hM,add_mul,one_mul] at h₂
    omega
  have h := (Nat.mul_le_mul_right D hh).trans (show N*l*D ≤ N*R by
    simpa only [Nat.mul_assoc,Nat.mul_comm l D] using Nat.mul_le_mul_left N h₁)
  apply Nat.le_of_mul_le_mul_right _ hR
  simpa only [Nat.mul_right_comm (M-1) D R] using h

/-- For a minimal locator pencil with genuinely moving support, both the fixed
coordinate factors and the parameter degree disappear from the final bound. -/
theorem count_moving [DecidableEq K] (m : ℕ → K[X]) {d s : ℕ} (hs : s ≤ d)
    (hlen : 2*s ≤ d+2) (hm : ∀ j ≤ d, (m j).natDegree ≤ 1)
    (v : Fin (s+1) → K[X]) (hv : v ≠ 0) (hk : catalecticant m d s *ᵥ v = 0)
    (hmin : ∀ b < s, ∀ a, catalecticant m d b *ᵥ a = 0 → a = 0)
    (H S : Finset K) (hsparse : ∀ t ∈ S, ∃ E ⊆ H, E.card ≤ d-s+1 ∧
      ∃ w : K → K, ∀ j ≤ d, (m j).eval t = ∑ y ∈ E, w y*y^j)
    (x z : K) (hxz : x ≠ z) (hz : z ∉ H)
    (ht : ((family v).map (evalRingHom z)).natDegree = (family v).natDegree)
    (hc : IsCoprime ((family v).map (evalRingHom x)) ((family v).map (evalRingHom z)))
    (hmove : (fixed H (form v)).card < s) :
    let c := (fixed H (form v)).card
    (S.card-1)*(d+c+2-2*s) ≤ H.card-c := by
  classical
  let A := fixed H (form v)
  let G := Lagrange.nodal A id
  let c := A.card
  let r := s-c-1
  let D := d-c
  let L := trim (functional m) G
  let μ (j : ℕ) := L (X^j)
  let ℓ := (family v).natDegree
  have hcs : c+r+1=s := by dsimp [c,A,r]; omega
  have hcd : c+D=d := by dsimp [D]; omega
  have hg : G ≠ 0 := Lagrange.nodal_ne_zero
  have hgd : G.natDegree=c := Lagrange.natDegree_nodal
  have hsub : A ⊆ H := fun _ h => (mem_fixed.mp h).1
  have hnon : form v ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun p : K[X][X] => p.coeff i.val) h
  obtain ⟨q,hq,_,hqd,_⟩ := split_fixed H (form v) hnon
  change form v=G.map C*q at hq
  change c+q.natDegree=(form v).natDegree at hqd
  have hqdeg : q.natDegree ≤ r+1 := by have hh := form_degree v; omega
  have hold : ApolarThrough (functional m) (form v) (d-s) := by
    apply (equations_iff_apolar m v).mp
    intro j hj
    exact congrFun hk ⟨j,by omega⟩
  have hprev (p : K[X][X]) (hp : p.natDegree ≤ c+r)
      (ha : ApolarThrough (functional m) p (D-r)) : p=0 := by
    let b (i : Fin ((c+r)+1)) := p.coeff i.val
    have hpb : form b=p := form_coeff p hp
    have he := (equations_iff_apolar m b (s:=d-(c+r))).mpr (by
      rw [hpb,show d-(c+r)=D-r by omega]; exact ha)
    have hb := hmin (c+r) (by omega) b (funext fun i => he i.val (by have := i.isLt; omega))
    rw [← hpb,hb]
    simp [form]
  have hprev' : ∀ p : K[X][X], p.natDegree ≤ G.natDegree+r →
      ApolarThrough (functional m) p (D-r) → p=0 := by simpa only [hgd] using hprev
  have hμ : functional μ=L := functional_moments _
  have htrim (j : ℕ) (hj : j ≤ D) : (μ j).natDegree ≤ 1 :=
    trim_affine m hm G j (by rw [hgd]; omega)
  have hker (a : Fin (r+1) → K[X]) (ha : catalecticant μ D r *ᵥ a=0) : a=0 := by
    have he : ApolarThrough (functional μ) (form a) (D-r) := by
      apply (equations_iff_apolar μ a).mp
      intro j hj
      exact congrFun ha ⟨j,by omega⟩
    rw [hμ] at he
    have hform := trim_minimal (functional m) G hg hprev' _ (form_degree _) he
    funext i
    simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun p : K[X][X] => p.coeff i.val) hform
  have hdeg : (D-2*r)*ℓ ≤ r+1 := by
    have hcop : IsCoprime ((G.map C*q).eval (C x)) ((G.map C*q).eval (C z)) := by
      simpa only [←hq,eval_form] using hc
    have hz' : G.eval z ≠ 0 := Lagrange.eval_nodal_not_at_node
      (fun y hy h => hz (h ▸ hsub hy))
    have hh := trimmed_chart_degree m G hg q (d:=D) (r:=r) (by omega) (by omega) hqdeg
      (by simpa only [hgd,hcd] using hm) (by simpa only [←hq,show D-(r+1)=d-s by omega] using hold)
      hprev' x z hxz hz' hcop
    simpa only [←hq,eval_form,ht,ℓ] using hh
  have hs' (t : K) (ht : t ∈ S) : ∃ U ⊆ H \ A, ∃ w : K → K,
      (∀ j ≤ D, (μ j).eval t=∑ y ∈ U,w y*y^j) ∧
      ∀ y ∈ U, ((form v).eval (C y)).eval t=0 := by
    obtain ⟨E,hE,hn,w,hw⟩ := hsparse t ht
    obtain ⟨U,hU,b,hmom,hsite⟩ := trimmed_atoms m hs v hk H A E t w hE hn hw
    exact ⟨U,hU,b,fun j hj => hmom j (by change c+j ≤ d; omega),hsite⟩
  choose! U hU w hmoment hsite using hs'
  have hsitepoly (y : K) (hy : y ∈ H \ A) :
      (form v).eval (C y) ≠ 0 ∧ ((form v).eval (C y)).natDegree ≤ ℓ := by
    refine ⟨fun h => (mem_sdiff.mp hy).2 (mem_fixed.mpr ⟨(mem_sdiff.mp hy).1,h⟩),?_⟩
    rw [eval_form]
    exact natDegree_map_le
  have hbound := count_sparse_fibers μ D r (by omega) htrim hker (H \ A) S U w hU hmoment
    (fun y => (form v).eval (C y)) ℓ hsitepoly hsite
  have hx := cancel_rank (Nat.zero_lt_succ r) hdeg hbound
  rwa [card_sdiff_of_subset hsub,show D-2*r=d+c+2-2*s by omega] at hx

open Code
open scoped NNReal
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.ApolarFixedPencil

/-- Unconditional incidence and nullity bound for the bad scalar family of
a Reed–Solomon pair at or below the half-distance range. -/
theorem count_mca_family {F L ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Field L] [IsAlgClosed L] [Infinite L] [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (φ : F →+* L) {dom : ι ↪ F} {k e d : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}
    (fam : BadScalarRichPointFamily dom k δ u) (bad : Finset F) (hsub : bad ⊆ fam.G)
    (hed : e ≤ d) (hlen : 2*e ≤ d+1) (hk : 1 ≤ k) (hd : k+d < Fintype.card ι)
    (he : Fintype.card ι - e ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) :
    bad.card ≤ e+1 ∨ (bad.card-1)*(d+2-2*e) ≤ Fintype.card ι := by
  classical
  by_cases hsmall : bad.card ≤ e+1
  · exact Or.inl hsmall
  have hlarge : e+1 < bad.card := by omega
  let ψ : F ↪ L := ⟨φ,φ.injective⟩
  let H₀ := (univ : Finset ι).map dom
  let H := H₀.map ψ
  let S := bad.map ψ
  let m := ApolarHankelMinors.moment H₀ (ApolarMcaSyndrome.coordinateRow dom (u 0))
    (ApolarMcaSyndrome.coordinateRow dom (u 1))
  let μ (j : ℕ) := (m j).map φ
  have hbad (t : F) (ht : t ∈ bad) := (fam.mem_G_iff t).mp (hsub ht)
  obtain ⟨s,hse,hmin,w,hw,hker,_,x,_,z,hz,hxz,_,ht,hcop⟩ :=
    minimal_chart_of_mca_events φ dom u bad hlarge hed hk hd he hbad H
  change catalecticant μ d s *ᵥ w=0 at hker
  let A := fixed H (form w)
  by_cases hmoving : A.card < s
  · right
    have hsp (t : L) (htt : t ∈ S) : ∃ E ⊆ H, E.card ≤ d-s+1 ∧
        ∃ a : L → L, ∀ j ≤ d, (μ j).eval t=∑ y ∈ E, a y*y^j := by
      obtain ⟨E,hE,hn,a,ha⟩ := extended_mca_atoms φ dom u bad hk hd he hbad t htt
      exact ⟨E,hE,by omega,a,ha⟩
    have hdeg (j : ℕ) (_ : j ≤ d) : (μ j).natDegree ≤ 1 := by
      dsimp only [μ,m,ApolarHankelMinors.moment]
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C]
      compute_degree
    have hcount := count_moving μ (d:=d) (s:=s) (by omega) (by omega) hdeg
      w hw hker hmin H S hsp x z hxz hz ht hcop hmoving
    change (S.card-1)*(d+A.card+2-2*s) ≤ H.card-A.card at hcount
    have h₁ : bad.card = S.card := by simp [S]
    have h₂ : H.card = Fintype.card ι := by simp [H,H₀]
    rw [h₁,←h₂]
    exact (Nat.mul_le_mul_left (S.card-1) (by omega : d+2-2*e ≤ d+A.card+2-2*s)).trans
      (hcount.trans (Nat.sub_le _ _))
  · left
    have hnon : form w ≠ 0 := by
      intro h
      apply hw
      funext i
      simpa only [coeff_form,coeff_zero,Pi.zero_apply] using congrArg (fun p : L[X][X] => p.coeff i.val) h
    obtain ⟨q,hq,hqn,hqd,_⟩ := split_fixed H (form w) hnon
    change A.card+q.natDegree=(form w).natDegree at hqd
    have hsf := form_degree w
    have h₁ : q.natDegree=0 := by omega
    have h₂ : A.card=s := by omega
    let G := Lagrange.nodal A id
    have hgd : G.natDegree=s := Lagrange.natDegree_nodal.trans h₂
    have hapos : ApolarThrough (functional μ) (form w) (d-s) := by
      apply (equations_iff_apolar μ w).mp
      intro j hj
      exact congrFun hker ⟨j,by omega⟩
    change form w=G.map C*q at hq
    rw [hq] at hapos
    have hh := count_le_of_constant_quotient φ fam bad hsub (by omega)
      G Lagrange.nodal_ne_zero q hqn h₁ (d-s) e hk (by omega) he (by omega) hapos
    omega

#print axioms count_mca_family
#print axioms count_moving

end ProximityGap.ApolarMovingCount
