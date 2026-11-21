/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusSeamCoordinateSupply

/-! # A finite two-thirds exponent bound for fractional linear subgroup intersections -/

namespace ProximityGap.MobiusSubgroupBound
open Finset

variable {F : Type*} [Field F]

/-- Rectangular choices of source and target powers for the two subgroup conditions.
The degree limit depends on the characteristic, independently of the field cardinality. -/
theorem rectangular {p N M A B C D : ℕ} [CharP F p] (hp : p.Prime) (hA : 0<A) (hC : 0<C)
    (hAN : A≤N) (hsize : A*C≤M) (hchar : A-1+N*(C-1)<p) (hD : D≤p)
    (hgap : D*(A+2*(D-1))<B*(A*C)) {a b K : F} (ha : a≠0) (hab : a≠b)
    (S : Finset F) (hreg : ∀ x ∈ S, x≠0 ∧ x≠a ∧ x≠b)
    (hpow : ∀ x ∈ S, x^N=1) (hratio : ∀ x ∈ S, (x-a)^M=K*(x-b)^M) :
    D*S.card ≤ A-1+N*(C-1)+M*(B-1) := by
  let d (j : Fin (A*C)) := j.val % A
  let e (j : Fin (A*C)) := d j + N*(j.val/A)
  have hd (j : Fin (A*C)) : d j < A := Nat.mod_lt _ hA
  have he (j : Fin (A*C)) : e j ≤ A-1+N*(C-1) := by
    have hq : j.val/A<C := (Nat.div_lt_iff_lt_mul hA).mpr (by simpa [Nat.mul_comm] using j.isLt)
    apply Nat.add_le_add (by have := hd j; omega) (Nat.mul_le_mul_left _ (by omega))
  have hinj : Function.Injective e := by
    intro i j h
    have hm := congrArg (· % N) h
    simp only [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ((hd _).trans_le hAN)] at hm
    have hout : N*(i.val/A)=N*(j.val/A) := Nat.add_left_cancel (show d i + _ = d i + _ by simpa [e,hm] using h)
    have hq := Nat.eq_of_mul_eq_mul_left (hA.trans_le hAN) hout
    apply Fin.ext
    calc i.val = d i + A*(i.val/A) := (Nat.mod_add_div ..).symm
         _ = d j + A*(j.val/A) := by rw [hm,hq]
         _ = j.val := Nat.mod_add_div ..
  have hv : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact hinj (CharP.natCast_injOn_Iio F p ((he i).trans_lt hchar) ((he j).trans_lt hchar) hij)
  have hf : IsUnit (((D-1).factorial : ℕ) : F) := by
    rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff F p]
    intro hh
    have := (Nat.Prime.dvd_factorial hp).mp hh
    have := hp.pos
    omega
  exact MobiusStepanov.mobius_count ha hab hv hsize he hA hd hgap hf S hreg
    (fun x hx j => by simp [e,pow_add,pow_mul,hpow x hx]) hratio

/-- The integral choice of powers giving the two-thirds bound for any subgroup order.
Taking the largest u with 2u³ ≤ N gives an explicit bound asymptotic to
3·2^(1/3)·N^(2/3) whenever the indicated characteristic condition holds. -/
theorem cubic_scale {p N u : ℕ} [CharP F p] (hp : p.Prime) (hu : 0<u)
    (hn : 2*u^3≤N) (hchar : 2*u^2-1+N*(u-1)<p) {a b K : F} (ha : a≠0) (hab : a≠b)
    (S : Finset F) (hreg : ∀ x ∈ S, x≠0 ∧ x≠a ∧ x≠b)
    (hpow : ∀ x ∈ S, x^N=1) (hratio : ∀ x ∈ S, (x-a)^N=K*(x-b)^N) :
    u^2*S.card ≤ 2*u^2-1+N*(u-1)+N*(2*u-1) := by
  have hmul : 2*u^2*u = 2*u^3 := by ring
  have haN : 2*u^2 ≤ N := (Nat.le_mul_of_pos_right _ hu).trans (hmul ▸ hn)
  apply rectangular hp (by positivity) hu haN (hmul ▸ hn) hchar (by omega) _ ha hab S hreg hpow hratio
  have hpos : 0<u^2 := by positivity
  have heq : u^2 * (2*u^2+2*(u^2-1)) + 2*u^2 = (2*u)*(2*u^2*u) := by
    have hsub : u^2-1+1=u^2 := by omega
    nlinarith only [congrArg (fun t : ℕ => 2*u^2*t) hsub]
  omega

/-- Optimized integer cutoffs at the length specified in the prize. -/
theorem production {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^40<p) {a b K : F}
    (ha : a≠0) (hab : a≠b) (S : Finset F) (hreg : ∀ x ∈ S, x≠0 ∧ x≠a ∧ x≠b)
    (hpow : ∀ x ∈ S, x^(2^30 : ℕ)=1)
    (hratio : ∀ x ∈ S, (x-a)^(2^30 : ℕ)=K*(x-b)^(2^30 : ℕ)) :
    S.card ≤ 3960117 := by
  have h := rectangular (A:=1322342) (B:=1621) (C:=812) (D:=659139) hp (by decide) (by decide)
    (by decide : 1322342≤2^30) (by decide : 1322342*812≤2^30) (by omega) (by omega)
    (by decide) ha hab S hreg hpow hratio
  omega

/-- A fractional-linear graph between two normalized subgroups with distinct orders.
The numerator's leading and constant coefficients and the denominator's leading
coefficient are nonzero. Scaling either coset representative preserves these hypotheses. -/
theorem rectangular_graph {p N M A B C D : ℕ} [CharP F p] (hp : p.Prime)
    (hN : 0<N) (hM : 0<M) (hA : 0<A) (hC : 0<C)
    (hAN : A≤N) (hsize : A*C≤M) (hchar : A-1+N*(C-1)<p) (hD : D≤p)
    (hgap : D*(A+2*(D-1))<B*(A*C))
    {I : Type*} [Fintype I] (x y : I → F) (hi : Function.Injective x)
    (hx : ∀ i, (x i)^N=1) (hy : ∀ i, (y i)^M=1)
    {a b c d : F} (ha : a≠0) (hb : b≠0) (hc : c≠0) (hdet : a*d-b*c≠0)
    (hxy : ∀ i, a*x i+b=y i*(c*x i+d)) :
    D*Fintype.card I ≤ A-1+N*(C-1)+M*(B-1) := by
  classical
  let zero := -b/a
  let pole := -d/c
  have hzero : zero ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hAB : zero ≠ pole := by
    intro hh
    apply hdet
    have h := (div_eq_div_iff ha hc).mp hh
    linear_combination h
  have he (i : I) : x i-zero = (c/a)*y i*(x i-pole) := by
    dsimp [zero,pole]
    field_simp
    linear_combination hxy i
  have hB (i : I) : x i ≠ pole := by
    intro hh
    apply hAB
    have hh' := he i
    rw [hh,sub_self,mul_zero] at hh'
    exact (sub_eq_zero.mp hh').symm
  have hA' (i : I) : x i ≠ zero := by
    apply sub_ne_zero.mp
    rw [he]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero hc ha) (by intro hh; simpa [hh, Nat.ne_of_gt hM] using hy i))
      (sub_ne_zero.mpr (hB i))
  have hh := rectangular hp hA hC hAN hsize hchar hD hgap hzero hAB (univ.image x) (by
    intro z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    exact ⟨by intro hh; simpa [hh, Nat.ne_of_gt hN] using hx i, hA' i,hB i⟩) (by simpa using hx)
    (K:=(c/a)^M) (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      rw [he i, mul_pow,mul_pow,hy i,mul_one])
  simpa only [card_image_of_injective _ hi, card_univ] using hh

private theorem graph_direct {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^40<p)
    {I : Type*} [Fintype I] (x y : I → F) (hi : Function.Injective x)
    (hx : ∀ i, (x i)^(2^30 : ℕ)=1) (hy : ∀ i, (y i)^(2^30 : ℕ)=1)
    {a b c d : F} (ha : a≠0) (hb : b≠0) (hc : c≠0) (hdet : a*d-b*c≠0)
    (hxy : ∀ i, a*x i+b=y i*(c*x i+d)) : Fintype.card I ≤ 3960117 := by
  have h := rectangular_graph (A:=1322342) (B:=1621) (C:=812) (D:=659139) hp
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    (by omega) (by decide) x y hi hx hy ha hb hc hdet hxy
  omega

/-- Every nonsingular fractional linear map other than a scaling or a scaled
reciprocal sends at most 3,960,117 members of the production subgroup back to it.
The graph formulation includes affine maps and maps whose zero is at infinity. -/
theorem production_graph {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^40<p)
    {I : Type*} [Fintype I] (x y : I → F) (hi : Function.Injective x)
    (hx : ∀ i, (x i)^(2^30 : ℕ)=1) (hy : ∀ i, (y i)^(2^30 : ℕ)=1)
    {a b c d : F} (hdet : a*d-b*c≠0) (hdiag : b≠0 ∨ c≠0) (hanti : a≠0 ∨ d≠0)
    (hxy : ∀ i, a*x i+b=y i*(c*x i+d)) : Fintype.card I ≤ 3960117 := by
  have hx0 (i : I) : x i≠0 := by intro h; simpa [h] using hx i
  have hy0 (i : I) : y i≠0 := by intro h; simpa [h] using hy i
  have hxi (i : I) : (x i)⁻¹ ^ (2^30 : ℕ)=1 := by rw [inv_pow,hx,inv_one]
  have hyi (i : I) : (y i)⁻¹ ^ (2^30 : ℕ)=1 := by rw [inv_pow,hy,inv_one]
  have hinv : Function.Injective (fun i => (x i)⁻¹) := fun i j hh => hi (inv_inj.mp hh)
  by_cases ha : a=0
  · subst a
    have hd := hanti.resolve_left (by simp)
    have hbc : b≠0 ∧ c≠0 := by simpa [mul_ne_zero_iff] using hdet
    apply graph_direct hp hbig _ _ hinv hxi hyi hd hbc.2 hbc.1 (show d*0-c*b≠0 by simpa [mul_comm] using hdet)
    intro i
    field_simp [hx0 i, hy0 i]
    linear_combination -(hxy i)
  by_cases hb : b=0
  · subst b
    have hc := hdiag.resolve_left (by simp)
    have hd : d≠0 := by intro h; simp [h] at hdet
    apply graph_direct hp hbig _ _ hi hx hyi hc hd ha
      (show c*0-d*a≠0 by simpa [mul_comm] using hdet)
    intro i
    field_simp [hy0 i]
    linear_combination -(hxy i)
  by_cases hc : c=0
  · subst c
    have hd : d≠0 := by intro h; simp [h] at hdet
    apply graph_direct hp hbig _ _ hinv hxi hy hb ha hd
      (show b*0-a*d≠0 by simpa using hdet)
    intro i
    field_simp [hx0 i]
    linear_combination hxy i
  exact graph_direct hp hbig x y hi hx hy ha hb hc hdet hxy

open MobiusSeamCoordinateSupply in
/-- The literal count on the finite subgroup, including maps with a zero matrix entry. -/
theorem graph_card {p : ℕ} [CharP F p] [Fintype F] [DecidableEq F] (hp : p.Prime)
    (hbig : 2^40<p) (u : Mobius F) (hdet : u.det≠0)
    (hdiag : u.b≠0 ∨ u.c≠0) (hanti : u.a≠0 ∨ u.d≠0) :
    (univ.filter fun x : F => x^(2^30 : ℕ)=1 ∧ (u.value x)^(2^30 : ℕ)=1).card ≤ 3960117 := by
  classical
  let S := univ.filter fun x : F => x^(2^30 : ℕ)=1 ∧ (u.value x)^(2^30 : ℕ)=1
  have h := production_graph hp hbig (fun i : S => i.val) (fun i : S => u.value i.val)
    Subtype.val_injective (fun i => (mem_filter.mp i.property).2.1)
    (fun i => (mem_filter.mp i.property).2.2) hdet hdiag hanti (by
      intro i
      have hd : u.den i.val ≠ 0 := by
        intro hh
        have hpw := (mem_filter.mp i.property).2.2
        simp [Mobius.value,hh] at hpw
      exact (div_mul_cancel₀ (u.num i.val) hd).symm)
  simpa only [Fintype.card_coe] using h

open MobiusSeamCoordinateSupply in
/-- The production subgroup supplies more than a billion sites separated across all
three directions. Six exceptional coordinates and labels may be reserved in advance. -/
theorem separated_sites {p : ℕ} [CharP F p] [Fintype F] [DecidableEq F] (hp : p.Prime)
    (hbig : 2^40<p) (m : Fin 3 → Mobius F) (H Y T : Finset F) (hH : H.card=2^30)
    (hpow : ∀ x ∈ H, x^(2^30 : ℕ)=1) (hY : Y.card ≤ 6) (hT : T.card ≤ 6)
    (hdet : ∀ i, (m i).det≠0)
    (hrel : ∀ i j, i≠j → let u := (m i).relative (m j); (u.b≠0 ∨ u.c≠0) ∧ (u.a≠0 ∨ u.d≠0)) :
    1049981095 ≤ (ordinary m H Y T).card := by
  have h := ordinary_card_of_pair_cap (L:=3960117) m H Y T hpow hY hT hdet (by
    intro i j hij
    apply graph_card hp hbig _ _ (hrel i j hij).1 (hrel i j hij).2
    rw [Mobius.det_relative]
    exact mul_ne_zero (hdet _) (hdet _))
  rwa [hH] at h

#print axioms cubic_scale
#print axioms production_graph
#print axioms separated_sites
end ProximityGap.MobiusSubgroupBound
