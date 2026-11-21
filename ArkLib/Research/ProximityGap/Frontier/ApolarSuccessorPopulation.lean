/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA
import ArkLib.Research.ProximityGap.Frontier.ApolarSuccessorDefect

/-! # How many genuinely uncovered fibers a successor-step failure requires -/

open Finset Polynomial Code
open scoped NNReal
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarMcaSyndrome ProximityGap.ApolarSuccessorDefect
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

namespace ProximityGap.ApolarSuccessorPopulation

private theorem rowWeight_nonzero {K : Type*} [Field K] (H : Finset K) (w : K → K)
    (x : K) (hw : w x ≠ 0) : rowWeight H w x ≠ 0 := by
  classical
  apply div_ne_zero hw
  exact prod_ne_zero_iff.mpr fun z hz => sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {u : WordStack F (Fin 2) ι}

/-- Universal numerator at the unique radius of the production-length rate-half code. -/
theorem boundary_count {δ : ℝ≥0} (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card ι=1073741824) (hc : 805306368 ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) :
    fam.G.card ≤ 805306371 := by
  exact _root_.ArkLib.ProximityGap.Frontier.SharpApolarMCA.family_bound
    (e:=268435456) (d:=536870911) fam fam.G Subset.rfl (by decide) (by decide) (by decide)
    (by omega) (by omega) (by omega)

omit [Fintype F] [Nonempty ι] [DecidableEq ι] in
/-- Every newly bad scalar at the successor has exactly h+1 true errors for the
selected polynomial. This counts the full agreement set, not a discarded subset. -/
theorem fresh_exact {δ₀ δ₁ : ℝ≥0} {k a : ℕ}
    (lo : BadScalarRichPointFamily dom k δ₀ u) (hi : BadScalarRichPointFamily dom k δ₁ u)
    (hlo : ⌈(1-δ₀)*(Fintype.card ι : ℝ≥0)⌉₊=a+1)
    (hhi : ⌈(1-δ₁)*(Fintype.card ι : ℝ≥0)⌉₊=a)
    {t : F} (ht : t ∈ hi.G \ lo.G) :
    (fullAgreement dom (u 0) (u 1) t (hi.q t)).card=a := by
  classical
  let S := fullAgreement dom (u 0) (u 1) t (hi.q t)
  have ht₁ := (mem_sdiff.mp ht).1
  have ht₀ := (mem_sdiff.mp ht).2
  have hge := hi.threshold_le t ht₁
  rw [hhi] at hge
  apply le_antisymm _ hge
  by_contra! hh
  change a < S.card at hh
  apply ht₀
  apply (lo.mem_G_iff t).mpr
  refine ⟨S,Nat.ceil_le.mp (by rw [hlo];omega),⟨fun i => (hi.q t).eval (dom i),?_,?_⟩,hi.noJoint t ht₁⟩
  · exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (hi.q t) (hi.degree_lt t ht₁) fun _ => rfl
  · intro i hi'
    exact (mem_filter.mp hi').2

omit [Fintype F] [Nonempty ι] in
/-- A new scalar's true errors all miss every nonzero degree-at-most-h
specialized locator apolar through h−1, even if its specialized degree drops. -/
theorem fresh_misses {δ₀ δ₁ : ℝ≥0} {h : ℕ} (hh : 0<h) (hn : Fintype.card ι=4*h)
    (lo : BadScalarRichPointFamily dom (2*h) δ₀ u)
    (hi : BadScalarRichPointFamily dom (2*h) δ₁ u)
    (hlo : ⌈(1-δ₀)*(Fintype.card ι : ℝ≥0)⌉₊=3*h)
    (hhi : ⌈(1-δ₁)*(Fintype.card ι : ℝ≥0)⌉₊=3*h-1)
    {t : F} (ht : t ∈ hi.G \ lo.G) (f : F[X]) (hf : f ≠ 0) (hdeg : f.natDegree ≤ h)
    (ha : ApolarThrough (syndrome ((univ : Finset ι).map dom) (RingHom.id F)
      (fun y => coordinateRow dom (u 0) y+t*coordinateRow dom (u 1) y)) f (h-1)) :
    ∀ i ∉ fullAgreement dom (u 0) (u 1) t (hi.q t), f.eval (dom i) ≠ 0 := by
  classical
  let H := (univ : Finset ι).map dom
  let S := fullAgreement dom (u 0) (u 1) t (hi.q t)
  let E := ((univ : Finset ι) \ S).map dom
  let q := hi.q t
  let a (y : F) := coordinateRow dom (u 0) y+t*coordinateRow dom (u 1) y
  let w := rowWeight H (fun y => a y-q.eval y)
  have hszS : S.card=3*h-1 := fresh_exact lo hi (by omega) hhi ht
  have hsz : E.card=h+1 := by
    simp only [E,card_map,card_sdiff_of_subset (subset_univ S),card_univ,hszS,hn]
    omega
  have hsub : E ⊆ H := Finset.map_subset_map.mpr sdiff_subset
  have hrow (y : F) (hy : y ∈ H) (hey : y ∉ E) : a y=q.eval y := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp hy
    have hS : i ∈ S := by
      by_contra h
      exact hey (mem_map.mpr ⟨i, mem_sdiff.mpr ⟨mem_univ _,h⟩,rfl⟩)
    simpa only [a,q,coordinateRow_apply] using (mem_filter.mp hS).2.symm
  have hw (y : F) (hy : y ∈ E) : w y≠0 := by
    obtain ⟨i,hi',rfl⟩ := mem_map.mp hy
    have hS := (mem_sdiff.mp hi').2
    have hfail : (hi.q t).eval (dom i) ≠ u 0 i+t*u 1 i := fun h =>
      hS (mem_filter.mpr ⟨mem_univ _,h⟩)
    apply rowWeight_nonzero
    apply sub_ne_zero.mpr
    simpa only [a,q,coordinateRow_apply] using hfail.symm
  have hqar : q.natDegree<2*h := hi.degree_lt t (mem_sdiff.mp ht).1
  have haE : ApolarThrough (weighted E (RingHom.id F) w) f (h-1) := by
    intro B hB
    have hD : q.natDegree+(f*B).natDegree < H.card-1 := by
      have hF := natDegree_mul_le (p:=f) (q:=B)
      have hcard : H.card=4*h := by simp [H,hn]
      omega
    rw [←syndrome_reduced H E a q (f*B) (RingHom.id F) hsub hrow hD]
    exact ha B hB
  rcases all_or_none E w f (s:=h-1) (by omega) haE hw with hcover | hmiss
  · have hroot : E ⊆ f.roots.toFinset := fun y hy =>
      Multiset.mem_toFinset.mpr ((mem_roots hf).mpr (hcover y hy))
    have h := (card_le_card hroot).trans ((Multiset.toFinset_card_le _).trans (card_roots' f))
    omega
  · intro i hi'
    exact hmiss _ (mem_map.mpr ⟨i,mem_sdiff.mpr ⟨mem_univ _,hi'⟩,rfl⟩)

omit [Fintype F] [Nonempty ι] in
/-- At a genuinely new scalar the middle catalecticant has at most one
projective locator, and its preceding catalecticant has trivial kernel. -/
theorem fresh_kernel {δ₀ δ₁ : ℝ≥0} {h : ℕ} (hh : 0<h) (hn : Fintype.card ι=4*h)
    (lo : BadScalarRichPointFamily dom (2*h) δ₀ u)
    (hi : BadScalarRichPointFamily dom (2*h) δ₁ u)
    (hlo : ⌈(1-δ₀)*(Fintype.card ι : ℝ≥0)⌉₊=3*h)
    (hhi : ⌈(1-δ₁)*(Fintype.card ι : ℝ≥0)⌉₊=3*h-1)
    {t : F} (ht : t ∈ hi.G \ lo.G) :
    let L := syndrome ((univ : Finset ι).map dom) (RingHom.id F)
      (fun y => coordinateRow dom (u 0) y+t*coordinateRow dom (u 1) y)
    ∃ i ∉ fullAgreement dom (u 0) (u 1) t (hi.q t),
      (∀ f g : F[X], f.natDegree ≤ h → g.natDegree ≤ h →
        ApolarThrough L f (h-1) → ApolarThrough L g (h-1) →
        C (g.eval (dom i))*f = C (f.eval (dom i))*g) ∧
      (∀ q : F[X], q.natDegree < h → ApolarThrough L q h → q=0) := by
  classical
  dsimp only
  let S := fullAgreement dom (u 0) (u 1) t (hi.q t)
  have hs : S.card=3*h-1 := fresh_exact lo hi (by omega) hhi ht
  have hex : 0 < ((univ : Finset ι) \ S).card := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hs,hn]
    omega
  obtain ⟨i,hi'⟩ := card_pos.mp hex
  have hiS := (mem_sdiff.mp hi').2
  refine ⟨i,hiS,?_,?_⟩
  · intro f g hf hg hfa hga
    by_contra hn'
    let b := C (g.eval (dom i))*f - C (f.eval (dom i))*g
    have hb : b ≠ 0 := sub_ne_zero.mpr hn'
    have hd : b.natDegree ≤ h := by
      simpa only [b,max_self] using natDegree_sub_le_of_le ((natDegree_C_mul_le (g.eval (dom i)) f).trans hf)
        ((natDegree_C_mul_le (f.eval (dom i)) g).trans hg)
    have he := fresh_misses hh hn lo hi hlo hhi ht b hb hd
    refine (he ?_ i hiS) ?_
    · intro B hB
      simp only [b,sub_mul,←Polynomial.smul_eq_C_mul,smul_mul_assoc,map_sub,map_smul,hfa B hB,hga B hB,
        smul_zero,sub_zero]
    · simp [b,mul_comm]
  · intro q hq aq
    by_contra hne
    let b : F[X] := q*((Polynomial.X : F[X])-C (dom i))
    have hb : b≠0 := mul_ne_zero hne (X_sub_C_ne_zero (dom i))
    have hd : b.natDegree ≤ h := by
      have hh' := natDegree_mul_le (p:=q) (q:=(Polynomial.X : F[X])-C (dom i))
      rw [natDegree_X_sub_C] at hh'
      dsimp only [b]
      omega
    have he := fresh_misses hh hn lo hi hlo hhi ht b hb hd
    refine (he ?_ i hiS) ?_
    · intro B hB
      rw [show b*B=q*(((Polynomial.X : F[X])-C (dom i))*B) from mul_assoc _ _ _]
      apply aq
      have hd' := natDegree_mul_le (p:=(Polynomial.X : F[X])-C (dom i)) (q:=B)
      rw [natDegree_X_sub_C] at hd'
      omega
    · simp [b]

/-- A failure on the two named budgets must contain many genuinely new scalars. -/
theorem fresh_card {δ₀ δ₁ : ℝ≥0} (lo : BadScalarRichPointFamily dom 536870912 δ₀ u)
    (hi : BadScalarRichPointFamily dom 536870912 δ₁ u) (hn : Fintype.card ι = 1073741824)
    (hc : 805306368 ≤ ⌈(1-δ₀)*(Fintype.card ι : ℝ≥0)⌉₊) :
    (1073741824 < hi.G.card → 268435454 ≤ (hi.G \ lo.G).card) ∧
    (2147483648 < hi.G.card → 1342177278 ≤ (hi.G \ lo.G).card) := by
  have h₁ := boundary_count lo hn hc
  have h₂ := Finset.le_card_sdiff lo.G hi.G
  omega

#print axioms boundary_count
#print axioms fresh_exact
#print axioms fresh_misses
#print axioms fresh_card
#print axioms fresh_kernel

end ProximityGap.ApolarSuccessorPopulation
