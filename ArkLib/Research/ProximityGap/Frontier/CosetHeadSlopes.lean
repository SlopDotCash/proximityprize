/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent

/-! # Multiplicatively separated secant slopes on a smooth domain

Use the points (bᵢ,tⁱ) in the coefficient plane. Polynomials representing
slopes on different edges have different two-element supports. A field-size
bound linear in the number of possible site ratios therefore suffices for
one parameter t to separate all edge labels on the whole evaluation domain.
-/

set_option autoImplicit false
namespace ProximityGap.CosetHeadSlopes
open Finset Polynomial
variable {F : Type} [Field F] [DecidableEq F] {m : ℕ}
abbrev Edge (m : ℕ) := Fin m × Fin m

/-- Each unordered edge has one representative, in increasing order. -/
def edges (m : ℕ) : Finset (Edge m) := univ.filter fun e => e.1 < e.2

/-- The slope as a polynomial in the common specialization parameter. -/
noncomputable def pSlope (b : Fin m ↪ F) (e : Edge m) : F[X] :=
  C ((b e.1-b e.2)⁻¹)*((Polynomial.X : F[X])^e.1.val - (Polynomial.X : F[X])^e.2.val)

omit [DecidableEq F] in
private theorem has_endpoint (b : Fin m ↪ F) (e : Edge m) (he : e∈edges m)
    (j : Fin m) (hj : j=e.1 ∨ j=e.2) : (pSlope b e).coeff j.val ≠ 0 := by
  have h := (mem_filter.mp he).2
  have ne : e.1.val ≠ e.2.val := Nat.ne_of_lt h
  have denom := inv_ne_zero (sub_ne_zero.mpr (b.injective.ne (ne_of_lt h)))
  rcases hj with rfl|rfl <;> simp [pSlope,coeff_X_pow,ne,ne.symm,denom]

omit [DecidableEq F] in
private theorem off_endpoint (b : Fin m ↪ F) (e : Edge m) (j : Fin m)
    (hu : j≠e.1) (hv : j≠e.2) : (pSlope b e).coeff j.val=0 := by
  have u : e.1.val ≠ j.val := fun eq => hu (Fin.ext eq.symm)
  have v : e.2.val ≠ j.val := fun eq => hv (Fin.ext eq.symm)
  simp [pSlope,coeff_X_pow,u.symm,v.symm]

omit [DecidableEq F] in
private theorem diff_ne (b : Fin m ↪ F) {e f : Edge m} (he : e∈edges m) (hf : f∈edges m)
    (ne : e≠f) (h : F) : pSlope b e - C h*pSlope b f ≠ 0 := by
  have eord := (mem_filter.mp he).2
  have ford := (mem_filter.mp hf).2
  have unique : ∃ i : Fin m, (i=e.1 ∨ i=e.2) ∧ i≠f.1 ∧ i≠f.2 := by
    by_contra! hn
    have a := hn e.1 (Or.inl rfl)
    have c := hn e.2 (Or.inr rfl)
    by_cases h₁ : e.1=f.1
    · have h₂ : e.2≠f.1 := by omega
      exact ne (Prod.ext h₁ (c h₂))
    · have h₂ := a h₁
      by_cases h₃ : e.2=f.1
      · omega
      · have := c h₃;omega
  obtain ⟨i,hi,hu,hv⟩ := unique
  intro zero
  have q := congrArg (fun P : F[X] => P.coeff i.val) (sub_eq_zero.mp zero)
  apply has_endpoint b e he i hi
  simpa only [coeff_C_mul,off_endpoint b f i hu hv,mul_zero] using q

omit [DecidableEq F] in
private theorem degree_bound (b : Fin m ↪ F) (e : Edge m) : (pSlope b e).natDegree ≤ m-1 := by
  apply (natDegree_C_mul_le ..).trans
  apply (natDegree_sub_le ..).trans
  simp only [natDegree_X_pow,max_le_iff]
  exact ⟨by have := e.1.isLt;omega,by have := e.2.isLt;omega⟩

/-- There is a single specialization for which every nonzero slope is
separated from every scaled slope on another edge, for any finite ratio set. -/
theorem separate [Fintype F] (b : Fin m ↪ F) (R : Finset F)
    (room : ((edges m).card + (edges m).offDiag.card*R.card)*(m-1) < Fintype.card F) :
    ∃ t : F, (∀ e∈edges m, (pSlope b e).eval t ≠ 0) ∧
      ∀ e∈edges m, ∀ f∈edges m, e≠f → ∀ h∈R, (pSlope b e).eval t ≠ h*(pSlope b f).eval t := by
  classical
  let E := edges m
  let roots (P : F[X]) := P.roots.toFinset
  have num (P : F[X]) : (roots P).card ≤ P.natDegree :=
    (Multiset.toFinset_card_le _).trans (card_roots' P)
  let zeros := E.biUnion fun e => roots (pSlope b e)
  let pairs := E.offDiag ×ˢ R
  let polys (g : (Edge m × Edge m) × F) := pSlope b g.1.1-C g.2*pSlope b g.1.2
  let bad := zeros ∪ pairs.biUnion (fun g => roots (polys g))
  have zbound : zeros.card ≤ E.card*(m-1) := by
    apply card_biUnion_le.trans
    simpa using (sum_le_sum (s:=E) (g:=fun _ => m-1) fun e _ => (num _).trans (degree_bound b e))
  have pbound : (pairs.biUnion (fun g => roots (polys g))).card ≤ pairs.card*(m-1) := by
    apply card_biUnion_le.trans
    have h (g) (_ : g∈pairs) : (roots (polys g)).card ≤ m-1 :=
      (num _).trans ((natDegree_sub_le ..).trans (max_le (degree_bound b _) ((natDegree_C_mul_le ..).trans (degree_bound b _))))
    simpa using sum_le_sum h
  have small : bad.card < Fintype.card F := by
    refine (card_union_le ..).trans_lt ((Nat.add_le_add zbound pbound).trans_lt ?_)
    simpa [pairs,E,Nat.add_mul] using room
  obtain ⟨t,_,ht⟩ := exists_mem_notMem_of_card_lt_card (t:=univ) (by simpa using small)
  refine ⟨t,?_,?_⟩
  · intro e he hz
    have nonzero : pSlope b e ≠ 0 := fun hh => has_endpoint b e he _ (Or.inl rfl) (by rw [hh,coeff_zero])
    exact ht (mem_union_left _ (mem_biUnion.mpr ⟨e,he,Multiset.mem_toFinset.mpr ((mem_roots nonzero).mpr hz)⟩))
  · intro e he f hf hne h hh eq
    have ne := diff_ne b he hf hne h
    have ev : (pSlope b e-C h*pSlope b f).IsRoot t := by simp [IsRoot,eq]
    exact ht (mem_union_right _ (mem_biUnion.mpr ⟨((e,f),h),
      mem_product.mpr ⟨mem_offDiag.mpr ⟨he,hf,hne⟩,hh⟩,Multiset.mem_toFinset.mpr ((mem_roots ne).mpr ev)⟩))

/-- The slopes of the chosen row pairs have disjoint multiples at distinct
sites on different edges, including for nonsmooth domains with a small ratio set. -/
theorem labels [Fintype F] {I : Type} (x : I ↪ F) (xn : ∀ i, x i ≠ 0)
    (b : Fin m ↪ F) (R : Finset F) (ratio : ∀ i j, x j/x i ∈ R)
    (room : ((edges m).card + (edges m).offDiag.card*R.card)*(m-1) < Fintype.card F) :
    ∃ a : Fin m → F, Set.InjOn (fun p : Edge m × I =>
      ((a p.1.1-a p.1.2)/(b p.1.1-b p.1.2))*x p.2) {p | p.1 ∈ edges m} := by
  obtain ⟨t,nz,sep⟩ := separate b R room
  let a (i : Fin m) := t^i.val
  have form (e : Edge m) : (a e.1-a e.2)/(b e.1-b e.2) = (pSlope b e).eval t := by
    simp [pSlope,a,div_eq_inv_mul]
  refine ⟨a,?_⟩
  rintro ⟨e,i⟩ he ⟨f,j⟩ hf eq
  change _*x i = _*x j at eq
  simp only [form] at eq
  by_cases same : e=f
  · subst f
    exact Prod.ext rfl (x.injective (mul_left_cancel₀ (nz e he) eq))
  · exfalso
    apply sep e he f hf same _ (ratio i j)
    apply (mul_left_inj' (xn i)).mp
    rw [mul_comm ((pSlope b f).eval t) (x j)] at eq
    simpa [mul_right_comm _ ((pSlope b f).eval t),xn i] using eq

/-- A whole multiplicative coset has at most one site ratio per site. -/
theorem smooth_ratios {I : Type} [Fintype I] [Nonempty I] [Fintype F]
    (x : I ↪ F) [ReedSolomon.Smooth x] :
    ∃ R : Finset F, R.card ≤ Fintype.card I ∧ (∀ i, x i ≠ 0) ∧ ∀ i j, x j / x i ∈ R := by
  classical
  let H := ReedSolomon.Smooth.H x
  let c := ReedSolomon.Smooth.a x
  have coset : (↑(univ.image x) : Set F) = (fun u : Fˣ => (c : F) * (u : F)) '' (H : Set Fˣ) :=
    ReedSolomon.Smooth.h_coset
  have point (i : I) : ∃ u ∈ H, (c : F) * (u : F) = x i := by
    have hi : x i ∈ (↑(univ.image x) : Set F) := mem_image_of_mem _ (mem_univ _)
    rwa [coset] at hi
  let o := Classical.choice (inferInstance : Nonempty I)
  refine ⟨univ.image (fun i => x i / x o), card_image_le.trans (le_of_eq card_univ), ?_, ?_⟩
  · intro i
    obtain ⟨u, _, hu⟩ := point i
    rw [← hu]
    exact mul_ne_zero c.ne_zero u.ne_zero
  · intro i j
    obtain ⟨u, hu, ei⟩ := point i
    obtain ⟨v, hv, ej⟩ := point j
    obtain ⟨w, hw, eo⟩ := point o
    have mem : (c : F) * ((v / u * w : Fˣ) : F) ∈ (↑(univ.image x) : Set F) := by
      rw [coset]
      exact ⟨_, H.mul_mem (H.div_mem hv hu) hw, rfl⟩
    obtain ⟨l, _, el⟩ := mem_image.mp mem
    exact mem_image.mpr ⟨l, mem_univ _, by
      rw [el, ← eo, ← ej, ← ei]
      push_cast
      field_simp⟩

/-- On every smooth domain a field bound linear in the domain length suffices
for simultaneous, pairwise distinct secant labels on all sites and edges. -/
theorem smooth_labels [Fintype F] {I : Type} [Fintype I] [Nonempty I]
    (x : I ↪ F) [ReedSolomon.Smooth x] (b : Fin m ↪ F)
    (room : ((edges m).card + (edges m).offDiag.card * Fintype.card I) * (m-1) < Fintype.card F) :
    ∃ a : Fin m → F, Set.InjOn (fun p : Edge m × I =>
      ((a p.1.1-a p.1.2)/(b p.1.1-b p.1.2))*x p.2) {p | p.1 ∈ edges m} := by
  obtain ⟨R, bound, nz, ratios⟩ := smooth_ratios x
  exact labels x nz b R ratios <| lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ bound) _)) room

end ProximityGap.CosetHeadSlopes
#print axioms ProximityGap.CosetHeadSlopes.labels
#print axioms ProximityGap.CosetHeadSlopes.smooth_labels
