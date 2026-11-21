/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.InterpolatedFourthHead
import ArkLib.Research.ProximityGap.Frontier.FourHeadQuotient

/-! # Counting a smooth four-head construction on a common received stack -/

open Finset Polynomial ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.SmoothFourHeadAssembly

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I] [DecidableEq I]

/-- The fourth head and the three original heads have distinct fresh labels at an
unowned coordinate for a suitable pair of received entries. -/
private theorem hole (v q : Option (Fin 3) → F) (hv : Function.Injective v)
    (hsize : 16 < Fintype.card F) : ∃ τ y : F, (∀ i, v i ≠ τ) ∧
      Function.Injective (fun i => (y - q i) / (v i - τ)) := by
  classical
  obtain ⟨τ, _, ht⟩ := exists_mem_notMem_of_card_lt_card
    (s := univ.image v) (t := (univ : Finset F)) (card_image_le.trans_lt (by simpa using
      (show 4 < Fintype.card F by omega)))
  have ht' (i) : v i ≠ τ := fun he => ht (he ▸ mem_image_of_mem v (mem_univ i))
  let key (i : Option (Fin 3)) : F × F := (-q i / (v i - τ), (v i - τ)⁻¹)
  have hk : Function.Injective key := fun i j he => hv
    (sub_left_inj.mp (inv_inj.mp (congrArg Prod.snd he)))
  obtain ⟨y, hy⟩ := FourHeadQuotient.exists_injective_affine_labels (univ.image key)
    (by simpa [card_image_of_injective _ hk] using hsize)
  refine ⟨τ,y,ht',fun i j he => hk (hy (mem_image_of_mem _ (mem_univ i))
    (mem_image_of_mem _ (mem_univ j)) ?_)⟩
  change -q i / _ + y * _ = -q j / _ + y * _
  change -q i / (v i - τ) + y * (v i - τ)⁻¹ = -q j / (v j - τ) + y * (v j - τ)⁻¹
  simp only [div_eq_mul_inv] at he ⊢
  linear_combination he

/-- A three-head allocation before the fourth interpolant and its fresh scalars are chosen. -/
structure Arrangement (dom : I ↪ F) (k : ℕ) where
  f : Fin 3 → F[X]
  owner : I → Fin 3
  miss : I → Fin 3
  union : Finset I
  ordinary : Finset I
  shared : Finset I
  holes : Finset I
  core : Fin 3 → Finset I
  degree : ∀ j, (f j).natDegree + 1 < k
  core_owned : ∀ j, core j ⊆ union
  agrees : ∀ j x, x ∈ core j → (f j).eval (dom x) = (f (owner x)).eval (dom x)
  ordinary_owned : ordinary ⊆ union
  misses : ∀ x ∈ ordinary, (f (miss x)).eval (dom x) ≠ (f (owner x)).eval (dom x)
  shared_owned : shared ⊆ union
  shared_degree : shared.card + 2 ≤ k
  holes_outside : Disjoint union holes
  outside_distinct : ∀ x ∉ union, Function.Injective (fun j => (f j).eval (dom x))

variable {dom : I ↪ F} {k : ℕ}

/-- Sites owned solely by the interpolated head. -/
def Arrangement.fourthOnly (a : Arrangement dom k) := a.unionᶜ \ a.holes

/-- Total fresh labels, including one per omitted triple value at each triple-owned
ordinary point and four per unowned point. -/
def Arrangement.count (a : Arrangement dom k) :=
  a.ordinary.card + (a.union \ a.shared).card + 3 * a.fourthOnly.card + 4 * a.holes.card

/-- One received stack achieves every fresh label counted by the arrangement. -/
theorem mass (a : Arrangement dom k) (δ : ℝ≥0) (m : ℕ)
    (hc : ∀ j, m ≤ (a.core j).card) (hc₄ : m ≤ (a.shared ∪ a.fourthOnly).card)
    (hkm : k ≤ m) (hsize : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((m + 1 : ℕ) : ℝ≥0))
    (hq : 3 * Fintype.card I < Fintype.card F) (h16 : 16 < Fintype.card F)
    (hfield : a.count.choose 2 ≤ Nat.card F) :
    (a.count : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let old (i : Fin 3) (x : I) := (a.f i).eval (dom x)
  let center (x : I) := old (a.owner x) x
  obtain ⟨B, hBdeg, hBshared, hBoutside⟩ := InterpolatedFourthHead.exists_fourth
    dom a.shared center old k a.shared_degree hq
  let L := Lagrange.nodal a.shared (fun x => dom x)
  let R : Option (Fin 3) → F[X] := Option.elim' B a.f
  let Q : Option (Fin 3) → F[X] := Option.elim' L (fun _ => 0)
  let core : Option (Fin 3) → Finset I := Option.elim' (a.shared ∪ a.fourthOnly) a.core
  have hL (x : I) (hx : x ∉ a.shared) : L.eval (dom x) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    exact fun y hy he => hx (dom.injective he ▸ hy)
  have holevals (x : I) : ∃ τ b : F, x ∈ a.holes →
      (∀ i, (R i).eval (dom x) ≠ τ) ∧ Function.Injective
        (fun i => (b - (Q i).eval (dom x)) / ((R i).eval (dom x) - τ)) := by
    by_cases hx : x ∈ a.holes
    · have hu : x ∉ a.union := fun hu => disjoint_left.mp a.holes_outside hu hx
      have hs : x ∉ a.shared := fun h => hu (a.shared_owned h)
      have hi : Function.Injective (fun i => (R i).eval (dom x)) := by
        intro i j he
        cases i <;> cases j
        · rfl
        · exact False.elim (hBoutside x hs _ he)
        · exact False.elim (hBoutside x hs _ he.symm)
        · exact congrArg some (a.outside_distinct x hu he)
      obtain ⟨τ,b,hh⟩ := hole _ (fun i => (Q i).eval (dom x)) hi h16
      exact ⟨τ,b,fun _ => hh⟩
    · exact ⟨0,0,fun h => (hx h).elim⟩
  choose τ b hh using holevals
  let w (x : I) := if x ∈ a.union then center x else if x ∈ a.holes then τ x else B.eval (dom x)
  let u (x : I) := if x ∈ a.union then 0 else if x ∈ a.holes then b x else L.eval (dom x)
  let tags (x : I) : Finset (Option (Fin 3)) := if x ∈ a.union then
    (if x ∈ a.ordinary then {some (a.miss x)} else ∅) ∪ (if x ∈ a.shared then ∅ else {none})
    else if x ∈ a.holes then univ else univ.erase none
  let S := (x : I) × ↥(tags x)
  have hu_none {x : I} (hu : x ∈ a.union) : none ∈ tags x ↔ x ∉ a.shared := by
    by_cases ho : x ∈ a.ordinary <;> by_cases hs : x ∈ a.shared <;> simp [tags, hu, ho, hs]
  have hu_some {x : I} (hu : x ∈ a.union) (j : Fin 3) :
      some j ∈ tags x ↔ x ∈ a.ordinary ∧ j = a.miss x := by
    by_cases ho : x ∈ a.ordinary <;> by_cases hs : x ∈ a.shared <;> simp [tags, hu, ho, hs]
  have cardAt (x : I) : (tags x).card = (if x ∈ a.ordinary then 1 else 0) +
      (if x ∈ a.union \ a.shared then 1 else 0) +
      (if x ∈ a.fourthOnly then 3 else 0) + (if x ∈ a.holes then 4 else 0) := by
    by_cases hu : x ∈ a.union
    · have hh : x ∉ a.holes := disjoint_left.mp a.holes_outside hu
      by_cases ho : x ∈ a.ordinary <;> by_cases hs : x ∈ a.shared <;>
        simp [tags, Arrangement.fourthOnly, hu, hh, ho, hs]
    · have ho : x ∉ a.ordinary := fun h => hu (a.ordinary_owned h)
      by_cases hh : x ∈ a.holes <;> simp [tags, Arrangement.fourthOnly, hu, ho, hh]
  have hcount : Fintype.card S = a.count := by
    simp [S, Fintype.card_sigma, cardAt, Finset.sum_add_distrib, Arrangement.count, Nat.mul_comm]
    congr 1
    ext x
    simp
  let slope (x : I) (i : Option (Fin 3)) := (u x - (Q i).eval (dom x)) / ((R i).eval (dom x) - w x)
  have local_mis (x : I) (i : Option (Fin 3)) (hti : i ∈ tags x) : (R i).eval (dom x) ≠ w x := by
    by_cases hu : x ∈ a.union
    · cases i with
      | none => simpa [R, w, hu, center] using hBoutside x ((hu_none hu).mp hti) (a.owner x)
      | some j =>
        obtain ⟨ho, rfl⟩ := (hu_some hu j).mp hti
        simpa [R, w, hu, center, old] using a.misses x ho
    · by_cases hx : x ∈ a.holes
      · simpa [w, hu, hx] using (hh x hx).1 i
      · have hs : x ∉ a.shared := fun h => hu (a.shared_owned h)
        cases i with
        | none => simp [tags, hu, hx] at hti
        | some j => simpa [R, w, hu, hx, old] using (hBoutside x hs j).symm
  have local_inj (x : I) (i j : Option (Fin 3)) (hti : i ∈ tags x) (htj : j ∈ tags x)
      (he : slope x i = slope x j) : i = j := by
    by_cases hu : x ∈ a.union
    · have h0 (ht : none ∈ tags x) : slope x none ≠ 0 := by
        apply div_ne_zero _ (sub_ne_zero.mpr (local_mis x none ht))
        simpa [u, hu, Q] using hL x ((hu_none hu).mp ht)
      have hs (t : Fin 3) : slope x (some t) = 0 := by simp [slope, u, hu, Q]
      cases i <;> cases j
      · rfl
      · exact ((h0 hti) (he.trans (hs _))).elim
      · exact ((h0 htj) (he.symm.trans (hs _))).elim
      · exact congrArg some (((hu_some hu _).mp hti).2.trans ((hu_some hu _).mp htj).2.symm)
    · by_cases hx : x ∈ a.holes
      · apply (hh x hx).2
        simpa [slope, u, w, hu, hx] using he
      · cases i <;> cases j
        · rfl
        · simp [tags, hu, hx] at hti
        · simp [tags, hu, hx] at htj
        · have hs : x ∉ a.shared := fun h => hu (a.shared_owned h)
          simp only [slope, u, w, hu, hx, ite_false, R, Q, Option.elim', eval_zero, sub_zero,
            div_eq_mul_inv] at he
          exact congrArg some (a.outside_distinct x hu (sub_left_inj.mp
            (inv_inj.mp (mul_left_cancel₀ (hL x hs) he))))
  have hcore (i : Option (Fin 3)) (x : I) (hx : x ∈ core i) :
      (R i).eval (dom x) = w x ∧ (Q i).eval (dom x) = u x := by
    cases i with
    | some j =>
      have hu := a.core_owned j hx
      simpa [R, Q, w, u, hu, center, old] using a.agrees j x hx
    | none =>
      rcases mem_union.mp hx with hs | ho
      · have hu := a.shared_owned hs
        have hz : L.eval (dom x) = 0 := Lagrange.eval_nodal_at_node hs
        simp [u, w, R, Q, hu, hz, hBshared x hs]
      · obtain ⟨hu,hh'⟩ := mem_sdiff.mp ho
        have hnu := mem_compl.mp hu
        simp [R, Q, w, u, hnu, hh']
  have aux := InterpolatedFourthHead.mass dom k δ (fun s : S => core s.2.val) Sigma.fst
    (fun s => R s.2.val) (fun s => Q s.2.val) w u (fun s => slope s.1 s.2.val)
    (by intro s; cases s.2.val with
        | none => exact hBdeg
        | some j => exact a.degree j)
    (by
      intro s
      cases s.2.val with
      | none =>
        apply degree_le_natDegree.trans_lt
        have hd := a.shared_degree
        change (L.natDegree : WithBot ℕ) < _
        rw [show L.natDegree = a.shared.card from Lagrange.natDegree_nodal]
        exact_mod_cast (by omega : a.shared.card < k)
      | some j => simp [Q])
    (fun s => hcore s.2.val)
    (by intro s; cases s.2.val with
        | none => exact hkm.trans hc₄
        | some j => exact hkm.trans (hc j))
    (by
      intro s
      apply hsize.trans
      apply Nat.cast_le.mpr
      apply Nat.add_le_add_right
      cases s.2.val with
      | none => exact hc₄
      | some j => exact hc j)
    (fun s => local_mis _ _ s.2.property)
    (fun s => div_mul_cancel₀ _ (sub_ne_zero.mpr (local_mis _ _ s.2.property)))
    (by
      rintro ⟨x,i⟩ ⟨y,j⟩ hs he
      change x = y at hs
      subst y
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext (local_inj _ _ _ i.property j.property he))))
    (hcount.symm ▸ hfield)
  simpa only [hcount] using aux

end ArkLib.ProximityGap.Frontier.SmoothFourHeadAssembly

#print axioms ArkLib.ProximityGap.Frontier.SmoothFourHeadAssembly.mass
