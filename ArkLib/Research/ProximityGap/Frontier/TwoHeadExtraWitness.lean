/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AveragedPencilProjection
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness

/-! # A third scalar in addition to all fresh labels from two full secants -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoHeadExtraWitness
open HalfPredecessorCoreFreshDecode
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Choose a parameter separating the affine lines indexed by a finite set of distinct keys. -/
private theorem separate {S : Type} [Fintype S] (key : S ↪ F × F)
    (hq : (Fintype.card S).choose 2 < Fintype.card F) :
    ∃ θ : F, Function.Injective (fun s => (key s).1 + θ * (key s).2) := by
  classical
  let v (θ : F) (s : S) := (key s).1 + θ * (key s).2
  have pair (a : S) (_ : a ∈ univ) (b : S) (_ : b ∈ univ) (hab : a ≠ b) :
      (univ.filter fun θ => v θ a = v θ b).card ≤ 1 := by
    apply card_le_one.mpr
    intro θ h z h'
    have e := (mem_filter.mp h).2
    have f := (mem_filter.mp h').2
    change (key a).1 + θ * (key a).2 = (key b).1 + θ * (key b).2 at e
    change (key a).1 + z * (key a).2 = (key b).1 + z * (key b).2 at f
    have eq : (θ - z) * ((key a).2 - (key b).2) = 0 := by linear_combination e - f
    rcases mul_eq_zero.mp eq with h | h
    · exact sub_eq_zero.mp h
    · have h2 := sub_eq_zero.mp h
      exact (hab (key.injective (Prod.ext (by simpa only [h2, add_left_inj] using e) h2))).elim
  obtain ⟨θ, hθ⟩ := AveragedPencilProjection.exists_image_with_pair_loss univ v pair
  simp only [card_univ, Nat.div_eq_of_lt hq, Nat.sub_zero] at hθ
  have eq : (univ.image (v θ)).card = (univ : Finset S).card := le_antisymm card_image_le (by simpa using hθ)
  exact ⟨θ, Set.injOn_univ.mp (by simpa only [coe_univ] using card_image_iff.mp eq)⟩

/-- Two full cores and a prescribed third section. The complement of the two
cores fixes the second row of any joint polynomial pair on the third support. -/
structure Arrangement (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) where
  head : Fin 2 → F[X]
  q : F[X]
  b : I → F
  core : Fin 2 → Finset I
  extra : Finset I
  nz : ∀ x, dom x ≠ 0
  deg : ∀ j, (head j).degree < (k:WithBot ℕ)
  degX : ∀ j, (Polynomial.X * head j).degree < (k:WithBot ℕ)
  degQ : q.degree < (k:WithBot ℕ)
  degXQ : (Polynomial.X * q).degree < (k:WithBot ℕ)
  pos : 0 < k
  rank : ∀ j, k ≤ (core j).card
  size : ∀ j, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (((core j).card + 1 : ℕ) : ℝ≥0)
  core_iff : ∀ x j, b x = (head j).eval (dom x) ↔ x ∈ core j
  distinct : ∀ x, x ∉ core 0 ∪ core 1 → (head 0).eval (dom x) ≠ (head 1).eval (dom x)
  out_rank : k ≤ (univ \ (core 0 ∪ core 1)).card
  out_in : univ \ (core 0 ∪ core 1) ⊆ extra
  anchor : (extra ∩ (core 0 ∪ core 1)).Nonempty
  extra_matches : ∀ x ∈ extra, q.eval (dom x) = b x
  extra_size : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (extra.card : ℝ≥0)

variable {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}

private abbrev Slot (a : Arrangement dom k δ) := (j : Fin 2) × ↥(a.core j)ᶜ

/-- A single received pair has one distinct bad label for each missing
head-site incidence, together with the untouched scalar zero. -/
theorem witnesses (a : Arrangement dom k δ)
    (hq : (1 + ∑ j, (a.core j)ᶜ.card).choose 2 < Fintype.card F) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F), G.card = 1 + ∑ j, (a.core j)ᶜ.card ∧
      ∀ z ∈ G, mcaEvent ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F)) δ (u 0) (u 1) z := by
  classical
  let O := univ \ (a.core 0 ∪ a.core 1)
  let val (j : Fin 2) (x : I) := (a.head j).eval (dom x)
  let v (s : Slot a) : F := if s.2.val ∈ O then (a.b s.2.val - val s.1 s.2.val)⁻¹ else 0
  let key : Option (Slot a) → F × F := fun s => s.elim (0, 0) (fun t => (dom t.2.val, v t))
  have hkey : Function.Injective key := by
    rintro (_ | ⟨j, x⟩) (_ | ⟨l, y⟩) eq
    · rfl
    · exact (a.nz _ (congrArg Prod.fst eq).symm).elim
    · exact (a.nz _ (congrArg Prod.fst eq)).elim
    · have hv : x.val = y.val := dom.injective (congrArg Prod.fst eq)
      have vv : v ⟨j, x⟩ = v ⟨l, y⟩ := congrArg Prod.snd eq
      by_cases h : j = l
      · subst l
        have xy : x = y := Subtype.ext hv
        subst y; rfl
      have hx : x.val ∉ a.core j := mem_compl.mp x.property
      have hy : x.val ∉ a.core l := hv ▸ mem_compl.mp y.property
      have ho : x.val ∈ O := by
          change x.val ∈ univ \ (a.core 0 ∪ a.core 1)
          fin_cases j <;> fin_cases l <;> simp_all
      have equal : val j x.val = val l x.val := by
        simp only [v, ← hv, ho, ite_true, inv_inj, sub_right_inj] at vv
        exact vv
      have hne := a.distinct x.val (mem_sdiff.mp ho).2
      fin_cases j <;> fin_cases l <;> simp_all [val]
  have card : Fintype.card (Option (Slot a)) = 1 + ∑ j, (a.core j)ᶜ.card := by
    simp only [Fintype.card_option, Fintype.card_sigma, Fintype.card_coe, Slot]; omega
  obtain ⟨θ, sep⟩ := separate (⟨key, hkey⟩) (by simpa only [card] using hq)
  let alpha (s : Slot a) := dom s.2.val + θ * v s
  have nz (s : Slot a) : alpha s ≠ 0 := by
    intro h
    have eq : (some s : Option (Slot a)) = none := sep (by simpa [key, alpha] using h)
    cases eq
  have sep' : Function.Injective alpha := fun x y h => Option.some.inj (sep (a₁ := some x) (a₂ := some y) h)
  have core_union {j : Fin 2} {y : I} (h : y ∈ a.core j) : y ∈ a.core 0 ∪ a.core 1 := by
    fin_cases j
    · exact mem_union_left _ h
    · exact mem_union_right _ h
  have existsO : O.Nonempty := card_pos.mp (a.pos.trans_le a.out_rank)
  obtain ⟨o, ho⟩ := existsO
  have notcore (j : Fin 2) : o ∉ a.core j := by
    have n := (mem_sdiff.mp ho).2
    fin_cases j <;> simp_all
  let os (j : Fin 2) : Slot a := ⟨j, o, mem_compl.mpr (notcore j)⟩
  have theta : θ ≠ 0 := by
    intro z
    have e : os 0 = os 1 := sep' (by simp [alpha, z, os])
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Sigma.fst e)
  let row (x : I) := dom x * a.b x + (if x ∈ O then θ else 0)
  let u : WordStack F (Fin 2) I := ![a.b, row]
  let C₀ := ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F))
  have literal (s : Slot a) : mcaEvent C₀ δ (u 0) (u 1) (-(alpha s)⁻¹) := by
    let j := s.1
    let x := s.2.val
    let z := -(alpha s)⁻¹
    have hx : x ∉ a.core j := mem_compl.mp s.2.property
    have mis : a.b x ≠ val j x := fun h => hx ((a.core_iff x j).mp h)
    have subne := sub_ne_zero.mpr mis
    have id : (alpha s) * (a.b x - val j x) = (a.b x - val j x) * dom x + (if x ∈ O then θ else 0) := by
      by_cases hh : x ∈ O
      · change (dom x + θ * (if x ∈ O then (a.b x - val j x)⁻¹ else 0)) * (a.b x - val j x) = _
        simp only [hh, ite_true]; field_simp [subne]
      · change (dom x + θ * (if x ∈ O then (a.b x - val j x)⁻¹ else 0)) * (a.b x - val j x) = _
        simp [hh, mul_comm]
    have hz : z ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (nz s))
    have hdeg := degree_C_mul (p := Polynomial.X * a.head j) hz
    apply mcaEvent_of_affine_core_fresh dom k δ u z (a.core j) x (a.head j) (Polynomial.X * a.head j)
      hx (a.deg j) (a.degX j) ((degree_add_le ..).trans_lt (max_lt (a.deg j)
      (hdeg.trans_lt (a.degX j)))) (a.rank j) (a.size j)
    · intro y hy
      have ho' : y ∉ O := by
        intro h; rcases mem_sdiff.mp h with ⟨_, hh⟩
        exact hh (core_union hy)
      have hb := ((a.core_iff y j).mpr hy).symm
      exact ⟨hb, by change (Polynomial.X * a.head j).eval (dom y) = row y; simp [row, ho', hb]⟩
    · change _ = a.b x + z * row x
      simp only [eval_add, eval_mul, eval_C, eval_X]
      change val j x + (-(alpha s)⁻¹) * (dom x * val j x) = a.b x + (-(alpha s)⁻¹) * (dom x * a.b x + _)
      field_simp [nz s]
      linear_combination -id
    · intro h
      exact mis (congrArg Prod.fst h).symm
  have extra : mcaEvent C₀ δ (u 0) (u 1) (0 : F) := by
    obtain ⟨x, hx⟩ := a.anchor
    have xe := (mem_inter.mp hx).1
    have xo : x ∉ O := fun h => (mem_sdiff.mp h).2 (mem_inter.mp hx).2
    have hp : (Polynomial.X * a.q + C θ).degree < (k:WithBot ℕ) :=
      (degree_add_le ..).trans_lt (max_lt a.degXQ (degree_C_le.trans_lt (by exact_mod_cast a.pos)))
    have nojoint := not_pairJointAgreesOn_insert_core dom k u O x a.q (Polynomial.X * a.q + C θ) a.degQ hp a.out_rank
      (by intro y hy; have h := a.extra_matches y (a.out_in hy)
          exact ⟨h, by change _ = row y; simp [row, hy, h]⟩) (by
        intro h; have t := congrArg Prod.snd h
        change (Polynomial.X * a.q + C θ).eval (dom x) = row x at t
        simp only [eval_add, eval_mul, eval_X, eval_C, row, xo, ite_false, add_zero, a.extra_matches x xe] at t
        exact theta (add_eq_left.mp t))
    let witness : McaDecode dom k δ u 0 := {
      S := a.extra
      P := a.q
      hdeg := a.degQ
      hcard := a.extra_size
      hagree := by intro i hi; simpa [u] using a.extra_matches i hi
      hnjp := by
        rintro ⟨v₀, h₀, v₁, h₁, h⟩
        exact nojoint ⟨v₀, h₀, v₁, h₁, fun i hi => h i (by
          rcases mem_insert.mp hi with rfl | h
          · exact xe
          · exact a.out_in h)⟩ }
    exact witness.mcaEvent
  let lab : Option (Slot a) → F := fun s => s.elim 0 (fun t => -(alpha t)⁻¹)
  have inj : Function.Injective lab := by
    rintro (_ | x) (_ | y) eq
    · rfl
    · exact (nz y (by simpa [lab] using eq.symm)).elim
    · exact (nz x (by simpa [lab] using eq)).elim
    · exact congrArg some (sep' (inv_inj.mp (neg_inj.mp eq)))
  refine ⟨u, univ.image lab, (card_image_of_injective _ inj).trans (by simpa using card), ?_⟩
  intro z hz
  obtain ⟨_ | s, _, rfl⟩ := mem_image.mp hz
  · exact extra
  · exact literal s

#print axioms witnesses
end ArkLib.ProximityGap.Frontier.TwoHeadExtraWitness
