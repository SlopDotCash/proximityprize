/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoHeadExtraWitness
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveWorstCaseIncidence

/-! # Two full heads and two additional projective directions -/
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoProjectiveExtraWitness
open HalfPredecessorCoreFreshDecode MCAProjectiveEquivariance ProjectiveWorstCaseIncidence

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Two heads for a pair of normalized rows. On the common exterior the extra projected
polynomials interpolate both rows. Each has a separate support with a joint mismatch. -/
structure Arrangement (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0) where
  head : Fin 2 → F[X]
  extra : Fin 2 → F[X]
  row : Fin 2 → I → F
  core : Fin 2 → Finset I
  support : Fin 2 → Finset I
  common : Finset I
  degree : ∀ j, (head j).natDegree + 1 < k
  extra_degree : ∀ j, (extra j).natDegree + 1 < k
  rank : ∀ j, k ≤ (core j).card
  size : ∀ j, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ (((core j).card + 1 : ℕ) : ℝ≥0)
  core_agrees : ∀ j i, (head j).eval (dom i) = row 0 i ↔ i ∈ core j
  common_rows : ∀ j i, i ∈ core j → row 1 i = row 0 i
  fresh : ∀ j i, i ∉ core j → row 1 i ≠ (head j).eval (dom i)
  slopes : ∀ i, i ∉ core 0 → i ∉ core 1 →
    (row 1 i - (head 0).eval (dom i)) / (row 0 i - (head 0).eval (dom i)) ≠
    (row 1 i - (head 1).eval (dom i)) / (row 0 i - (head 1).eval (dom i))
  common_rank : k ≤ common.card
  common_in : ∀ j, common ⊆ support j
  extra_agrees : ∀ j i, i ∈ support j → (extra j).eval (dom i) = row j i
  support_size : ∀ j, (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((support j).card : ℝ≥0)
  first_mismatch : ∃ i ∈ support 0, i ∉ core 0 ∧ (extra 1).eval (dom i) ≠ row 1 i
  second_mismatch : ∃ i ∈ support 1, (extra 0).eval (dom i) ≠ row 0 i

variable {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0}

private abbrev Slot (a : Arrangement dom k δ) := (j : Fin 2) × ↥(a.core j)ᶜ

/-- The two extra projective directions and all the fresh labels fit in one finite chart. -/
theorem witnesses (a : Arrangement dom k δ) (N : ℕ) (hN : N = ∑ j, (a.core j)ᶜ.card)
    (hq : (N + 1).choose 2 < Fintype.card F) (room : N + 1 < Fintype.card F) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F), G.card = N + 2 ∧
      ∀ z ∈ G, mcaEvent (ReedSolomon.code dom k : Set (I → F)) δ (u 0) (u 1) z := by
  classical
  let H (j : Fin 2) (i : I) := (a.head j).eval (dom i)
  let slope (s : Slot a) := (a.row 1 s.2.val - H s.1 s.2.val) / (a.row 0 s.2.val - H s.1 s.2.val)
  have nz (s : Slot a) : slope s ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr (a.fresh s.1 s.2.val (mem_compl.mp s.2.property)))
    (sub_ne_zero.mpr (fun e => mem_compl.mp s.2.property ((a.core_agrees _ _).mp e.symm)))
  let key : Option (Slot a) → F × F := fun x => x.elim (0, 0) fun s => (slope s * dom s.2.val, slope s)
  have inj : Function.Injective key := by
    rintro (_ | ⟨j, x⟩) (_ | ⟨l, y⟩) e
    · rfl
    · exact (nz _ (congrArg Prod.snd e).symm).elim
    · exact (nz _ (congrArg Prod.snd e)).elim
    · have eq : slope ⟨j, x⟩ = slope ⟨l, y⟩ := congrArg Prod.snd e
      have ab : slope ⟨j, x⟩ * dom x.val = slope ⟨l, y⟩ * dom y.val := congrArg Prod.fst e
      rw [← eq] at ab
      have xy := dom.injective (mul_left_cancel₀ (nz ⟨j, x⟩) ab)
      have jl : j = l := by
        by_contra ne
        have h₁ : x.val ∉ a.core j := mem_compl.mp x.property
        have h₂ : x.val ∉ a.core l := xy ▸ mem_compl.mp y.property
        have same : (a.row 1 x.val - H j x.val) / (a.row 0 x.val - H j x.val) =
            (a.row 1 x.val - H l x.val) / (a.row 0 x.val - H l x.val) := by
          simpa only [slope, ← xy] using eq
        fin_cases j <;> fin_cases l
        · exact ne rfl
        · exact a.slopes x.val h₁ h₂ same
        · exact a.slopes x.val h₂ h₁ same.symm
        · exact ne rfl
      subst l
      have hxy : x = y := Subtype.ext xy
      subst y; rfl
  have card : Fintype.card (Option (Slot a)) = N + 1 := by
    simp [Slot, hN, card_compl]
  obtain ⟨θ, sep⟩ := TwoHeadExtraWitness.separate ⟨key, inj⟩ (by simpa only [card] using hq)
  let alpha (s : Slot a) := slope s * (dom s.2.val + θ)
  have eval (s : Slot a) : (key (some s)).1 + θ * (key (some s)).2 = alpha s := by
    dsimp [key, alpha]; ring
  have nzα (s : Slot a) : alpha s ≠ 0 := by
    intro h
    have e : (some s : Option (Slot a)) = none := sep ((eval s).trans (by simpa [key] using h))
    cases e
  have distinct : Function.Injective alpha := fun s t eq =>
    Option.some.inj (sep (a₁ := some s) (a₂ := some t) ((eval s).trans (eq.trans (eval t).symm)))
  let twist (f : F[X]) := ((Polynomial.X : F[X]) + C θ) * f
  have deg {f : F[X]} (small : f.natDegree + 1 < k) : (twist f).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    apply WithBot.coe_lt_coe.mpr
    have bound := natDegree_mul_le (p := (Polynomial.X : F[X]) + C θ) (q := f)
    rw [natDegree_X_add_C] at bound
    change (((Polynomial.X : F[X]) + C θ) * f).natDegree < k
    omega
  let C₀ := ReedSolomon.code dom k
  let u : WordStack F (Fin 2) I := ![a.row 0, fun i => (dom i + θ) * a.row 1 i]
  have literal (s : Slot a) : mcaEvent (C₀ : Set (I → F)) δ (u 0) (u 1) (-(alpha s)⁻¹) := by
    let j := s.1
    let x := s.2.val
    let z := -(alpha s)⁻¹
    have hx : x ∉ a.core j := mem_compl.mp s.2.property
    have mis : a.row 0 x ≠ H j x := fun e => hx ((a.core_agrees j x).mp e.symm)
    have hd := ((degree_le_natDegree).trans_lt (show ((a.head j).natDegree : WithBot ℕ) < k by
      exact_mod_cast (show (a.head j).natDegree < k by have := a.degree j; omega)))
    have hr := deg (a.degree j)
    have hz : z ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (nzα s))
    apply mcaEvent_of_affine_core_fresh dom k δ u z (a.core j) x (a.head j) (twist (a.head j))
      hx hd hr ((degree_add_le ..).trans_lt (max_lt hd ((degree_C_mul hz).trans_lt hr)))
      (a.rank j) (a.size j)
    · intro i hi
      have e := (a.core_agrees j i).mpr hi
      exact ⟨e, by change (twist _).eval _ = (dom i + θ) * a.row 1 i
                   simp [twist, e, a.common_rows j i hi]⟩
    · have id : alpha s * (a.row 0 x - H j x) = (dom x + θ) * (a.row 1 x - H j x) := by
        change ((a.row 1 x - H j x) / (a.row 0 x - H j x) * (dom x + θ)) *
          (a.row 0 x - H j x) = _
        rw [mul_right_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr mis), mul_comm]
      change _ = a.row 0 x + z * ((dom x + θ) * a.row 1 x)
      simp only [twist, eval_add, eval_mul, eval_C, eval_X]
      change H j x + z * ((dom x + θ) * H j x) = _
      dsimp only [z]
      field_simp [nzα s]
      linear_combination -id
    · intro e
      exact mis (congrArg Prod.fst e).symm
  have exdeg (j : Fin 2) : (a.extra j).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (a.extra j).natDegree < k by have := a.extra_degree j; omega)
  have nojoint (j : Fin 2) (x : I) (xe : x ∈ a.support j)
      (mis : ((a.extra 0).eval (dom x), (twist (a.extra 1)).eval (dom x)) ≠ (u 0 x, u 1 x)) :
      ¬ pairJointAgreesOn (C₀ : Set (I → F)) (a.support j) (u 0) (u 1) := by
    have h := not_pairJointAgreesOn_insert_core dom k u a.common x (a.extra 0) (twist (a.extra 1))
      (exdeg 0) (deg (a.extra_degree 1)) a.common_rank (fun i hi => by
        refine ⟨a.extra_agrees 0 i (a.common_in 0 hi), ?_⟩
        change (twist _).eval _ = (dom i + θ) * a.row 1 i
        simp [twist, a.extra_agrees 1 i (a.common_in 1 hi)]) mis
    rintro ⟨v₀, h₀, v₁, h₁, explain⟩
    apply h
    refine ⟨v₀, h₀, v₁, h₁, fun i hi => explain i ?_⟩
    rcases mem_insert.mp hi with rfl | hi
    · exact xe
    · exact a.common_in j hi
  have horiz : mcaEvent (C₀ : Set (I → F)) δ (u 0) (u 1) (0 : F) := by
    obtain ⟨i, hi, hx, bad⟩ := a.first_mismatch
    have nt : dom i + θ ≠ 0 := fun e => nzα ⟨0, i, mem_compl.mpr hx⟩ (by simp [alpha, e])
    refine ⟨a.support 0, a.support_size 0, ⟨_, ReedSolomon.mem_code_iff_eval.mpr
      ⟨a.extra 0, exdeg 0, fun _ => rfl⟩, fun x hx => ?_⟩, nojoint 0 i hi ?_⟩
    · simpa [u] using a.extra_agrees 0 x hx
    · intro e
      have h := congrArg Prod.snd e
      change (twist _).eval _ = (dom i + θ) * a.row 1 i at h
      simp only [twist, eval_mul, eval_add, eval_C, eval_X] at h
      exact bad (mul_left_cancel₀ nt h)
  have vert : mcaEventProj (C₀ : Set (I → F)) δ (u 0) (u 1) (0 : F) 1 := by
    obtain ⟨i, hi, bad⟩ := a.second_mismatch
    refine ⟨a.support 1, a.support_size 1, ⟨_, ReedSolomon.mem_code_iff_eval.mpr
      ⟨twist (a.extra 1), deg (a.extra_degree 1), fun _ => rfl⟩, fun x hx => ?_⟩,
      nojoint 1 i hi (fun e => bad (congrArg Prod.fst e))⟩
    simp [u, twist, a.extra_agrees 1 x hx]
  let lab (x : Option (Slot a)) : F := x.elim 0 fun s => -(alpha s)⁻¹
  have unique : Function.Injective lab := by
    rintro (_ | x) (_ | y) eq
    · rfl
    · exact (nzα y (by simpa [lab] using eq.symm)).elim
    · exact (nzα x (by simpa [lab] using eq)).elim
    · exact congrArg some (distinct (inv_inj.mp (neg_inj.mp eq)))
  have allbad : univ.image lab ⊆ univ.filter (fun z : F => mcaEvent (C₀ : Set (I → F)) δ (u 0) (u 1) z) := by
    rintro z hz
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    obtain ⟨_ | s, _, rfl⟩ := mem_image.mp hz
    · exact horiz
    · exact literal s
  have affine := card_le_card allbad
  rw [card_image_of_injective _ unique, card_univ, card] at affine
  have proj := badSlotCount_eq_affine_add_infty (F := F) (C₀ : Set (I → F)) δ (u 0) (u 1)
  simp only [vert, ↓reduceIte] at proj
  have too : ¬ OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (C₀ : Set (I → F)) δ (N + 1) := by
    intro h
    have bound := (worstCaseIncidenceBounded_iff_projective C₀ δ _ room).mp h u
    omega
  unfold OpenCoreConditionalPin.WorstCaseIncidenceBounded at too
  push Not at too
  obtain ⟨v, hv⟩ := too
  obtain ⟨G, hsub, hcard⟩ := exists_subset_card_eq (show N + 2 ≤ _ from hv)
  exact ⟨v, G, hcard, fun z hz => (mem_filter.mp (hsub hz)).2⟩

#print axioms witnesses
end ArkLib.ProximityGap.Frontier.TwoProjectiveExtraWitness
