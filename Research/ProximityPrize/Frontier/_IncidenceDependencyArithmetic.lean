/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Global relation-core rank and shortening for affine decoded heads

For a finite family of error planes, the span of all components of relations is
supported on coordinates belonging to at least two planes. Its dimension plus
the relation-kernel dimension equals the sum of the projection dimensions.
Shortening in the received space then bounds this dimension by the shared
support. The affine-head application derives code membership from two heads.

The finite coordinate ledger at the end retains explicit counting inputs.
This module does not prove a new canonical threshold or a global witness budget.
See `Research/ProximityPrize/multiline-relation-shortening.md` for the exact
first-sponsor research implications and remaining proof obligations.
-/

set_option autoImplicit false

namespace ProximityGap.IncidenceDependencyArithmetic

/-- A nonzero code subspace supported on S satisfies the shortened Singleton
bound. The distance input is the small-support vanishing condition used by the
existing canonical incidence proofs. -/
theorem shortened_subspace_bound {F Coord : Type*} [Field F]
    [Fintype Coord] [DecidableEq Coord]
    (C V : Submodule F (Coord → F)) (D : ℕ) (hDpos : 0 < D)
    (hVC : V ≤ C) (S : Finset Coord)
    (hsupport : ∀ v ∈ V, ∀ x ∉ S, v x = 0)
    (hne : ∃ v ∈ V, v ≠ 0)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    Module.finrank F V + D ≤ S.card + 1 := by
  classical
  have hDcard : D ≤ S.card := by
    by_contra h
    obtain ⟨v, hv, hv0⟩ := hne
    exact hv0 (hdistance v (hVC hv) S (by omega) (hsupport v hv))
  obtain ⟨B, hBS, hBcard⟩ :=
    Finset.exists_subset_card_eq (show D-1 ≤ S.card by omega)
  let res : V →ₗ[F] (↥(S \ B) → F) :=
    { toFun := fun v x => v.val x.val
      map_add' := by
        intros
        rfl
      map_smul' := by
        intros
        rfl }
  have hker : LinearMap.ker res = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 ?_
    intro v hv
    have hsmall : ∀ x ∉ B, v.val x = 0 := by
      intro x hxB
      by_cases hxS : x ∈ S
      · have hx : x ∈ S \ B := Finset.mem_sdiff.mpr ⟨hxS, hxB⟩
        have he := congrArg (fun f : (↥(S \ B) → F) => f ⟨x, hx⟩) hv
        simpa [res] using he
      · exact hsupport v.val v.property x hxS
    have hz := hdistance v.val (hVC v.property) B (by omega) hsmall
    apply Subtype.ext
    exact hz
  have hinj : Function.Injective res := by
    simpa [LinearMap.ker_eq_bot] using hker
  have hdim : Module.finrank F V ≤ (S \ B).card := by
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h
  have hcard : (S \ B).card = S.card-B.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBS]
  rw [hcard, hBcard] at hdim
  omega

/-- A two-dimensional quotient loses at most two dimensions before shortening.
The quotient only needs to be defined on the supported error space. -/
theorem quotient_shortening_bound {F Coord : Type*} [Field F]
    [Fintype Coord] [DecidableEq Coord]
    (C V : Submodule F (Coord → F)) (D : ℕ) (hDpos : 0 < D)
    (q : V →ₗ[F] (Fin 2 → F))
    (hkernel : ∀ v : V, q v = 0 → v.val ∈ C)
    (S : Finset Coord) (hsupport : ∀ v ∈ V, ∀ x ∉ S, v x = 0)
    (hrank : 3 ≤ Module.finrank F V)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    Module.finrank F V + D ≤ S.card + 3 := by
  classical
  let W : Submodule F (Coord → F) := (LinearMap.ker q).map V.subtype
  have hdim : Module.finrank F W = Module.finrank F (LinearMap.ker q) := by
    dsimp [W]
    rw [Submodule.finrank_map_subtype_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker q
  have hrange : Module.finrank F (LinearMap.range q) ≤ 2 := by
    refine le_trans (Submodule.finrank_le _) ?_
    simp
  have hWpos : 0 < Module.finrank F W := by omega
  have hWbot : W ≠ ⊥ := by
    intro h
    rw [h] at hWpos
    simpa using hWpos
  have hWC : W ≤ C := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact hkernel w hw
  have hWS : ∀ v ∈ W, ∀ x ∉ S, v x = 0 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact hsupport w.val w.property
  have hshort := shortened_subspace_bound C W D hDpos hWC S hWS
    (Submodule.exists_mem_ne_zero_of_ne_bot hWbot) hdistance
  omega

/-- The shortening bound in the received-space form used by bad witnesses. -/
theorem received_space_shortening_bound {F Coord : Type*} [Field F]
    [Fintype Coord] [DecidableEq Coord]
    (C V P : Submodule F (Coord → F)) (D : ℕ) (hDpos : 0 < D)
    (hVP : V ≤ C ⊔ P) (hP : Module.finrank F P ≤ 2)
    (S : Finset Coord) (hsupport : ∀ v ∈ V, ∀ x ∉ S, v x = 0)
    (hrank : 3 ≤ Module.finrank F V)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    Module.finrank F V + D ≤ S.card + 3 := by
  classical
  have hid := Submodule.finrank_sup_add_finrank_inf_eq V C
  have hCP := Submodule.finrank_sup_add_finrank_inf_eq C P
  have hle : Module.finrank F ↥(V ⊔ C) ≤ Module.finrank F ↥(C ⊔ P) :=
    Submodule.finrank_mono (sup_le hVP le_sup_left)
  have hdim : Module.finrank F V ≤ Module.finrank F ↥(V ⊓ C) + 2 := by
    omega
  have hpos : 0 < Module.finrank F ↥(V ⊓ C) := by omega
  have hbot : V ⊓ C ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simpa using hpos
  have hs : ∀ v ∈ V ⊓ C, ∀ x ∉ S, v x = 0 := by
    intro v hv
    exact hsupport v hv.1
  have hb := shortened_subspace_bound C (V ⊓ C) D hDpos inf_le_right S hs
    (Submodule.exists_mem_ne_zero_of_ne_bot hbot) hdistance
  omega

/-- Coordinates supported by at least two members of a finite family. -/
noncomputable def sharedSupport {I Coord : Type*} [Fintype I] [Fintype Coord]
    (Q : I → Finset Coord) : Finset Coord := by
  classical
  exact Finset.univ.filter (fun x => ∃ i j, i ≠ j ∧ x ∈ Q i ∧ x ∈ Q j)

/-- All components occurring in relations among a family of subspaces. -/
def relationComponents {F I Coord : Type*} [Field F] [Fintype I]
    (W : I → Submodule F (Coord → F)) : Set (Coord → F) :=
  {v | ∃ r : I → (Coord → F), (∀ i, r i ∈ W i) ∧
    (∑ i, r i) = 0 ∧ ∃ i, r i = v}

/-- A relation component cannot be nonzero on an exclusive coordinate. -/
theorem relation_component_shared_support {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (W : I → Submodule F (Coord → F)) (Q : I → Finset Coord)
    (hsupport : ∀ i, ∀ v ∈ W i, ∀ x ∉ Q i, v x = 0)
    (r : I → (Coord → F)) (hr : ∀ i, r i ∈ W i)
    (hsum : (∑ i, r i) = 0) (i : I) (x : Coord)
    (hx : x ∉ sharedSupport Q) : r i x = 0 := by
  classical
  by_cases hxi : x ∈ Q i
  · have hother : ∀ j, j ≠ i → r j x = 0 := by
      intro j hji
      apply hsupport j (r j) (hr j) x
      intro hxj
      apply hx
      simp only [sharedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, j, Ne.symm hji, hxi, hxj⟩
    have he : (∑ j, r j x) = r i x := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact hother j hji
      · simp
    have hz : (∑ j, r j x) = 0 := by
      simpa only [Finset.sum_apply, Pi.zero_apply] using
        congrArg (fun f : Coord → F => f x) hsum
    exact he.symm.trans hz
  · exact hsupport i (r i) (hr i) x hxi

/-- The span of all relation components is supported on shared coordinates. -/
theorem relation_core_shared_support {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (W : I → Submodule F (Coord → F)) (Q : I → Finset Coord)
    (hsupport : ∀ i, ∀ v ∈ W i, ∀ x ∉ Q i, v x = 0) :
    ∀ v ∈ Submodule.span F (relationComponents W),
      ∀ x ∉ sharedSupport Q, v x = 0 := by
  classical
  intro v hv x hx
  let ev : (Coord → F) →ₗ[F] F :=
    LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
  have hle : Submodule.span F (relationComponents W) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨r, hr, hsum, i, rfl⟩ := hw
    change r i x = 0
    exact relation_component_shared_support W Q hsupport r hr hsum i x hx
  exact hle hv

/-- Global shortening for the relation core of arbitrarily many pencils. -/
theorem relation_core_shortening {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (C P : Submodule F (Coord → F))
    (W : I → Submodule F (Coord → F)) (Q : I → Finset Coord)
    (D : ℕ) (hDpos : 0 < D) (hP : Module.finrank F P ≤ 2)
    (hW : ∀ i, W i ≤ C ⊔ P)
    (hsupport : ∀ i, ∀ v ∈ W i, ∀ x ∉ Q i, v x = 0)
    (hrank : 3 ≤ Module.finrank F (Submodule.span F (relationComponents W)))
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    Module.finrank F (Submodule.span F (relationComponents W)) + D ≤
      (sharedSupport Q).card + 3 := by
  have hcontain : Submodule.span F (relationComponents W) ≤ C ⊔ P := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨r, hr, hsum, i, rfl⟩ := hv
    exact hW i (hr i)
  exact received_space_shortening_bound C _ P D hDpos hcontain hP
    (sharedSupport Q) (relation_core_shared_support W Q hsupport) hrank hdistance

/-- Summation from the external product of a finite subspace family. -/
def familySum {F I Coord : Type*} [Field F] [Fintype I]
    (W : I → Submodule F (Coord → F)) :
    ((i : I) → W i) →ₗ[F] (Coord → F) where
  toFun r := ∑ i, (r i).val
  map_add' := by
    intro r s
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro a r
    simp [Finset.smul_sum]

/-- The image of the relation kernel at one member of the family. -/
def relationProjection {F I Coord : Type*} [Field F] [Fintype I]
    (W : I → Submodule F (Coord → F)) (i : I) :
    LinearMap.ker (familySum W) →ₗ[F] (Coord → F) where
  toFun r := (r.val i).val
  map_add' := by
    intros
    rfl
  map_smul' := by
    intros
    rfl

/-- Exact dimension of the global relation core, with no independence assumption. -/
theorem relation_core_dimension {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I]
    (W : I → Submodule F (Coord → F)) :
    Module.finrank F (Submodule.span F (relationComponents W)) +
      Module.finrank F (LinearMap.ker (familySum W)) =
      ∑ i, Module.finrank F (LinearMap.range (relationProjection W i)) := by
  classical
  let U : I → Submodule F (Coord → F) :=
    fun i => LinearMap.range (relationProjection W i)
  have hUW : ∀ i, U i ≤ W i := by
    intro i v hv
    obtain ⟨r, rfl⟩ := hv
    exact (r.val i).property
  let emb : ((i : I) → U i) →ₗ[F] ((i : I) → W i) :=
    { toFun := fun r i => ⟨(r i).val, hUW i (r i).property⟩
      map_add' := by
        intros
        rfl
      map_smul' := by
        intros
        rfl }
  let ke : LinearMap.ker (familySum U) →ₗ[F] LinearMap.ker (familySum W) :=
    { toFun := fun r => ⟨emb r.val, r.property⟩
      map_add' := by
        intros
        rfl
      map_smul' := by
        intros
        rfl }
  have hki : Function.Injective ke := by
    intro r s h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker (familySum W) => (z.val i).val) h
  have hks : Function.Surjective ke := by
    intro r
    let s : (i : I) → U i := fun i =>
      ⟨(r.val i).val, ⟨r, rfl⟩⟩
    refine ⟨⟨s, r.property⟩, ?_⟩
    apply Subtype.ext
    funext i
    rfl
  have hkdim : Module.finrank F (LinearMap.ker (familySum U)) =
      Module.finrank F (LinearMap.ker (familySum W)) :=
    (LinearEquiv.ofBijective ke ⟨hki, hks⟩).finrank_eq
  have hrange : LinearMap.range (familySum U) =
      Submodule.span F (relationComponents W) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨r, rfl⟩ := hv
      apply Submodule.sum_mem
      intro i hi
      obtain ⟨s, hs⟩ := (r i).property
      apply Submodule.subset_span
      refine ⟨fun j => (s.val j).val, fun j => (s.val j).property, ?_, i, hs⟩
      exact s.property
    · apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨r, hr, hsum, i, rfl⟩ := hv
      let s : LinearMap.ker (familySum W) :=
        ⟨fun j => ⟨r j, hr j⟩, hsum⟩
      let a : U i := ⟨r i, ⟨s, rfl⟩⟩
      let b : (j : I) → U j := Pi.single i a
      refine ⟨b, ?_⟩
      change (∑ j, (b j).val) = r i
      rw [Finset.sum_eq_single i]
      · simp [b, a]
      · intro j hj hji
        simp [b, Pi.single_eq_of_ne hji]
      · simp
  have hrn := LinearMap.finrank_range_add_finrank_ker (familySum U)
  rw [hrange, hkdim, Module.finrank_pi_fintype] at hrn
  exact hrn

/-- Global multi-line rank/shortening inequality in projected-kernel dimensions. -/
theorem projected_relation_shortening {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (C P : Submodule F (Coord → F))
    (W : I → Submodule F (Coord → F)) (Q : I → Finset Coord)
    (D : ℕ) (hDpos : 0 < D) (hP : Module.finrank F P ≤ 2)
    (hW : ∀ i, W i ≤ C ⊔ P)
    (hsupport : ∀ i, ∀ v ∈ W i, ∀ x ∉ Q i, v x = 0)
    (hactive : Module.finrank F (LinearMap.ker (familySum W)) + 3 ≤
      ∑ i, Module.finrank F (LinearMap.range (relationProjection W i)))
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    (∑ i, Module.finrank F (LinearMap.range (relationProjection W i))) + D ≤
      (sharedSupport Q).card + 3 +
        Module.finrank F (LinearMap.ker (familySum W)) := by
  have hid := relation_core_dimension W
  have hrank : 3 ≤ Module.finrank F (Submodule.span F (relationComponents W)) := by
    omega
  have hs := relation_core_shortening C P W Q D hDpos hP hW hsupport hrank hdistance
  omega

/-- Shared coordinates consume at least two incidences in the support ledger. -/
theorem shared_support_incidence_budget {I Coord : Type*}
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (Q : I → Finset Coord) :
    2 * (sharedSupport Q).card ≤ ∑ i, (Q i).card := by
  classical
  have hpoint : ∀ x : Coord,
      (if x ∈ sharedSupport Q then 2 else 0) ≤
        ∑ i : I, if x ∈ Q i then 1 else 0 := by
    intro x
    by_cases hx : x ∈ sharedSupport Q
    · obtain ⟨i, j, hij, hxi, hxj⟩ :
          ∃ i j, i ≠ j ∧ x ∈ Q i ∧ x ∈ Q j := by
        simpa [sharedSupport] using hx
      have hp := Finset.sum_le_sum_of_subset
        (f := fun i : I => if x ∈ Q i then (1 : ℕ) else 0)
        (Finset.subset_univ ({i, j} : Finset I))
      rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton] at hp
      simpa only [if_pos hx, if_pos hxi, if_pos hxj] using hp
    · simp only [if_neg hx]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hs
  simpa [Finset.sum_ite, mul_comm] using hs

/-- Global relation shortening expressed directly in the total support budget. -/
theorem projected_relation_incidence_budget {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (C P : Submodule F (Coord → F))
    (W : I → Submodule F (Coord → F)) (Q : I → Finset Coord)
    (D : ℕ) (hDpos : 0 < D) (hP : Module.finrank F P ≤ 2)
    (hW : ∀ i, W i ≤ C ⊔ P)
    (hsupport : ∀ i, ∀ v ∈ W i, ∀ x ∉ Q i, v x = 0)
    (hactive : Module.finrank F (LinearMap.ker (familySum W)) + 3 ≤
      ∑ i, Module.finrank F (LinearMap.range (relationProjection W i)))
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    2 * ((∑ i, Module.finrank F (LinearMap.range (relationProjection W i))) + D) ≤
      (∑ i, (Q i).card) + 6 +
        2 * Module.finrank F (LinearMap.ker (familySum W)) := by
  have hr := projected_relation_shortening C P W Q D hDpos hP hW
    hsupport hactive hdistance
  have hi := shared_support_incidence_budget Q
  omega

/-- A short full-support relation between actual decoding errors forces every
decoded head onto one affine line. No rank-activity hypothesis is required. -/
theorem affine_heads_of_small_error_relation {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (C : Submodule F (Coord → F)) (u₀ u₁ : Coord → F)
    (w : I → (Coord → F)) (γ c : I → F) (Q : I → Finset Coord)
    (D t : ℕ) (hw : ∀ i, w i ∈ C) (hc : ∀ i, c i ≠ 0)
    (hagree : ∀ i x, x ∉ Q i → w i x = u₀ x + γ i * u₁ x)
    (hweight : ∀ i, (Q i).card ≤ t)
    (hsmall : Fintype.card I * t < 2 * D)
    (hrel : (∑ i, c i • (u₀ + γ i • u₁ - w i)) = 0)
    (i₀ i₁ : I) (hγ : γ i₀ ≠ γ i₁)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    ∃ U V, U ∈ C ∧ V ∈ C ∧ ∀ i, w i = U + γ i • V := by
  classical
  let S := sharedSupport Q
  have houtside : ∀ i x, x ∉ S → w i x = u₀ x + γ i * u₁ x := by
    intro i x hx
    by_cases hxi : x ∈ Q i
    · have hj : ∀ j, j ≠ i → x ∉ Q j := by
        intro j hji hxj
        apply hx
        simp only [S, sharedSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, j, Ne.symm hji, hxi, hxj⟩
      have hz : (∑ j, c j * (u₀ x + γ j * u₁ x - w j x)) = 0 := by
        have he := congrArg (fun v : Coord → F => v x) hrel
        simpa using he
      have he : (∑ j, c j * (u₀ x + γ j * u₁ x - w j x)) =
          c i * (u₀ x + γ i * u₁ x - w i x) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hagree j x (hj j hji)]
          ring
        · simp
      rw [he] at hz
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hc i))).symm
    · exact hagree i x hxi
  have hcard : S.card < D := by
    have hi := shared_support_incidence_budget Q
    have hwgt := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hweight i)
    have hsum : (∑ _i : I, t) = Fintype.card I * t := by simp
    rw [hsum] at hwgt
    change 2 * S.card ≤ _ at hi
    omega
  let V := (γ i₀ - γ i₁)⁻¹ • (w i₀ - w i₁)
  let U := w i₀ - γ i₀ • V
  have hVC : V ∈ C := C.smul_mem _ (C.sub_mem (hw i₀) (hw i₁))
  have hUC : U ∈ C := C.sub_mem (hw i₀) (C.smul_mem _ hVC)
  have hV : ∀ x ∉ S, V x = u₁ x := by
    intro x hx
    have hd : w i₀ x - w i₁ x = (γ i₀ - γ i₁) * u₁ x := by
      rw [houtside i₀ x hx, houtside i₁ x hx]
      ring
    change (γ i₀ - γ i₁)⁻¹ * (w i₀ x - w i₁ x) = u₁ x
    rw [hd, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hγ), one_mul]
  have hU : ∀ x ∉ S, U x = u₀ x := by
    intro x hx
    change w i₀ x - γ i₀ * V x = u₀ x
    rw [hV x hx, houtside i₀ x hx]
    ring
  refine ⟨U, V, hUC, hVC, ?_⟩
  intro i
  apply sub_eq_zero.mp
  apply hdistance _ (C.sub_mem (hw i) (C.add_mem hUC (C.smul_mem _ hVC))) S hcard
  intro x hx
  change w i x - (U x + γ i * V x) = 0
  rw [houtside i x hx, hU x hx, hV x hx]
  ring

/-- Error plane of an affine family of decoded heads. -/
def affineErrorPlane {F Coord : Type*} [Field F]
    (u₀ u₁ U V : Coord → F) : Submodule F (Coord → F) :=
  Submodule.span F {u₀ - U, u₁ - V}

noncomputable def affineErrorSupport {F Coord : Type*} [Field F] [Fintype Coord]
    (u₀ u₁ U V : Coord → F) : Finset Coord := by
  classical
  exact Finset.univ.filter (fun x => u₀ x ≠ U x ∨ u₁ x ≠ V x)

/-- Two distinct decoded code heads force both affine parameters into the code. -/
theorem affine_parameters_mem_code {F Coord : Type*} [Field F]
    (C : Submodule F (Coord → F)) (U V : Coord → F) (a b : F)
    (hab : a ≠ b) (ha : U + a • V ∈ C) (hb : U + b • V ∈ C) :
    U ∈ C ∧ V ∈ C := by
  have hdiff : (a - b) • V ∈ C := by
    have h := C.sub_mem ha hb
    have he : (a - b) • V = (U + a • V) - (U + b • V) := by
      rw [sub_smul]
      abel
    rwa [← he] at h
  have hV : V ∈ C := by
    have h := C.smul_mem (a - b)⁻¹ hdiff
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] at h
  have hU := C.sub_mem ha (C.smul_mem a hV)
  constructor
  · simpa using hU
  · exact hV

/-- Affine error planes have their explicit coefficient support. -/
theorem affine_error_plane_support {F Coord : Type*} [Field F] [Fintype Coord]
    (u₀ u₁ U V : Coord → F) :
    ∀ v ∈ affineErrorPlane u₀ u₁ U V,
      ∀ x ∉ affineErrorSupport u₀ u₁ U V, v x = 0 := by
  classical
  intro v hv x hx
  have hzero : u₀ x = U x ∧ u₁ x = V x := by
    simpa [affineErrorSupport, not_or] using hx
  let ev : (Coord → F) →ₗ[F] F :=
    LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
  have hle : affineErrorPlane u₀ u₁ U V ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · change u₀ x - U x = 0
      exact sub_eq_zero.mpr hzero.1
    · change u₁ x - V x = 0
      exact sub_eq_zero.mpr hzero.2
  exact hle hv

/-- The projected-kernel inequality for actual affine decoded code heads.
Received-space containment and shared support are derived from the heads. -/
theorem affine_head_relation_shortening {F I Coord : Type*} [Field F]
    [Fintype I] [Fintype Coord] [DecidableEq I] [DecidableEq Coord]
    (C : Submodule F (Coord → F)) (u₀ u₁ : Coord → F)
    (U V : I → (Coord → F)) (a b : I → F)
    (hab : ∀ i, a i ≠ b i)
    (ha : ∀ i, U i + a i • V i ∈ C)
    (hb : ∀ i, U i + b i • V i ∈ C)
    (D : ℕ) (hDpos : 0 < D)
    (hactive : Module.finrank F (LinearMap.ker
        (familySum (fun i => affineErrorPlane u₀ u₁ (U i) (V i)))) + 3 ≤
      ∑ i, Module.finrank F (LinearMap.range
        (relationProjection (fun j => affineErrorPlane u₀ u₁ (U j) (V j)) i)))
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    (∑ i, Module.finrank F (LinearMap.range
      (relationProjection (fun j => affineErrorPlane u₀ u₁ (U j) (V j)) i))) + D ≤
      (sharedSupport (fun i => affineErrorSupport u₀ u₁ (U i) (V i))).card + 3 +
      Module.finrank F (LinearMap.ker
        (familySum (fun i => affineErrorPlane u₀ u₁ (U i) (V i)))) := by
  classical
  let P : Submodule F (Coord → F) := Submodule.span F {u₀, u₁}
  have hP : Module.finrank F P ≤ 2 := by
    have h₁ := finrank_span_le_card (R := F) ({u₀, u₁} : Set (Coord → F))
    have h₂ : ({u₀, u₁} : Set (Coord → F)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (by simp)
    exact h₁.trans h₂
  have hW : ∀ i, affineErrorPlane u₀ u₁ (U i) (V i) ≤ C ⊔ P := by
    intro i
    obtain ⟨hU, hV⟩ := affine_parameters_mem_code C (U i) (V i)
      (a i) (b i) (hab i) (ha i) (hb i)
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact (C ⊔ P).sub_mem
        ((show P ≤ C ⊔ P from le_sup_right) (Submodule.subset_span (by simp)))
        ((show C ≤ C ⊔ P from le_sup_left) hU)
    · exact (C ⊔ P).sub_mem
        ((show P ≤ C ⊔ P from le_sup_right) (Submodule.subset_span (by simp)))
        ((show C ≤ C ⊔ P from le_sup_left) hV)
  exact projected_relation_shortening C P _ _ D hDpos hP hW
    (fun i => affine_error_plane_support u₀ u₁ (U i) (V i)) hactive hdistance

noncomputable def affineHeadErrors {F Coord : Type*} [Field F] [Fintype Coord]
    (u₀ u₁ U V : Coord → F) (a : F) : Finset Coord := by
  classical
  exact Finset.univ.filter (fun x => u₀ x + a * u₁ x ≠ U x + a * V x)

/-- The plane support lies in the union of errors of any two distinct heads. -/
theorem affine_support_pair_cover {F Coord : Type*} [Field F] [Fintype Coord]
    [DecidableEq Coord]
    (u₀ u₁ U V : Coord → F) (a b : F) (hab : a ≠ b) :
    affineErrorSupport u₀ u₁ U V ⊆
      affineHeadErrors u₀ u₁ U V a ∪ affineHeadErrors u₀ u₁ U V b := by
  classical
  intro x hx
  by_contra hnot
  have hpair : x ∉ affineHeadErrors u₀ u₁ U V a ∧
      x ∉ affineHeadErrors u₀ u₁ U V b := by
    simpa only [Finset.mem_union, not_or] using hnot
  have ha : u₀ x + a * u₁ x = U x + a * V x := by
    simpa [affineHeadErrors] using hpair.1
  have hb : u₀ x + b * u₁ x = U x + b * V x := by
    simpa [affineHeadErrors] using hpair.2
  have he : (a - b) * (u₁ x - V x) = 0 := by
    linear_combination ha - hb
  have h₁ : u₁ x = V x :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab))
  have h₀ : u₀ x = U x := by
    rw [h₁] at ha
    exact add_right_cancel ha
  simpa [affineErrorSupport, h₀, h₁] using hx

/-- A set covered by every pair of three sets has incidence at least twice its size. -/
theorem three_pair_cover_card {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (Q : Finset Coord) (E : Fin 3 → Finset Coord)
    (hpair : ∀ i j, i ≠ j → Q ⊆ E i ∪ E j) :
    2 * Q.card ≤ ∑ i, (E i).card := by
  classical
  have hpoint : ∀ x : Coord,
      (if x ∈ Q then 2 else 0) ≤ ∑ i : Fin 3, if x ∈ E i then 1 else 0 := by
    intro x
    by_cases hx : x ∈ Q
    · have h₀₁ := hpair 0 1 (by decide) hx
      have h₀₂ := hpair 0 2 (by decide) hx
      have h₁₂ := hpair 1 2 (by decide) hx
      simp only [Finset.mem_union] at h₀₁ h₀₂ h₁₂
      simp only [if_pos hx, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      split_ifs
      all_goals simp_all
    · simp only [if_neg hx]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hs
  simpa [Finset.sum_ite, mul_comm] using hs

/-- Three distinct nearby heads control the entire error-plane support. -/
theorem three_head_support_budget {F Coord : Type*} [Field F] [Fintype Coord]
    [DecidableEq Coord] (u₀ u₁ U V : Coord → F)
    (a : Fin 3 → F) (ha : Function.Injective a) (t : ℕ)
    (herrors : ∀ i, (affineHeadErrors u₀ u₁ U V (a i)).card ≤ t) :
    2 * (affineErrorSupport u₀ u₁ U V).card ≤ 3 * t := by
  have hp := three_pair_cover_card (affineErrorSupport u₀ u₁ U V)
    (fun i => affineHeadErrors u₀ u₁ U V (a i))
    (fun i j hij => affine_support_pair_cover u₀ u₁ U V (a i) (a j)
      (fun h => hij (ha h)))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => herrors i)
  have hc : (∑ _i : Fin 3, t) = 3 * t := by simp
  rw [hc] at hs
  exact hp.trans hs

/-- Universal coordinate-count inequality for a minimal multi-line dependency. -/
theorem coordinate_count_bound (L a k : ℤ)
    (hL : 4 ≤ L) (ha : 1 ≤ a) (haL : a ≤ L)
    (hk : 0 ≤ k) (hka : k ≤ a) :
    2 * (3*L*(L-1)-3*(L-a)*(L-a-1)-k*(L-a)) ≤
      (5*L-7)*(3*a-k)+4*(if a=1 ∧ k=1 then 1 else 0) := by
  by_cases ha1 : a = 1
  · subst a
    by_cases hk1 : k = 1
    · subst k
      simp only [and_self, ↓reduceIte]
      nlinarith
    · have hk0 : k = 0 := by omega
      subst k
      norm_num
      nlinarith
  · have ha2 : 2 ≤ a := by omega
    have hfirst : 0 ≤ a*(a-2) := mul_nonneg (by omega) (by omega)
    have hsecond : 0 ≤ (3*L+2*a-7)*(a-k) :=
      mul_nonneg (by omega) (by omega)
    have hnot : ¬ (a=1 ∧ k=1) := by tauto
    simp only [if_neg hnot]
    nlinarith [hfirst, hsecond]

/-- Arithmetic transfer after codeword averaging and shared-support shortening.
The two structural inputs are explicit and are not proved by this declaration. -/
theorem dependency_necessary (L D t n E S : ℤ)
    (haverage : 6*L*(L-1)*D ≤ 3*L*(5*L-7)*t+4*E)
    (hshared : D+L-4 ≤ S) (hambient : E+S ≤ n) :
    (6*L*(L-1)+4)*D ≤ 3*L*(5*L-7)*t+4*(n-L+4) := by
  nlinarith

/-- Finite-coordinate ledger. Codeword-distance, error-budget and shortening
inputs remain explicit until the canonical witness construction is connected. -/
theorem dependency_from_coordinate_ledger {X : Type*} (U : Finset X)
    (L D t n E S : ℤ) (a k b : X → ℤ) (hL : 4 ≤ L)
    (hcoord : ∀ x ∈ U, 1 ≤ a x ∧ a x ≤ L ∧ 0 ≤ k x ∧ k x ≤ a x)
    (hcount : ∀ x ∈ U, b x ≤
      3*L*(L-1)-3*(L-a x)*(L-a x-1)-k x*(L-a x))
    (hdistance : 3*L*(L-1)*D ≤ ∑ x ∈ U, b x)
    (herrors : (∑ x ∈ U, (3*a x-k x)) ≤ 3*L*t)
    (hexclusive : (∑ x ∈ U, (if a x=1 ∧ k x=1 then (1 : ℤ) else 0)) ≤ E)
    (hshared : D+L-4 ≤ S) (hambient : E+S ≤ n) :
    (6*L*(L-1)+4)*D ≤ 3*L*(5*L-7)*t+4*(n-L+4) := by
  have hpoint : ∀ x ∈ U, 2*b x ≤
      (5*L-7)*(3*a x-k x)+4*(if a x=1 ∧ k x=1 then (1 : ℤ) else 0) := by
    intro x hx
    obtain ⟨ha, haL, hk, hka⟩ := hcoord x hx
    have hc := coordinate_count_bound L (a x) (k x) hL ha haL hk hka
    have hb := hcount x hx
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have herrors' := mul_le_mul_of_nonneg_left herrors (show 0 ≤ 5*L-7 by omega)
  have havg : 6*L*(L-1)*D ≤ 3*L*(5*L-7)*t+4*E := by
    nlinarith [hdistance, herrors', hexclusive]
  exact dependency_necessary L D t n E S havg hshared hambient

/-- Literal integer exclusion, conditional on the necessary inequality above. -/
theorem literal_dependency_excluded (L : ℤ) (hlo : 4 ≤ L) (hhi : L ≤ 12) :
    ¬ ((6*L*(L-1)+4)*536870913 ≤
      3*L*(5*L-7)*221512373+4*(1073741824-L+4)) := by
  interval_cases L
  all_goals norm_num

end ProximityGap.IncidenceDependencyArithmetic

#print axioms ProximityGap.IncidenceDependencyArithmetic.coordinate_count_bound
#print axioms ProximityGap.IncidenceDependencyArithmetic.shortened_subspace_bound
#print axioms ProximityGap.IncidenceDependencyArithmetic.dependency_necessary
#print axioms ProximityGap.IncidenceDependencyArithmetic.dependency_from_coordinate_ledger
#print axioms ProximityGap.IncidenceDependencyArithmetic.literal_dependency_excluded
#print axioms ProximityGap.IncidenceDependencyArithmetic.quotient_shortening_bound
#print axioms ProximityGap.IncidenceDependencyArithmetic.received_space_shortening_bound
#print axioms ProximityGap.IncidenceDependencyArithmetic.relation_component_shared_support
#print axioms ProximityGap.IncidenceDependencyArithmetic.relation_core_shared_support
#print axioms ProximityGap.IncidenceDependencyArithmetic.relation_core_shortening
#print axioms ProximityGap.IncidenceDependencyArithmetic.relation_core_dimension
#print axioms ProximityGap.IncidenceDependencyArithmetic.projected_relation_shortening
#print axioms ProximityGap.IncidenceDependencyArithmetic.affine_parameters_mem_code
#print axioms ProximityGap.IncidenceDependencyArithmetic.affine_error_plane_support
#print axioms ProximityGap.IncidenceDependencyArithmetic.affine_head_relation_shortening
#print axioms ProximityGap.IncidenceDependencyArithmetic.affine_support_pair_cover
#print axioms ProximityGap.IncidenceDependencyArithmetic.three_pair_cover_card
#print axioms ProximityGap.IncidenceDependencyArithmetic.three_head_support_budget
#print axioms ProximityGap.IncidenceDependencyArithmetic.shared_support_incidence_budget
#print axioms ProximityGap.IncidenceDependencyArithmetic.projected_relation_incidence_budget
#print axioms ProximityGap.IncidenceDependencyArithmetic.affine_heads_of_small_error_relation
