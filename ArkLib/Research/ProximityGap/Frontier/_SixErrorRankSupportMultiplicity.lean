/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Coordinate support forced by low rank

If every `r` members of an `n`-vector family are linearly independent while
the full span has dimension at most `r`, each active coordinate must occur in
at least `n - r + 1` vectors. Summing this multiplicity yields a support-mass
lower bound. At `n = 6` and `r = 4`, this is the rank-four obstruction used in
six-error circuit analysis. A separate finite-field lemma produces one
subspace vector whose support is exactly the union of all active coordinates.
The rank-support statement is a necessary condition, not an independence result.
-/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.SixErrorRankSupportMultiplicity

/-- A rank-`r` family of `r + 1` vectors whose every deletion is independent has a dependence
with every coefficient nonzero. This is the circuit relation needed to pass from rank information
to full-support error relations. -/
theorem full_support_relation_of_rank
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {r : ℕ} (e : Fin (r + 1) → V)
    (hLI : ∀ i : Fin (r + 1),
      LinearIndependent F (fun j : Fin r => e (i.succAbove j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r) :
    ∃ c : Fin (r + 1) → F,
      (∑ i, c i • e i = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  have hnot : ¬ LinearIndependent F e := by
    intro hlin
    have hspan := hrank
    rw [finrank_span_eq_card hlin] at hspan
    simp only [Fintype.card_fin] at hspan
    omega
  obtain ⟨c, hsum, hc⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨c, hsum, ?_⟩
  intro i
  by_contra hci_ne
  have hci : c i = 0 := by simpa using hci_ne
  let b : Fin r → Fin (r + 1) := i.succAbove
  have hb : Function.Injective b := Fin.succAbove_right_injective
  have hImage : Finset.univ.image b = Finset.univ.erase i := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, _hk, rfl⟩
      exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injective _ hb]
      simp
  have hsumErase :
      (∑ j ∈ Finset.univ.erase i, c j • e j) = 0 := by
    have hsplit := Finset.sum_erase_add Finset.univ (fun j => c j • e j)
      (Finset.mem_univ i)
    rw [hsum] at hsplit
    simpa [hci] using hsplit
  have hsumImage :
      (∑ j ∈ Finset.univ.image b, c j • e j) =
        ∑ j : Fin r, c (b j) • e (b j) := by
    rw [Finset.sum_image (fun j _ k _ hjk => hb hjk)]
  have hsumB : (∑ j : Fin r, c (b j) • e (b j)) = 0 := by
    rw [← hsumImage, hImage]
    exact hsumErase
  have hcoeff : ∀ j : Fin r, c (b j) = 0 := by
    have hz := Fintype.linearIndependent_iff.mp (hLI i) (fun j => c (b j)) hsumB
    intro j
    simpa using hz j
  have hcAll : ∀ j : Fin (r + 1), c j = 0 := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using hci
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
      rw [← hk]
      exact hcoeff k
  rcases hc with ⟨j, hj⟩
  exact hj (hcAll j)

/-- In a subspace of a finite coordinate space, if the field is larger than the set of active
coordinates, one vector is nonzero at every active coordinate. Every vector in the subspace
vanishes at inactive coordinates by definition, so this vector has support exactly equal to the
union of supports of the subspace. -/
theorem full_support_vector_of_active_submodule
    {F I : Type*} [Field F] [Fintype F] [Fintype I]
    (R : Submodule F (I → F))
    (hcard : (Finset.univ.filter
      (fun i => ∃ v : R, (v : I → F) i ≠ 0)).card < Fintype.card F) :
    ∃ v : R, ∀ i,
      (∃ w : R, (w : I → F) i ≠ 0) ↔ (v : I → F) i ≠ 0 := by
  classical
  let active : I → Prop := fun i => ∃ w : R, (w : I → F) i ≠ 0
  let A : Finset I := Finset.univ.filter active
  have hstep : ∀ s : Finset I, (∀ i ∈ s, active i) →
      ∃ v : R, ∀ i ∈ s, (v : I → F) i ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, by simp⟩
    | @insert i s hi ih =>
        intro hs
        obtain ⟨v, hv⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
        obtain ⟨w, hw⟩ := hs i (Finset.mem_insert_self i s)
        let bad := (insert i s).image (fun j =>
          if (w : I → F) j = 0 then 0 else -(v : I → F) j / (w : I → F) j)
        have hsub : insert i s ⊆ A := by
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs j hj⟩
        have hbad : bad.card < Fintype.card F := by
          calc
            bad.card ≤ (insert i s).card := Finset.card_image_le
            _ ≤ A.card := Finset.card_le_card hsub
            _ < Fintype.card F := by simpa [A, active] using hcard
        have hbadCompl : 0 < badᶜ.card := by
          rw [Finset.card_compl]
          omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hbadCompl
        have haBad : a ∉ bad := by simpa using ha
        have hnew : ∀ j ∈ insert i s, (v : I → F) j + a * (w : I → F) j ≠ 0 := by
          intro j hj hzero
          have hvj : (v : I → F) j ≠ 0 ∨ j = i := by
            rcases Finset.mem_insert.mp hj with hji | hjs
            · exact Or.inr hji
            · exact Or.inl (hv j hjs)
          by_cases hwj : (w : I → F) j = 0
          · rcases hvj with hvj | hji
            · exact hvj (by simpa [hwj] using hzero)
            · subst j
              exact hw hwj
          · have haEq : a = -(v : I → F) j / (w : I → F) j := by
              have hmul : a * (w : I → F) j = -(v : I → F) j := by
                linear_combination hzero
              calc
                a = (a * (w : I → F) j) / (w : I → F) j := by field_simp [hwj]
                _ = -(v : I → F) j / (w : I → F) j := by rw [hmul]
            apply haBad
            apply Finset.mem_image.mpr
            exact ⟨j, hj, by simp [hwj, haEq]⟩
        refine ⟨v + a • w, ?_⟩
        intro j hj
        simpa using hnew j hj
  have hactive : ∀ i ∈ A, active i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨v, hv⟩ := hstep A hactive
  refine ⟨v, ?_⟩
  intro i
  constructor
  · intro hi
    exact hv i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  · intro hi
    exact ⟨v, hi⟩

/-- If every member of a finite vector family participates in some linear dependence, and the
field has more elements than the family has members, then one dependence has full support.
This is the finite-field hyperplane-avoidance step that converts coordinatewise activity into a
single relation usable by affine-head collapse arguments. -/
theorem full_support_relation_of_active_coordinates
    {F V I : Type*} [Field F] [Fintype F] [Fintype I]
    [AddCommGroup V] [Module F V]
    (e : I → V) (hcard : Fintype.card I < Fintype.card F)
    (hactive : ∀ i, ∃ c : I → F, (∑ j, c j • e j = 0) ∧ c i ≠ 0) :
    ∃ c : I → F, (∑ j, c j • e j = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  let relationMap : (I → F) →ₗ[F] V :=
    { toFun := fun c => ∑ i, c i • e i
      map_add' := by
        intro c d
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp [smul_eq_mul, Finset.smul_sum, mul_smul] }
  let R : Submodule F (I → F) := LinearMap.ker relationMap
  have hcardActive : (Finset.univ.filter
      (fun i => ∃ c : R, (c : I → F) i ≠ 0)).card < Fintype.card F := by
    calc
      _ ≤ Fintype.card I := Finset.card_le_univ _
      _ < Fintype.card F := hcard
  have hactiveR : ∀ i, ∃ c : R, (c : I → F) i ≠ 0 := by
    intro i
    obtain ⟨c, hc, hci⟩ := hactive i
    refine ⟨⟨c, ?_⟩, hci⟩
    change relationMap c = 0
    simpa [relationMap] using hc
  obtain ⟨c, hc⟩ := full_support_vector_of_active_submodule R hcardActive
  have hcRel : (∑ i, (c : I → F) i • e i) = 0 := c.property
  exact ⟨c, hcRel, fun i => (hc i).mp (hactiveR i)⟩

/-- If every `r` vectors are independent and the whole family has rank at
most `r`, an active coordinate occurs in at least `n - r + 1` vectors. -/
theorem rank_coordinate_multiplicity
    {F Coord : Type} [Field F] [Fintype Coord] {n r : ℕ}
    (hrn : r ≤ n) (e : Fin n → (Coord → F))
    (hLI : ∀ b : Fin r → Fin n, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r)
    (x : Coord) (hactive : ∃ j, e j x ≠ 0)
    (N : Finset (Fin n)) (hNmem : ∀ j, j ∈ N ↔ e j x ≠ 0) :
    n - r + 1 ≤ N.card := by
  classical
  by_contra hn
  let Z := {j : Fin n // e j x = 0}
  have hN : Fintype.card {j : Fin n // ¬ e j x = 0} ≤ n - r := by
    rw [Fintype.card_of_subtype (p := fun j : Fin n => ¬ e j x = 0) N hNmem]
    omega
  have hcomp := Fintype.card_subtype_compl (fun j : Fin n => e j x = 0)
  have hZle := Fintype.card_subtype_le (fun j : Fin n => e j x = 0)
  have hZcard : r ≤ Fintype.card Z := by
    simp only [Fintype.card_fin] at hcomp hZle
    dsimp [Z]
    omega
  let bz : Fin r → Z := fun j =>
    (Fintype.equivFin Z).symm (Fin.castLE hZcard j)
  let b : Fin r → Fin n := fun j => (bz j).val
  have hb : Function.Injective b := by
    intro i j hij
    have hs : bz i = bz j := Subtype.ext hij
    have hf : Fin.castLE hZcard i = Fin.castLE hZcard j :=
      (Fintype.equivFin Z).symm.injective hs
    apply Fin.ext
    exact congrArg (fun k : Fin (Fintype.card Z) => k.val) hf
  have hLIb := hLI b hb
  have hspan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      Submodule.span F (Set.range e) := by
    apply Submodule.span_mono
    rintro z ⟨j, rfl⟩
    exact ⟨b j, rfl⟩
  have heq := Submodule.eq_of_le_of_finrank_le hspan (by
    rw [finrank_span_eq_card hLIb]
    simpa using hrank)
  let ev : (Coord → F) →ₗ[F] F :=
    LinearMap.proj (R := F) (φ := fun _ : Coord => F) x
  have hvan : Submodule.span F (Set.range (fun j => e (b j))) ≤
      LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact (bz j).property
  obtain ⟨k, hk⟩ := hactive
  apply hk
  have hm : e k ∈ Submodule.span F (Set.range (fun j => e (b j))) := by
    rw [heq]
    exact Submodule.subset_span ⟨k, rfl⟩
  exact hvan hm

/-- The coordinate multiplicity forces `n - r + 1` incidences per active
coordinate, even when supplied supports include coordinates where a vector
vanishes. -/
theorem rank_support_mass
    {F Coord : Type} [Field F] [Fintype Coord] [DecidableEq Coord]
    {n r : ℕ} (hrn : r ≤ n) (e : Fin n → (Coord → F)) (Q : Fin n → Finset Coord)
    (hsupport : ∀ j, ∀ x ∉ Q j, e j x = 0)
    (hLI : ∀ b : Fin r → Fin n, Function.Injective b →
      LinearIndependent F (fun j => e (b j)))
    (hrank : Module.finrank F (Submodule.span F (Set.range e)) ≤ r) :
    (n - r + 1) * (Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)).card ≤
      ∑ j, (Q j).card := by
  classical
  let S := Finset.univ.filter (fun x => ∃ j, e j x ≠ 0)
  have hpoint : ∀ x : Coord, (if x ∈ S then n - r + 1 else 0) ≤
      ∑ j : Fin n, if x ∈ Q j then 1 else 0 := by
    intro x
    by_cases hx : x ∈ S
    · have hmul := rank_coordinate_multiplicity hrn e hLI hrank x
        ((Finset.mem_filter.mp hx).2)
        (Finset.univ.filter (fun j => e j x ≠ 0)) (fun j => by simp)
      have hcount : (Finset.univ.filter (fun j : Fin n => e j x ≠ 0)).card ≤
          ∑ j : Fin n, if x ∈ Q j then 1 else 0 := by
        rw [Finset.card_filter]
        apply Finset.sum_le_sum
        intro j _
        by_cases he : e j x = 0
        · simp [he]
        · have hxQ : x ∈ Q j := by
            by_contra h
            exact he (hsupport j x h)
          simp [he, hxQ]
      simpa only [if_pos hx] using hmul.trans hcount
    · simp only [if_neg hx]
      exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hs
  simpa [S, Finset.sum_ite, mul_comm] using hs

end ProximityGap.SixErrorRankSupportMultiplicity

#print axioms ProximityGap.SixErrorRankSupportMultiplicity.rank_coordinate_multiplicity
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.rank_support_mass
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.full_support_relation_of_rank
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.full_support_relation_of_active_coordinates
#print axioms ProximityGap.SixErrorRankSupportMultiplicity.full_support_vector_of_active_submodule
