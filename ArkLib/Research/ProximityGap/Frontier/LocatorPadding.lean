/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ReedSolomon
import CompPoly.ToMathlib.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

/-! # Extending an MCA witness by a prescribed number of zero coordinates

Multiplication by the nodal polynomial adds the selected new sites to every
agreement set. A joint explanation would vanish at those sites and hence
would divide by the same polynomial to give a joint explanation downstairs.
Other coordinates in the larger domain need not enter the agreement set.
-/

namespace ProximityGap.LocatorPadding

open Polynomial Finset
open scoped NNReal ENNReal

variable {I J F : Type} [Field F] [Nonempty J]

/-- Multiply the old row by the nodal polynomial on the chosen new sites. -/
noncomputable def extendWord (old : J ↪ I) (D : I ↪ F) (Z : Finset I) (u : J → F) (i : I) : F :=
  (Lagrange.nodal Z D).eval (D i) * u (Function.invFun old i)

private theorem extend_old (old : J ↪ I) (D : I ↪ F) (Z : Finset I) (u : J → F) (j : J) :
    extendWord old D Z u (old j) = (Lagrange.nodal Z D).eval (D (old j)) * u j := by
  rw [extendWord, Function.leftInverse_invFun old.injective j]

private theorem extend_zero (old : J ↪ I) (D : I ↪ F) (Z : Finset I) (u : J → F) {i : I}
    (hi : i ∈ Z) : extendWord old D Z u i = 0 := by
  rw [extendWord, Lagrange.eval_nodal_at_node hi, zero_mul]

private theorem shorten [DecidableEq I] (old : J ↪ I) (D : I ↪ F) (Z : Finset I)
    (fresh : ∀ j, old j ∉ Z) {k : ℕ} (hk : 0 < k) (u : J → F) (S : Finset J) (v : I → F)
    (hv : v ∈ ReedSolomon.code D (k + Z.card))
    (matchOn : ∀ i ∈ S.map old ∪ Z, v i = extendWord old D Z u i) :
    ∃ w ∈ ReedSolomon.code (old.trans D) k, ∀ j ∈ S, w j = u j := by
  classical
  let : NeZero (k + Z.card) := ⟨by omega⟩
  obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
  have zero (i : I) (hi : i ∈ Z) : p.eval (D i) = 0 := by
    rw [heval, matchOn i (mem_union_right _ hi), extend_zero old D Z u hi]
  obtain ⟨q, eq⟩ := Polynomial.prod_X_sub_C_dvd Z D D.injective.injOn p zero
  change p = Lagrange.nodal Z D * q at eq
  have degree : q.natDegree < k := by
    by_cases hz : q = 0
    · simpa [hz] using hk
    rw [eq, natDegree_mul Lagrange.nodal_ne_zero hz, Lagrange.natDegree_nodal] at hp
    omega
  refine ⟨fun i => q.eval (D (old i)),
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q degree (fun _ => rfl), ?_⟩
  intro j hj
  have h := (heval (old j)).trans (matchOn _ (mem_union_left _ (mem_map.mpr ⟨j,hj,rfl⟩)))
  rw [eq, eval_mul, extend_old] at h
  apply mul_left_cancel₀ _ h
  apply Lagrange.eval_nodal_not_at_node
  intro i hi eq
  exact fresh j (D.injective eq ▸ hi)

variable [Fintype I] [Fintype J]

/-- Every bad challenge is preserved when the agreement target admits the old
support and all the selected extra coordinates. -/
theorem mcaEvent_extend (old : J ↪ I) (D : I ↪ F) (Z : Finset I) (fresh : ∀ j, old j ∉ Z)
    {k : ℕ} (hk : 0 < k) {δ δ' : ℝ≥0} (size : ∀ t : ℕ, (1 - δ) * Fintype.card J ≤ (t : ℝ≥0) →
      (1 - δ') * Fintype.card I ≤ ((t + Z.card : ℕ) : ℝ≥0)) (u v : J → F) (γ : F)
    (bad : mcaEvent (ReedSolomon.code (old.trans D) k : Set (J → F)) δ u v γ) :
    mcaEvent (ReedSolomon.code D (k + Z.card) : Set (I → F)) δ'
      (extendWord old D Z u) (extendWord old D Z v) γ := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  obtain ⟨S,hS,⟨w,hw,agree⟩,no⟩ := bad
  obtain ⟨p,hp,heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  have dis : Disjoint (S.map old) Z := by
    apply disjoint_left.mpr
    intro i hi
    obtain ⟨j,_,rfl⟩ := mem_map.mp hi
    exact fresh j
  refine ⟨S.map old ∪ Z, ?_, ?_, ?_⟩
  · rw [card_union_of_disjoint dis, card_map]
    exact size _ hS
  · let q := Lagrange.nodal Z D * p
    have hdeg : q.natDegree < k + Z.card := by
      have bound := natDegree_mul_le (p := Lagrange.nodal Z D) (q := p)
      rw [Lagrange.natDegree_nodal] at bound
      dsimp only [q]
      omega
    refine ⟨fun i => q.eval (D i),
      ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q hdeg (fun _ => rfl), ?_⟩
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      change (Lagrange.nodal Z D * p).eval (D (old j)) = _
      rw [eval_mul, extend_old, extend_old]
      have fold : p.eval (D (old j)) = u j + γ * v j := (heval j).trans (agree j hj)
      rw [fold, smul_eq_mul]
      ring
    · change (Lagrange.nodal Z D * p).eval (D i) = _
      rw [eval_mul, Lagrange.eval_nodal_at_node hi, zero_mul, extend_zero old D Z u hi,
        extend_zero old D Z v hi, smul_zero, add_zero]
  · rintro ⟨a,ha,b,hb,both⟩
    obtain ⟨w,hw,wa⟩ := shorten old D Z fresh hk u S a ha (fun i hi => (both i hi).1)
    obtain ⟨z,hz,zb⟩ := shorten old D Z fresh hk v S b hb (fun i hi => (both i hi).2)
    exact no ⟨w,hw,z,hz,fun i hi => ⟨wa i hi,zb i hi⟩⟩

/-- Worst-case MCA probability survives padding by any feasible number of zero
coordinates, allowing additional unselected sites in the target domain. -/
theorem epsMCA_le [Fintype F] [Nonempty I] (D : I ↪ F) (old : J ↪ I) {k r : ℕ}
    (hk : 0 < k) (room : Fintype.card J + r ≤ Fintype.card I) {δ δ' : ℝ≥0}
    (size : ∀ t : ℕ, (1 - δ) * (Fintype.card J : ℝ≥0) ≤ (t : ℝ≥0) →
      (1 - δ') * (Fintype.card I : ℝ≥0) ≤ ((t + r : ℕ) : ℝ≥0)) :
    epsMCA (F := F) (ReedSolomon.code (old.trans D) k : Set (J → F)) δ ≤
      epsMCA (F := F) (ReedSolomon.code D (k + r) : Set (I → F)) δ' := by
  classical
  let fresh := (univ.map old)ᶜ
  have enough : r ≤ fresh.card := by simp [fresh,card_compl]; omega
  obtain ⟨Z, sub, card⟩ := exists_subset_card_eq enough
  have free (j : J) : old j ∉ Z := fun hj =>
    (mem_compl.mp (sub hj)) (mem_map.mpr ⟨j,mem_univ _,rfl⟩)
  subst r
  rw [epsMCA_eq_iSup_badCount_div, epsMCA_eq_iSup_badCount_div]
  apply ENNReal.div_le_div_right _ _
  apply iSup_le
  intro u
  apply le_iSup_of_le (fun i : Fin 2 => extendWord old D Z (u i))
  apply Nat.cast_le.mpr (card_le_card _)
  intro γ hγ
  exact mem_filter.mpr ⟨mem_univ _, mcaEvent_extend old D Z free hk size (u 0) (u 1) γ
    (mem_filter.mp hγ).2⟩

end ProximityGap.LocatorPadding
