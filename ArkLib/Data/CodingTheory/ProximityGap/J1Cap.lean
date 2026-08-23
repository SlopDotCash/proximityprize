/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2

/-!
# The J1 finite-algebra cap: at most two constrained scalars (issue #65)

`GrandChallengesLattice.lean` reduces the radius-`1/n` Grand MCA bad-count cap to the
finite-algebra statement that the scalar set cut out by `j1RatioConstraint` has at most two
elements (`j1RatioConstraintBadScalars_card_le_two_of_not_three` /
`mcaBadCount_j1_le_two_of_not_three_ratioConstraints`).  This file proves that statement
unconditionally, under the standing window hypothesis `k + 3 ≤ #ι`, by a **codeword
window-collision argument** — no coefficient eliminant needed:

1. *Omitted-window codeword extraction* (`j1RatioConstraint_exists_omitted_codeword`):
   by `j1RatioConstraint_to_omitted` + the gluing lemma `extendableOn_of_forall_cT_eq_zero`,
   every constrained `γ` has a coordinate `i` with `u₁` non-extendable on `univ.erase i` and a
   codeword `w` agreeing with the line word `u₀ + γ • u₁` on all of `univ.erase i`.
2. *Same window ⟹ same scalar* (`j1_gamma_eq_of_same_window`): two line codewords on one
   window with distinct scalars exhibit `u₁` itself as extendable there
   (`(γ−γ')⁻¹ • (w − w')` agrees with `u₁`), contradicting non-extendability.
3. *Three scalars collide* (`not_three_j1_ratioConstraints`): three distinct constrained
   scalars have three pairwise-distinct witness coordinates `i₀, i₁, i₂`; the pairwise
   difference codewords `d_ab := (γ_a−γ_b)⁻¹ • (w_a−w_b)` all agree with `u₁` off
   `{i_a, i_b}`, hence agree pairwise on the `n−3 ≥ k` remaining points and are a single
   codeword `d` (`code_ext_of_agree_card_le`); but then `d` agrees with `u₁` on **all** of
   `univ.erase i₀` (any `x ≠ i₀` misses `i₁` or `i₂`), contradicting witness `i₀`'s
   non-extendability.

The cap of `2` is tight: two distinct constrained scalars on two distinct omitted windows are
consistent (then `u₁` agrees with `d₀₁` everywhere except possibly at `i₀` and `i₁`).

## Main results

* `not_three_j1_ratioConstraints` — no three distinct scalars satisfy the J1 constraint.
* `j1RatioConstraintBadScalars_card_le_two` — the issue-#65 finite-algebra cap.
* `mcaBadCount_j1_le_two` — the unconditional radius-`1/n` bad-count cap at lattice index `1`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

namespace GrandChallengesLattice

open Polynomial ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Codeword extensionality from `k`-point agreement.**  Two Reed–Solomon codewords (degree
`< k` polynomial evaluations) that agree on at least `k` coordinates are equal. -/
theorem code_ext_of_agree_card_le (domain : ι ↪ F) {k : ℕ} {v v' : ι → F}
    (hv : v ∈ (ReedSolomon.code domain k : Set (ι → F)))
    (hv' : v' ∈ (ReedSolomon.code domain k : Set (ι → F)))
    {A : Finset ι} (hA : k ≤ A.card) (hagree : ∀ x ∈ A, v x = v' x) :
    v = v' := by
  rw [SetLike.mem_coe, mem_code_iff_exists_polynomial] at hv hv'
  obtain ⟨p, hpdeg, hp⟩ := hv
  obtain ⟨q, hqdeg, hq⟩ := hv'
  have hinj : Set.InjOn (fun i => domain i) (↑A : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  have hcast : (k : WithBot ℕ) ≤ (A.card : WithBot ℕ) := by exact_mod_cast hA
  have hpq : p = q := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := A) (v := fun i => domain i)
      hinj (lt_of_lt_of_le hpdeg hcast) (lt_of_lt_of_le hqdeg hcast) ?_
    intro i hi
    have h1 : v i = p.eval (domain i) := by
      simpa [ReedSolomon.evalOnPoints] using congrFun hp i
    have h2 : v' i = q.eval (domain i) := by
      simpa [ReedSolomon.evalOnPoints] using congrFun hq i
    rw [← h1, ← h2]
    exact hagree i hi
  funext i
  have h1 : v i = p.eval (domain i) := by
    simpa [ReedSolomon.evalOnPoints] using congrFun hp i
  have h2 : v' i = q.eval (domain i) := by
    simpa [ReedSolomon.evalOnPoints] using congrFun hq i
  rw [h1, h2, hpq]

/-- **Omitted-window codeword extraction.**  Every J1-constrained scalar has an omitted window
`univ.erase i` where `u₁` is non-extendable while the line word `u₀ + γ • u₁` agrees with an
actual codeword on the whole window. -/
theorem j1RatioConstraint_exists_omitted_codeword
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {u₀ u₁ : ι → F} {γ : F}
    (hγ : j1RatioConstraint domain k u₀ u₁ γ) :
    ∃ i : ι,
      NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) (Finset.univ.erase i) u₁ ∧
      ∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)),
        ∀ x ∈ Finset.univ.erase i, w x = (u₀ + γ • u₁) x := by
  obtain ⟨i, hne, hvanish⟩ := j1RatioConstraint_to_omitted domain hk hγ
  obtain ⟨w, hwC, hwagree⟩ := extendableOn_of_forall_cT_eq_zero domain hvanish
  exact ⟨i, hne, w, hwC, hwagree⟩

/-- **Same window ⟹ same scalar.**  If `u₁` is non-extendable on a window `S` while the line
words at `γ` and `γ'` both agree with codewords on `S`, then `γ = γ'`: otherwise
`(γ−γ')⁻¹ • (w − w')` is a codeword agreeing with `u₁` on `S`. -/
theorem j1_gamma_eq_of_same_window
    (domain : ι ↪ F) {k : ℕ} {S : Finset ι} {u₀ u₁ : ι → F} {γ γ' : F}
    (hne : NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) S u₁)
    (hw : ∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)),
      ∀ x ∈ S, w x = (u₀ + γ • u₁) x)
    (hw' : ∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)),
      ∀ x ∈ S, w x = (u₀ + γ' • u₁) x) :
    γ = γ' := by
  by_contra hγγ'
  have hsub : γ - γ' ≠ 0 := sub_ne_zero.mpr hγγ'
  obtain ⟨w, hwC, hwa⟩ := hw
  obtain ⟨w', hwC', hwa'⟩ := hw'
  apply hne
  refine ⟨(γ - γ')⁻¹ • (w - w'), ?_, ?_⟩
  · exact SetLike.mem_coe.mpr
      (Submodule.smul_mem _ _
        (Submodule.sub_mem _ (SetLike.mem_coe.mp hwC) (SetLike.mem_coe.mp hwC')))
  · intro x hx
    have hdiff : w x - w' x = (γ - γ') * u₁ x := by
      rw [hwa x hx, hwa' x hx]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hdiff]
    exact inv_mul_cancel_left₀ hsub _

/-- The pairwise difference codeword `(γ_a − γ_b)⁻¹ • (w_a − w_b)` agrees with `u₁` at every
coordinate outside the two omitted points. -/
private theorem diff_codeword_agrees
    {u₀ u₁ : ι → F} {γa γb : F} (hab : γa ≠ γb)
    {ia ib : ι} {wa wb : ι → F}
    (hwa : ∀ x ∈ Finset.univ.erase ia, wa x = (u₀ + γa • u₁) x)
    (hwb : ∀ x ∈ Finset.univ.erase ib, wb x = (u₀ + γb • u₁) x)
    {x : ι} (hxa : x ≠ ia) (hxb : x ≠ ib) :
    ((γa - γb)⁻¹ • (wa - wb)) x = u₁ x := by
  have hsub : γa - γb ≠ 0 := sub_ne_zero.mpr hab
  have ha := hwa x (Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩)
  have hb := hwb x (Finset.mem_erase.mpr ⟨hxb, Finset.mem_univ x⟩)
  have hdiff : wa x - wb x = (γa - γb) * u₁ x := by
    rw [ha, hb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hdiff]
  exact inv_mul_cancel_left₀ hsub _

/-- **The J1 three-scalar collision.**  No three pairwise-distinct scalars satisfy the J1
ratio constraint (window hypothesis `k + 3 ≤ #ι`).  This is the issue-#65 finite-algebra core
in the exact `not-three` shape consumed by
`j1RatioConstraintBadScalars_card_le_two_of_not_three`. -/
theorem not_three_j1_ratioConstraints
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    ¬ ∃ γ₀ γ₁ γ₂ : F,
      γ₀ ≠ γ₁ ∧ γ₀ ≠ γ₂ ∧ γ₁ ≠ γ₂ ∧
      j1RatioConstraint domain k u₀ u₁ γ₀ ∧
      j1RatioConstraint domain k u₀ u₁ γ₁ ∧
      j1RatioConstraint domain k u₀ u₁ γ₂ := by
  rintro ⟨γ₀, γ₁, γ₂, h01, h02, h12, hc0, hc1, hc2⟩
  obtain ⟨i₀, hne₀, w₀, hw₀C, hw₀⟩ :=
    j1RatioConstraint_exists_omitted_codeword domain hk hc0
  obtain ⟨i₁, hne₁, w₁, hw₁C, hw₁⟩ :=
    j1RatioConstraint_exists_omitted_codeword domain hk hc1
  obtain ⟨i₂, hne₂, w₂, hw₂C, hw₂⟩ :=
    j1RatioConstraint_exists_omitted_codeword domain hk hc2
  -- distinct scalars have distinct witness coordinates
  have hii01 : i₀ ≠ i₁ := by
    rintro rfl
    exact h01 (j1_gamma_eq_of_same_window domain hne₀ ⟨w₀, hw₀C, hw₀⟩ ⟨w₁, hw₁C, hw₁⟩)
  have hii02 : i₀ ≠ i₂ := by
    rintro rfl
    exact h02 (j1_gamma_eq_of_same_window domain hne₀ ⟨w₀, hw₀C, hw₀⟩ ⟨w₂, hw₂C, hw₂⟩)
  have hii12 : i₁ ≠ i₂ := by
    rintro rfl
    exact h12 (j1_gamma_eq_of_same_window domain hne₁ ⟨w₁, hw₁C, hw₁⟩ ⟨w₂, hw₂C, hw₂⟩)
  -- the two pairwise difference codewords through γ₀
  set d01 : ι → F := (γ₀ - γ₁)⁻¹ • (w₀ - w₁) with hd01def
  set d02 : ι → F := (γ₀ - γ₂)⁻¹ • (w₀ - w₂) with hd02def
  have hd01C : d01 ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    SetLike.mem_coe.mpr
      (Submodule.smul_mem _ _
        (Submodule.sub_mem _ (SetLike.mem_coe.mp hw₀C) (SetLike.mem_coe.mp hw₁C)))
  have hd02C : d02 ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    SetLike.mem_coe.mpr
      (Submodule.smul_mem _ _
        (Submodule.sub_mem _ (SetLike.mem_coe.mp hw₀C) (SetLike.mem_coe.mp hw₂C)))
  have hd01agree : ∀ x : ι, x ≠ i₀ → x ≠ i₁ → d01 x = u₁ x := fun x hx0 hx1 =>
    diff_codeword_agrees h01 hw₀ hw₁ hx0 hx1
  have hd02agree : ∀ x : ι, x ≠ i₀ → x ≠ i₂ → d02 x = u₁ x := fun x hx0 hx2 =>
    diff_codeword_agrees h02 hw₀ hw₂ hx0 hx2
  -- the difference codewords agree on the n−3 ≥ k points off {i₀,i₁,i₂}, hence are equal
  set A : Finset ι := ((Finset.univ.erase i₀).erase i₁).erase i₂ with hAdef
  have hi₁mem : i₁ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨hii01.symm, Finset.mem_univ i₁⟩
  have hi₂mem : i₂ ∈ (Finset.univ.erase i₀).erase i₁ :=
    Finset.mem_erase.mpr ⟨hii12.symm,
      Finset.mem_erase.mpr ⟨hii02.symm, Finset.mem_univ i₂⟩⟩
  have hAcard : A.card = Fintype.card ι - 3 := by
    rw [hAdef, Finset.card_erase_of_mem hi₂mem, Finset.card_erase_of_mem hi₁mem,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    omega
  have hAk : k ≤ A.card := by omega
  have hmemA : ∀ x ∈ A, x ≠ i₀ ∧ x ≠ i₁ ∧ x ≠ i₂ := by
    intro x hx
    rw [hAdef, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase] at hx
    exact ⟨hx.2.2.1, hx.2.1, hx.1⟩
  have hd : d01 = d02 := by
    refine code_ext_of_agree_card_le domain hd01C hd02C hAk ?_
    intro x hx
    obtain ⟨hx0, hx1, hx2⟩ := hmemA x hx
    rw [hd01agree x hx0 hx1, hd02agree x hx0 hx2]
  -- but then d01 agrees with u₁ on ALL of univ.erase i₀ — contradicting witness i₀
  apply hne₀
  refine ⟨d01, hd01C, ?_⟩
  intro x hx
  have hx0 : x ≠ i₀ := (Finset.mem_erase.mp hx).1
  by_cases hx1 : x = i₁
  · subst hx1
    rw [hd]
    exact hd02agree x hx0 hii12
  · exact hd01agree x hx0 hx1

/-- **The issue-#65 finite-algebra cap.**  For every stack `(u₀, u₁)` the scalar set cut out by
the J1 window ratio constraints has at most two elements (window hypothesis `k + 3 ≤ #ι`). -/
theorem j1RatioConstraintBadScalars_card_le_two
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2 :=
  j1RatioConstraintBadScalars_card_le_two_of_not_three domain u₀ u₁
    (not_three_j1_ratioConstraints domain hk u₀ u₁)

/-- **Unconditional radius-`1/n` bad-count cap at lattice index 1.**  The J1 finite-algebra
theorem feeds the conditional cap of `GrandChallengesLattice.lean`, discharging its
hypothesis. -/
theorem mcaBadCount_j1_le_two
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ ≤ 2 :=
  mcaBadCount_j1_le_two_of_not_three_ratioConstraints domain u₀ u₁
    (not_three_j1_ratioConstraints domain hk u₀ u₁)

end GrandChallengesLattice

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityGap.GrandChallengesLattice.code_ext_of_agree_card_le
#print axioms ProximityGap.GrandChallengesLattice.j1RatioConstraint_exists_omitted_codeword
#print axioms ProximityGap.GrandChallengesLattice.j1_gamma_eq_of_same_window
#print axioms ProximityGap.GrandChallengesLattice.not_three_j1_ratioConstraints
#print axioms ProximityGap.GrandChallengesLattice.j1RatioConstraintBadScalars_card_le_two
#print axioms ProximityGap.GrandChallengesLattice.mcaBadCount_j1_le_two
