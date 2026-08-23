/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceExact
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# The boundary-slice law UNCONDITIONAL: every line, no far-ness hypothesis (#371)

`boundary_slice_badSet_eq` computes the bad set exactly at the boundary radius
(`k < (1−δ)n ≤ k+1`) **for strongly far directions** (`hμ`: max codeword agreement of `u₁`
at most `k`).  This file removes the far-ness hypothesis entirely:

  **for EVERY stack `(u₀, u₁)`, the bad set at the boundary radius is the residual-ratio
  image over the NON-DEGENERATE injective `(k+1)`-tuples** (those with
  `residual dom k t u₁ ≠ 0`):

  `badSet = { −e_t(u₀)/e_t(u₁) : t injective, e_t(u₁) ≠ 0 }`   (both inclusions).

Strong farness makes every injective tuple non-degenerate, so the strongly-far law is the
special case.  The new content is the **extraction lemma**
(`exists_resNeZero_tuple_of_no_joint`): a no-joint witness always contains a non-degenerate
tuple — if every `(k+1)`-tuple of the witness had vanishing `u₁`-residual, the per-tuple
extensions would glue (two degree-`< k` extensions agreeing on `k` shared nodes are equal)
into a single codeword explaining `u₁` on the whole witness, and together with the line's
witness codeword that builds a joint pair, contradicting the no-joint clause.

**Why this matters (#371, the deployed-value lane).**  The bad side of the deployed pin is
the maximum of the ratio-image size over all stacks.  The strongly-far law restricted that
census to far directions; this law closes the gap: *no direction class is exempt* — the
extremizer hunt (worst character lines, §50–§52; far-generic `C(n,k+1)` attainment) ranges
over the same ratio-image functional for every line, and any non-far surplus is counted by
exactly the same formula.  In particular the §50 high-frequency character-line counts are
genuine `ε_mca` mass at the boundary radius regardless of their distance to the code.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The extraction lemma**: a no-joint witness of a bad scalar contains an injective
`(k+1)`-tuple with non-vanishing direction residual.  Otherwise all per-tuple extensions of
`u₁` glue into one degree-`< k` explanation of `u₁` on the witness, which combines with the
line's witness codeword into a joint pair. -/
theorem exists_resNeZero_tuple_of_no_joint (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {S : Finset (Fin n)} (hScard : k + 1 ≤ S.card)
    (hwC : ∃ w ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hno : ¬ pairJointAgreesOn
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁) :
    ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ a, t a ∈ S) ∧
      residual dom k t u₁ ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the base tuple: an enumeration of a (k+1)-subset of S
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hScard
  set t₀ : Fin (k + 1) → Fin n :=
    fun a => (S'.equivFin.symm (Fin.cast hS'card.symm a) : Fin n) with ht₀
  have ht₀inj : Function.Injective t₀ := by
    intro a b hab
    have h1 : (S'.equivFin.symm (Fin.cast hS'card.symm a))
        = S'.equivFin.symm (Fin.cast hS'card.symm b) := Subtype.ext hab
    have h2 := S'.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have ht₀mem : ∀ a, t₀ a ∈ S := fun a =>
    hS'sub (S'.equivFin.symm (Fin.cast hS'card.symm a)).2
  -- its extension (degree < k) for u₁
  obtain ⟨c₀, hc₀C, hcag₀⟩ := extension_of_residual_eq_zero dom t₀ ht₀inj
    (hcon t₀ ht₀inj ht₀mem)
  obtain ⟨P₀, hP₀deg, rfl⟩ := hc₀C
  -- P₀ explains u₁ on ALL of S
  have hP₀S : ∀ x ∈ S, u₁ x = P₀.eval (dom x) := by
    intro x hxS
    by_cases hxim : ∃ a, t₀ a = x
    · obtain ⟨a, rfl⟩ := hxim
      exact (show P₀.eval (dom (t₀ a)) = u₁ (t₀ a) from hcag₀ a).symm
    · push_neg at hxim
      -- the swapped tuple: replace the last coordinate by x
      have htxinj : Function.Injective (Function.update t₀ (Fin.last k) x) := by
        intro a b hab
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k
        · rw [ha, hb]
        · subst ha
          rw [Function.update_self, Function.update_of_ne hb] at hab
          exact absurd hab.symm (hxim b)
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha] at hab
          exact absurd hab (hxim a)
        · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
          exact ht₀inj hab
      have htxmem : ∀ a, Function.update t₀ (Fin.last k) x a ∈ S := by
        intro a
        by_cases ha : a = Fin.last k
        · subst ha
          rw [Function.update_self]
          exact hxS
        · rw [Function.update_of_ne ha]
          exact ht₀mem a
      obtain ⟨cx, hcxC, hcagx⟩ := extension_of_residual_eq_zero dom
        (Function.update t₀ (Fin.last k) x) htxinj (hcon _ htxinj htxmem)
      obtain ⟨Px, hPxdeg, rfl⟩ := hcxC
      -- the two extensions agree on the k shared nodes, hence are equal
      have hinjlam : Function.Injective (fun j : Fin k => t₀ j.castSucc) :=
        fun a b hab => Fin.castSucc_injective k (ht₀inj hab)
      have hscard : (Finset.univ.image (fun j : Fin k => t₀ j.castSucc)).card = k := by
        rw [Finset.card_image_of_injective _ hinjlam, Finset.card_univ, Fintype.card_fin]
      have hPeq : Px = P₀ := by
        refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
          (Finset.univ.image (fun j : Fin k => t₀ j.castSucc))
          (fun a _ b _ hab => dom.injective hab) ?_ ?_ ?_
        · rw [hscard]; exact hPxdeg
        · rw [hscard]; exact hP₀deg
        · intro i hi
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
          have hne : j.castSucc ≠ Fin.last k := ne_of_lt (Fin.castSucc_lt_last j)
          have h1 : Px.eval (dom (Function.update t₀ (Fin.last k) x j.castSucc))
              = u₁ (Function.update t₀ (Fin.last k) x j.castSucc) := hcagx j.castSucc
          rw [Function.update_of_ne hne] at h1
          have h2 : P₀.eval (dom (t₀ j.castSucc)) = u₁ (t₀ j.castSucc) := hcag₀ j.castSucc
          rw [h1, h2]
      have hlast : Px.eval (dom (Function.update t₀ (Fin.last k) x (Fin.last k)))
          = u₁ (Function.update t₀ (Fin.last k) x (Fin.last k)) := hcagx (Fin.last k)
      rw [Function.update_self, hPeq] at hlast
      exact hlast.symm
  -- assemble the joint pair
  obtain ⟨w, hwmem, hwag⟩ := hwC
  obtain ⟨Pw, hPwdeg, rfl⟩ := hwmem
  refine hno ⟨fun i => (Pw - γ • P₀).eval (dom i),
    ⟨Pw - γ • P₀,
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt hPwdeg (lt_of_le_of_lt (Polynomial.degree_smul_le γ P₀) hP₀deg)), rfl⟩,
    fun i => P₀.eval (dom i), ⟨P₀, hP₀deg, rfl⟩, fun i hi => ⟨?_, (hP₀S i hi).symm⟩⟩
  have h1 : Pw.eval (dom i) = u₀ i + γ * u₁ i := by
    have h := hwag i hi
    rwa [smul_eq_mul] at h
  show (Pw - γ • P₀).eval (dom i) = u₀ i
  rw [Polynomial.smul_eq_C_mul, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, h1, ← hP₀S i hi]
  ring

open Classical in
/-- **THE UNCONDITIONAL BOUNDARY-SLICE LAW**: at the boundary radius, for EVERY stack, the
bad set is exactly the residual-ratio image over the non-degenerate injective
`(k+1)`-tuples.  No far-ness hypothesis: the strongly-far law
(`boundary_slice_badSet_eq`) is the special case in which every injective tuple is
non-degenerate. -/
theorem boundary_slice_badSet_eq_unconditional (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      = (Finset.univ.filter
          (fun t : Fin (k+1) → Fin n =>
            Function.Injective t ∧ residual dom k t u₁ ≠ 0)).image
        (fun t => -(residual dom k t u₀) / residual dom k t u₁) := by
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · -- ⊆ : a bad witness contains a non-degenerate tuple pinning the scalar
    rintro ⟨S, hsz, hwC, hno⟩
    have hScard : k + 1 ≤ S.card := by
      have h1 : ((k : ℝ≥0)) < (S.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
      have h2 : k < S.card := by exact_mod_cast h1
      omega
    obtain ⟨t, htinj, htmem, hres⟩ :=
      exists_resNeZero_tuple_of_no_joint dom hk hScard hwC hno
    obtain ⟨w, hwmem, hag⟩ := hwC
    obtain ⟨P, hPdeg, rfl⟩ := hwmem
    have hPdeg' : P.natDegree < k := by
      by_cases hP0 : P = 0
      · subst hP0
        simpa using hk
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    have hlinezero : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      refine residual_eq_zero_of_extends dom k t hPdeg' fun a => ?_
      have := hag (t a) (htmem a)
      simpa [smul_eq_mul] using this.symm
    rw [residual_line] at hlinezero
    exact ⟨t, ⟨htinj, hres⟩, (gamma_eq_of_owned dom k t hres hlinezero).symm⟩
  · -- ⊇ : every non-degenerate tuple's ratio is bad
    rintro ⟨t, ⟨htinj, hres1⟩, rfl⟩
    set γ := -(residual dom k t u₀) / residual dom k t u₁ with hγ
    have hlinezero : residual dom k t (fun i => u₀ i + γ * u₁ i) = 0 := by
      rw [residual_line, hγ]
      field_simp
      ring
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hlinezero
    refine ⟨Finset.univ.image t, ?_, ⟨c, hcC, ?_⟩, ?_⟩
    · have hcard : (Finset.univ.image t).card = k + 1 := by
        rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
          Fintype.card_fin]
      rw [hcard]
      exact_mod_cast hhi
    · intro i hi
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      have h := hcag a
      show c (t a) = u₀ (t a) + γ • u₁ (t a)
      rw [smul_eq_mul]
      exact h
    · -- no joint: v₁ would extend u₁ on the tuple, killing the residual
      rintro ⟨v₀, hv₀, v₁, hv₁, hagj⟩
      obtain ⟨P₁, hP₁deg, rfl⟩ := hv₁
      have hP₁deg' : P₁.natDegree < k := by
        by_cases hP0 : P₁ = 0
        · subst hP0
          simpa using hk
        · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP₁deg
      refine hres1 (residual_eq_zero_of_extends dom k t hP₁deg' fun a => ?_)
      exact ((hagj (t a) (Finset.mem_image_of_mem t (Finset.mem_univ a))).2).symm

open Classical in
/-- **The unconditional boundary count**: at the boundary radius, every stack has at most
`#{non-degenerate injective tuples}` bad scalars — the count side of the law, for every
line with no far-ness hypothesis. -/
theorem boundary_slice_badScalars_card_le_unconditional (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (Finset.univ.filter
          (fun t : Fin (k+1) → Fin n =>
            Function.Injective t ∧ residual dom k t u₁ ≠ 0)).card := by
  rw [boundary_slice_badSet_eq_unconditional dom hk hlo hhi u₀ u₁]
  exact Finset.card_image_le

open Classical in
/-- **Coarse every-line boundary budget**: the unconditional boundary-slice count is always
at most the number of `(k+1)`-tuples.  This is the hypothesis-free `n^(k+1)` numerator
before any residual-ratio collision census is used. -/
theorem boundary_slice_badScalars_card_le_pow_unconditional (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n ^ (k + 1) := by
  refine le_trans (boundary_slice_badScalars_card_le_unconditional dom hk hlo hhi u₀ u₁) ?_
  calc
    (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n =>
          Function.Injective t ∧ residual dom k t u₁ ≠ 0)).card
        ≤ (Finset.univ : Finset (Fin (k + 1) → Fin n)).card := by
          exact Finset.card_le_card (by intro t _; simp)
    _ = Fintype.card (Fin (k+1) → Fin n) := by rw [Finset.card_univ]
    _ = n ^ (k + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

open Classical in
/-- **The every-line boundary `ε_mca` bridge**: at the boundary radius
`k < (1-δ)n ≤ k+1`, every stack has bad-scalar mass at most `n^(k+1)/|F|`.
Sharper boundary-slice results replace the numerator by a residual-ratio image
size; this theorem is the unconditional coarse consumer. -/
theorem epsMCA_le_boundary_slice_everyLine_pow (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n ^ (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ (n ^ (k + 1))
    (fun u => boundary_slice_badScalars_card_le_pow_unconditional dom hk hlo hhi
      (u 0) (u 1))

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.exists_resNeZero_tuple_of_no_joint
#print axioms ProximityGap.Ownership.boundary_slice_badSet_eq_unconditional
#print axioms ProximityGap.Ownership.boundary_slice_badScalars_card_le_unconditional
#print axioms ProximityGap.Ownership.boundary_slice_badScalars_card_le_pow_unconditional
#print axioms ProximityGap.Ownership.epsMCA_le_boundary_slice_everyLine_pow
