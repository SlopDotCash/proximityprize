/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GenericFarPin

/-!
# The universal boundary bound (#371): the all-stacks sup is SOLVED

The last gap in the boundary-radius picture: the ownership ceiling
`#badSet ≤ C(n,k+1)` held only for strongly far directions.  This file removes
EVERY hypothesis on the stack:

* `explainable_of_tuple_residuals_zero` — the gluing lemma: if every injective
  `(k+1)`-tuple inside a witness kills the residual of `u`, then a single
  codeword explains `u` on the whole witness (overlapping interpolants agree
  on `k` shared nodes, hence glue).
* `badSet_subset_ratio_image_universal` — for ANY stack `(u₀, u₁)` at any
  radius below capacity: every bad scalar is pinned by a tuple with nonzero
  direction residual.  (If all direction residuals on the witness vanished,
  the glued codeword would assemble a joint pair, contradicting badness.)
* `residual_comp_perm` / `exists_perm_of_image_eq` — the residual ratio is a
  function of the tuple's image set (row permutations scale both determinants
  by the same sign).
* `universal_badSet_card_le` — **`#badSet ≤ C(n,k+1)` for EVERY stack and
  every radius below capacity**, unconditionally.
* `boundary_allStacks_solution` — combined with the generic-far attainment:
  at the boundary radius, when `C(n,k+1)² ≤ q`,

    **`sup over ALL stacks of #badSet  =  C(n, k+1)`** — exactly:

  every stack is bounded by it, and some stack attains it.  The boundary-slice
  threshold value is completely determined.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Any large enough finset contains an injective `(k+1)`-tuple. -/
theorem exists_injTuple_of_card_le {k : ℕ} {S : Finset (Fin n)}
    (h : k + 1 ≤ S.card) :
    ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ ∀ a, t a ∈ S := by
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq h
  refine ⟨fun a => (S'.equivFin.symm (Fin.cast hS'card.symm a) : Fin n),
    ?_, fun a => hS'sub (S'.equivFin.symm (Fin.cast hS'card.symm a)).2⟩
  intro a b hab
  have h1 : (S'.equivFin.symm (Fin.cast hS'card.symm a))
      = S'.equivFin.symm (Fin.cast hS'card.symm b) := Subtype.ext hab
  exact Fin.cast_injective _ (S'.equivFin.symm.injective h1)

open Classical in
/-- **The gluing lemma**: if every injective `(k+1)`-tuple inside `S` kills the
residual of `u`, a single codeword explains `u` on all of `S`. -/
theorem explainable_of_tuple_residuals_zero (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {u : Fin n → F} {S : Finset (Fin n)} (hS : k + 1 ≤ S.card)
    (hres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      (∀ a, t a ∈ S) → residual dom k t u = 0) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ S, c i = u i := by
  obtain ⟨t₀, ht₀inj, ht₀mem⟩ := exists_injTuple_of_card_le hS
  obtain ⟨c, hcC, hcag⟩ :=
    extension_of_residual_eq_zero dom t₀ ht₀inj (hres t₀ ht₀inj ht₀mem)
  refine ⟨c, hcC, fun i hi => ?_⟩
  by_cases hmem : ∃ a, t₀ a = i
  · obtain ⟨a, rfl⟩ := hmem
    exact hcag a
  · push Not at hmem
    -- swap the last node for `i`
    set t₁ : Fin (k + 1) → Fin n := Function.update t₀ (Fin.last k) i with ht₁
    have ht₁inj : Function.Injective t₁ := by
      intro a b hab
      rw [ht₁] at hab
      by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k
      · rw [ha, hb]
      · subst ha
        rw [Function.update_self, Function.update_of_ne hb] at hab
        exact absurd hab.symm (hmem b)
      · subst hb
        rw [Function.update_self, Function.update_of_ne ha] at hab
        exact absurd hab (hmem a)
      · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact ht₀inj hab
    have ht₁mem : ∀ a, t₁ a ∈ S := by
      intro a
      rw [ht₁]
      by_cases ha : a = Fin.last k
      · subst ha
        rw [Function.update_self]
        exact hi
      · rw [Function.update_of_ne ha]
        exact ht₀mem a
    obtain ⟨c', hc'C, hc'ag⟩ :=
      extension_of_residual_eq_zero dom t₁ ht₁inj (hres t₁ ht₁inj ht₁mem)
    -- the two interpolants agree on the k shared nodes, hence are equal
    obtain ⟨P, hPdeg, rfl⟩ := hcC
    obtain ⟨P', hP'deg, rfl⟩ := hc'C
    have hPP' : P = P' := by
      have hzero : P - P' = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (s := (Finset.univ.erase (Fin.last k)).image (fun a => dom (t₀ a)))
          ?_ ?_
        · have hcard : ((Finset.univ.erase (Fin.last k)).image
              (fun a => dom (t₀ a))).card = k := by
            rw [Finset.card_image_of_injective _
              (fun a b hab => ht₀inj (dom.injective hab)),
              Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, Fintype.card_fin]
            omega
          rw [hcard]
          exact lt_of_le_of_lt (Polynomial.degree_sub_le P P')
            (max_lt hPdeg hP'deg)
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          have hane : a ≠ Fin.last k := (Finset.mem_erase.mp ha).1
          have h1 : P.eval (dom (t₀ a)) = u (t₀ a) := hcag a
          have h2 : P'.eval (dom (t₀ a)) = u (t₀ a) := by
            have h := hc'ag a
            rw [ht₁, Function.update_of_ne hane] at h
            exact h
          rw [eval_sub, h1, h2, sub_self]
      exact sub_eq_zero.mp hzero
    have h3 := hc'ag (Fin.last k)
    rw [ht₁, Function.update_self] at h3
    rw [hPP']
    exact h3

open Classical in
/-- **The universal forward inclusion**: for ANY stack at any radius below
capacity, every bad scalar is the residual ratio of a tuple with nonzero
direction residual.  No farness hypotheses. -/
theorem badSet_subset_ratio_image_universal (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
      ⊆ (Finset.univ.filter
          (fun t : Fin (k + 1) → Fin n => Function.Injective t
            ∧ residual dom k t u₁ ≠ 0)).image
        (fun t => -(residual dom k t u₀) / residual dom k t u₁) := by
  intro γ hγ
  obtain ⟨S, hsz, ⟨c, hcC, hag⟩, hno⟩ := (Finset.mem_filter.mp hγ).2
  have hScard : k + 1 ≤ S.card := by
    have h1 : ((k : ℝ≥0)) < (S.card : ℝ≥0) := lt_of_lt_of_le hlo hsz
    have h2 : k < S.card := by exact_mod_cast h1
    omega
  -- some tuple in the witness has nonzero direction residual
  have hpin : ∃ t : Fin (k + 1) → Fin n, Function.Injective t
      ∧ (∀ a, t a ∈ S) ∧ residual dom k t u₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
        (∀ a, t a ∈ S) → residual dom k t u₁ = 0 := by
      intro t htinj htmem
      by_contra hne
      exact hne (by
        by_contra hne2
        exact hne2 (by
          have := hall t htinj htmem
          exact this))
    obtain ⟨c₁, hc₁C, hc₁ag⟩ :=
      explainable_of_tuple_residuals_zero dom hk hScard hres
    -- assemble the joint pair
    refine hno ⟨c - γ • c₁, ?_, c₁, hc₁C, fun i hi => ⟨?_, ?_⟩⟩
    · exact Submodule.sub_mem _ hcC (Submodule.smul_mem _ γ hc₁C)
    · have h1 := hag i hi
      have h2 := hc₁ag i hi
      show (c - γ • c₁) i = u₀ i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hc : c i = u₀ i + γ * u₁ i := by simpa [smul_eq_mul] using h1
      rw [hc, h2]
      ring
    · exact hc₁ag i hi
  obtain ⟨t, htinj, htmem, htres⟩ := hpin
  -- the tuple pins the scalar
  obtain ⟨P, hPdeg, rfl⟩ := hcC
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
  refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, htinj, htres⟩, ?_⟩
  exact (gamma_eq_of_owned dom k t htres hlinezero).symm

omit [Fintype F] [DecidableEq F] in
/-- Row permutations scale the residual by the permutation sign. -/
theorem residual_comp_perm (dom : Fin n ↪ F) (k : ℕ)
    (t : Fin (k + 1) → Fin n) (π : Equiv.Perm (Fin (k + 1)))
    (y : Fin n → F) :
    residual dom k (t ∘ ⇑π) y
      = ((Equiv.Perm.sign π : ℤ) : F) * residual dom k t y := by
  have hsub : borderedMatrix dom k (t ∘ ⇑π) y
      = (borderedMatrix dom k t y).submatrix ⇑π id := rfl
  rw [residual, hsub, Matrix.det_permute, residual]

omit [Fintype F] [DecidableEq F] in
/-- The residual ratio is invariant under tuple permutations. -/
theorem ratio_comp_perm (dom : Fin n ↪ F) (k : ℕ)
    (t : Fin (k + 1) → Fin n) (π : Equiv.Perm (Fin (k + 1)))
    (u₀ u₁ : Fin n → F) :
    -(residual dom k (t ∘ ⇑π) u₀) / residual dom k (t ∘ ⇑π) u₁
      = -(residual dom k t u₀) / residual dom k t u₁ := by
  rw [residual_comp_perm dom k t π u₀, residual_comp_perm dom k t π u₁]
  have hs : ((Equiv.Perm.sign π : ℤ) : F) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
      rw [h] <;> simp
  rw [neg_div, neg_div, mul_div_mul_left _ _ hs]

/-- Two injective tuples with the same image differ by a permutation. -/
theorem exists_perm_of_image_eq {k : ℕ} {t t' : Fin (k + 1) → Fin n}
    (ht : Function.Injective t) (ht' : Function.Injective t')
    (himg : Finset.univ.image t = Finset.univ.image t') :
    ∃ π : Equiv.Perm (Fin (k + 1)), t = t' ∘ ⇑π := by
  have hrange : Set.range t = Set.range t' := by
    have h1 : Set.range t = ↑(Finset.univ.image t) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have h2 : Set.range t' = ↑(Finset.univ.image t') := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [h1, h2, himg]
  set π : Fin (k + 1) ≃ Fin (k + 1) :=
    (Equiv.ofInjective t ht).trans
      ((Equiv.setCongr hrange).trans (Equiv.ofInjective t' ht').symm)
    with hπ
  refine ⟨π, funext fun a => ?_⟩
  show t a = t' (π a)
  rw [hπ]
  simp only [Equiv.trans_apply, Equiv.setCongr_apply]
  rw [Equiv.apply_ofInjective_symm ht']
  rfl

open Classical in
/-- **THE UNIVERSAL BOUND**: for EVERY stack and every radius below capacity,
the bad-scalar count is at most `C(n, k+1)` — unconditionally. -/
theorem universal_badSet_card_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card ≤ n.choose (k + 1) := by
  -- the canonical set-level ratio function
  set Φ : Finset (Fin n) → F := fun s =>
    if h : s.card = k + 1 then
      -(residual dom k
          (fun a => (s.equivFin.symm (Fin.cast h.symm a) : Fin n)) u₀)
        / residual dom k
          (fun a => (s.equivFin.symm (Fin.cast h.symm a) : Fin n)) u₁
    else 0 with hΦ
  -- the tuple-level ratio image is contained in the subset-level image
  have hsub2 : (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t
          ∧ residual dom k t u₁ ≠ 0)).image
      (fun t => -(residual dom k t u₀) / residual dom k t u₁)
      ⊆ (Finset.univ.powersetCard (k + 1)).image Φ := by
    intro x hx
    obtain ⟨t, htmem, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨-, htinj, -⟩ := Finset.mem_filter.mp htmem
    set s : Finset (Fin n) := Finset.univ.image t with hs
    have hscard : s.card = k + 1 := by
      rw [hs, Finset.card_image_of_injective _ htinj, Finset.card_univ,
        Fintype.card_fin]
    set tc : Fin (k + 1) → Fin n :=
      fun a => (s.equivFin.symm (Fin.cast hscard.symm a) : Fin n) with htc
    have htcinj : Function.Injective tc := by
      intro a b hab
      have h1 : (s.equivFin.symm (Fin.cast hscard.symm a))
          = s.equivFin.symm (Fin.cast hscard.symm b) := Subtype.ext hab
      exact Fin.cast_injective _ (s.equivFin.symm.injective h1)
    have htcimg : Finset.univ.image tc = s := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        exact (s.equivFin.symm (Fin.cast hscard.symm a)).2
      · rw [Finset.card_image_of_injective _ htcinj, Finset.card_univ,
          Fintype.card_fin, hscard]
    obtain ⟨π, hπ⟩ := exists_perm_of_image_eq htinj htcinj (by rw [htcimg])
    refine Finset.mem_image.mpr ⟨s, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hscard⟩, ?_⟩
    rw [hΦ]
    simp only [hscard, dif_pos]
    rw [show (fun a => (s.equivFin.symm (Fin.cast hscard.symm a) : Fin n))
      = tc from rfl, hπ]
    exact (ratio_comp_perm dom k tc π u₀ u₁).symm
  calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card
      ≤ ((Finset.univ.powersetCard (k + 1)).image Φ).card :=
        Finset.card_le_card
          ((badSet_subset_ratio_image_universal dom hk hlo u₀ u₁).trans hsub2)
    _ ≤ (Finset.univ.powersetCard (k + 1)).card := Finset.card_image_le
    _ = n.choose (k + 1) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **THE ALL-STACKS BOUNDARY SOLUTION**: at the boundary radius, when
`C(n,k+1)² ≤ q`, the supremum of the bad-scalar count over ALL stacks is
EXACTLY `C(n, k+1)` — every stack is bounded by it, and some stack attains
it.  The boundary-slice threshold value is completely determined. -/
theorem boundary_allStacks_solution (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F) :
    (∀ u₀ u₁ : Fin n → F,
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          u₀ u₁ γ)).card ≤ n.choose (k + 1))
    ∧ ∃ Q₀ : F[X],
      (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
        = n.choose (k + 1) :=
  ⟨fun u₀ u₁ => universal_badSet_card_le dom hk hlo u₀ u₁,
    exists_genericFar_badSet_card dom hk hlo hhi hsmall⟩

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.explainable_of_tuple_residuals_zero
#print axioms ProximityGap.Ownership.badSet_subset_ratio_image_universal
#print axioms ProximityGap.Ownership.universal_badSet_card_le
#print axioms ProximityGap.Ownership.boundary_allStacks_solution
