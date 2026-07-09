/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipBound
import ArkLib.Data.CodingTheory.ProximityGap.PopularCodewords

/-!
# The general-k multiplicity theorem (#371)

The `k = 1` multiplicity bound lifted to every rate: for a direction `u₁` whose
maximum codeword agreement is `≤ μ`, every bad scalar owns at least
`s.descFactorial k · (s − k − μ)` injective `(k+1)`-tuples (`s = n − w`), because
the degenerate tuples (those where `u₁` extends to degree `< k`) are pinned by
their first `k` coordinates — the extension is unique (`codeword_eq_of_common_tuple`)
and the last coordinate must lie in its agreement set.  Hence

  **`#bad · (s.descFactorial k · (s − k − μ)) ≤ n^{k+1}`**

— radius-free, the general-rate multiplicity engine for the universal below-UDR
assembly.
-/

set_option maxHeartbeats 1000000

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Injective tuples inside a set number at least its descending factorial. -/
theorem injective_tuples_card_ge_descFactorial {k : ℕ} (A : Finset (Fin n)) :
    A.card.descFactorial k ≤ (Finset.univ.filter
      (fun t : Fin k → Fin n => Function.Injective t ∧ ∀ a, t a ∈ A)).card := by
  have hcard : ((Finset.univ : Finset (Fin k ↪ {x // x ∈ A})).card)
      ≤ (Finset.univ.filter
        (fun t : Fin k → Fin n => Function.Injective t ∧ ∀ a, t a ∈ A)).card := by
    refine Finset.card_le_card_of_injOn
      (fun e => fun a => ((e : Fin k ↪ {x // x ∈ A}) a : Fin n)) ?_ ?_
    · intro e _
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, fun a => (e a).2⟩
      intro a b hab
      exact e.injective (Subtype.ext hab)
    · intro e _ e' _ heq
      refine DFunLike.ext _ _ fun a => ?_
      simpa using congrFun heq a
  calc A.card.descFactorial k
      = Fintype.card (Fin k ↪ {x // x ∈ A}) := by
        rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin k ↪ {x // x ∈ A})).card) :=
        (Finset.card_univ).symm
    _ ≤ _ := hcard

open Classical in
/-- **The degenerate-tuple count**: injective `(k+1)`-tuples in `S` on which `u₁`
extends to a codeword number at most `(#injective k-tuples in S) · μ`, when every
codeword agrees with `u₁` on ≤ `μ` positions. -/
theorem degenerate_tuples_card_le (dom : Fin n ↪ F) {k : ℕ} (S : Finset (Fin n))
    {u₁ : Fin n → F} {μ : ℕ}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ μ) :
    ((Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
        (Function.Injective t ∧ ∀ a, t a ∈ S) ∧
        ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ a, c (t a) = u₁ (t a))).card)
      ≤ (Finset.univ.filter (fun t' : Fin k → Fin n =>
          Function.Injective t' ∧ ∀ a, t' a ∈ S)).card * μ := by
  set kT := Finset.univ.filter (fun t' : Fin k → Fin n =>
    Function.Injective t' ∧ ∀ a, t' a ∈ S) with hkT
  set B := (kT ×ˢ (Finset.univ : Finset (Fin n))).filter
    (fun p => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (∀ a, c (p.1 a) = u₁ (p.1 a)) ∧ c p.2 = u₁ p.2) with hB
  -- the degenerate set injects into B
  have hsub : (Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
      (Function.Injective t ∧ ∀ a, t a ∈ S) ∧
      ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
        ∀ a, c (t a) = u₁ (t a))).card ≤ B.card := by
    refine Finset.card_le_card_of_injOn
      (fun t => (fun a => t a.castSucc, t (Fin.last k))) ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter] at ht
      obtain ⟨-, ⟨hinjt, hmem⟩, c, hcC, hagr⟩ := ht
      rw [Finset.mem_coe, hB, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, Finset.mem_univ _⟩, c, hcC, fun a => hagr a.castSucc,
        hagr (Fin.last k)⟩
      rw [hkT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, fun a => hmem _⟩
      intro a b hab
      exact Fin.castSucc_injective k (hinjt hab)
    · intro t ht t' ht' heq
      funext a
      by_cases ha : a = Fin.last k
      · rw [ha]
        exact congrArg Prod.snd heq
      · have ha' : (a : ℕ) < k := by
          have := a.2
          by_contra hc
          exact ha (Fin.ext (by rw [Fin.val_last]; omega))
        have haeq : a = Fin.castSucc ⟨(a : ℕ), ha'⟩ := Fin.ext rfl
        rw [haeq]
        exact congrFun (congrArg Prod.fst heq) ⟨(a : ℕ), ha'⟩
  -- B counts fiberwise over the first component, ≤ μ per fiber
  have hBcount : B.card ≤ kT.card * μ := by
    have hfib : B.card = ∑ t' ∈ kT, (B.filter (fun p => p.1 = t')).card := by
      refine Finset.card_eq_sum_card_fiberwise (f := Prod.fst) ?_
      intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [hfib]
    calc ∑ t' ∈ kT, (B.filter (fun p => p.1 = t')).card
        ≤ ∑ _t' ∈ kT, μ := by
          refine Finset.sum_le_sum fun t' ht' => ?_
          -- per-fiber: all last points lie in ONE agreement set
          by_cases hne : (B.filter (fun p => p.1 = t')).Nonempty
          · obtain ⟨p₀, hp₀⟩ := hne
            obtain ⟨hp₀B, hp₀fst⟩ := Finset.mem_filter.mp hp₀
            obtain ⟨-, c₀, hc₀C, hc₀ag, -⟩ := Finset.mem_filter.mp hp₀B
            rw [hp₀fst] at hc₀ag
            have ht'inj : Function.Injective t' :=
              ((Finset.mem_filter.mp ht').2).1
            calc (B.filter (fun p => p.1 = t')).card
                ≤ (agreeSet c₀ u₁).card := by
                  refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
                  · intro p hp
                    obtain ⟨hpB, hpfst⟩ := Finset.mem_filter.mp hp
                    obtain ⟨-, c, hcC, hcag, hclast⟩ := Finset.mem_filter.mp hpB
                    rw [hpfst] at hcag
                    -- uniqueness: c = c₀
                    have hceq : c = c₀ :=
                      codeword_eq_of_common_tuple dom (y := u₁) hcC hc₀C t'
                        ht'inj hcag hc₀ag
                    rw [Finset.mem_coe, agreeSet, Finset.mem_filter]
                    refine ⟨Finset.mem_univ _, ?_⟩
                    rw [← hceq]
                    exact hclast
                  · intro p hp p' hp' hsnd
                    have h1 := (Finset.mem_filter.mp hp).2
                    have h2 := (Finset.mem_filter.mp hp').2
                    exact Prod.ext (h1.trans h2.symm) hsnd
              _ ≤ μ := hμ c₀ hc₀C
          · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
            simp
      _ = kT.card * μ := by
          rw [Finset.sum_const, smul_eq_mul]
  exact le_trans hsub hBcount

open Classical in
/-- **The converse vanishing**: a zero residual on an injective tuple yields a
codeword extension of the direction on that tuple. -/
theorem extension_of_residual_eq_zero (dom : Fin n ↪ F) {k : ℕ}
    {u₁ : Fin n → F} (t : Fin (k+1) → Fin n) (htinj : Function.Injective t)
    (hres : residual dom k t u₁ = 0) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ a, c (t a) = u₁ (t a) := by
  obtain ⟨v, hv0, hvker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hres
  -- the row identity: ∑_j v(j⁺)·x_a^j + u₁(t a)·v(last) = 0
  have hrow : ∀ a : Fin (k+1),
      (∑ j : Fin k, v j.castSucc * (dom (t a)) ^ (j : ℕ))
        + u₁ (t a) * v (Fin.last k) = 0 := by
    intro a
    have h := congrFun hvker a
    have hsplit : ∑ b : Fin (k + 1), borderedMatrix dom k t u₁ a b * v b
        = (∑ j : Fin k, v j.castSucc * (dom (t a)) ^ (j : ℕ))
          + u₁ (t a) * v (Fin.last k) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hjk : ((j.castSucc : Fin (k+1)) : ℕ) < k := by
          rw [Fin.val_castSucc]
          exact j.2
        show borderedMatrix dom k t u₁ a j.castSucc * v j.castSucc = _
        rw [show borderedMatrix dom k t u₁ a j.castSucc
            = (dom (t a)) ^ ((j.castSucc : Fin (k+1)) : ℕ) from if_pos hjk,
          Fin.val_castSucc]
        ring
      · show borderedMatrix dom k t u₁ a (Fin.last k) * v (Fin.last k) = _
        rw [show borderedMatrix dom k t u₁ a (Fin.last k) = u₁ (t a) from by
          show (if ((Fin.last k : Fin (k+1)) : ℕ) < k then _ else u₁ (t a))
            = u₁ (t a)
          rw [Fin.val_last, if_neg (lt_irrefl k)]]
    rw [← hsplit]
    exact h
  -- the last coordinate of the kernel vector is nonzero
  have hvlast : v (Fin.last k) ≠ 0 := by
    intro hzero
    apply hv0
    set P : F[X] := ∑ j : Fin k, C (v j.castSucc) * X ^ (j : ℕ) with hP
    -- P vanishes at k+1 distinct points and has degree < k ⟹ P = 0
    have hProots : ∀ a : Fin (k+1), P.eval (dom (t a)) = 0 := by
      intro a
      rw [hP, eval_finset_sum]
      have hexp : ∀ j : Fin k,
          (C (v j.castSucc) * X ^ (j : ℕ)).eval (dom (t a))
          = v j.castSucc * (dom (t a)) ^ (j : ℕ) := by
        intro j
        rw [eval_mul, eval_C, eval_pow, eval_X]
      rw [Finset.sum_congr rfl fun j _ => hexp j]
      have := hrow a
      rw [hzero, mul_zero, add_zero] at this
      exact this
    have hPdeg : P.degree < ((k + 1 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (k+1))]
      intro j _
      refine lt_of_le_of_lt (degree_mul_le _ _) ?_
      calc (C (v j.castSucc)).degree + (X ^ (j : ℕ) : F[X]).degree
          ≤ 0 + ((j : ℕ) : WithBot ℕ) :=
            add_le_add degree_C_le (by rw [degree_X_pow])
        _ < ((k + 1 : ℕ) : WithBot ℕ) := by
            rw [zero_add]
            exact_mod_cast (by omega : (j : ℕ) < k + 1)
    have hPzero : P = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (f := P) (s := (Finset.univ.image t).image dom) ?_ ?_
      · have hcard : ((Finset.univ.image t).image dom).card = k + 1 := by
          rw [Finset.card_image_of_injective _ dom.injective,
            Finset.card_image_of_injective _ htinj, Finset.card_univ,
            Fintype.card_fin]
        rw [hcard]
        exact hPdeg
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
        exact hProots a
    -- coefficients vanish ⟹ v = 0
    funext b
    by_cases hb : b = Fin.last k
    · rw [hb, hzero]
      rfl
    · have hb' : (b : ℕ) < k := by
        have := b.2
        by_contra hc
        exact hb (Fin.ext (by rw [Fin.val_last]; omega))
      have hbeq : b = Fin.castSucc ⟨(b : ℕ), hb'⟩ := Fin.ext rfl
      have hcoeff : P.coeff ((b : ℕ)) = v b := by
        rw [hP, finset_sum_coeff]
        rw [Finset.sum_eq_single (⟨(b : ℕ), hb'⟩ : Fin k)]
        · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, ← hbeq]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X_pow, if_neg (by
            intro h
            exact hj (Fin.ext h.symm)), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have := congrArg (fun Q : F[X] => Q.coeff ((b : ℕ))) hPzero
      simp only [coeff_zero] at this
      rw [hcoeff] at this
      rw [this]
      rfl
  -- the extension polynomial: rescale the kernel vector
  set c : F := -(v (Fin.last k))⁻¹ with hc
  set P : F[X] := ∑ j : Fin k, C (c * v j.castSucc) * X ^ (j : ℕ) with hP
  have hPdeg : P.degree < k := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
    intro j _
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    calc (C (c * v j.castSucc)).degree + (X ^ (j : ℕ) : F[X]).degree
        ≤ 0 + ((j : ℕ) : WithBot ℕ) :=
          add_le_add degree_C_le (by rw [degree_X_pow])
      _ < (k : WithBot ℕ) := by
          rw [zero_add]
          exact_mod_cast j.2
  refine ⟨fun i => P.eval (dom i), ⟨P, hPdeg, rfl⟩, fun a => ?_⟩
  show P.eval (dom (t a)) = u₁ (t a)
  rw [hP, eval_finset_sum]
  have hexp : ∀ j : Fin k,
      (C (c * v j.castSucc) * X ^ (j : ℕ)).eval (dom (t a))
      = c * (v j.castSucc * (dom (t a)) ^ (j : ℕ)) := by
    intro j
    rw [eval_mul, eval_C, eval_pow, eval_X]
    ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, ← Finset.mul_sum]
  have hsum : ∑ j : Fin k, v j.castSucc * (dom (t a)) ^ (j : ℕ)
      = -(u₁ (t a) * v (Fin.last k)) := by
    linear_combination hrow a
  rw [hsum, hc]
  field_simp


open Classical in
/-- **THE GENERAL-k MULTIPLICITY THEOREM**: for a direction with maximum codeword
agreement ≤ `μ`, at every radius `δ ≤ w/n`:

  `#bad · ((n−w).descFactorial k · (n−w−k−μ)) ≤ n^{k+1}`. -/
theorem badScalars_card_mul_le_of_agreement (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {w : ℕ} {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {μ : ℕ}
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ μ) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w).descFactorial k * (n - w - k - μ))
      ≤ Fintype.card (Fin (k + 1) → Fin n) := by
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) with hbad
  have hch : ∀ γ ∈ bad, ∃ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin (k + 1) → Fin n, (∀ a, t a ∈ S) →
        residual dom k t u₁ ≠ 0 →
        residual dom k t u₀ + γ * residual dom k t u₁ = 0 := by
    intro γ hγ
    exact mcaEvent_owned_tuples dom hk δ (Finset.mem_filter.mp hγ).2
  choose! W hWsz hWprop using hch
  set 𝒯 : F → Finset (Fin (k + 1) → Fin n) := fun γ =>
    Finset.univ.filter (fun t => (Function.Injective t ∧ ∀ a, t a ∈ W γ) ∧
      residual dom k t u₁ ≠ 0) with h𝒯
  refine badScalars_card_mul_le_ownership dom k u₀ u₁ bad _ 𝒯 ?_ ?_
  · intro γ hγ t ht
    obtain ⟨⟨-, htW⟩, hres⟩ := (Finset.mem_filter.mp ht).2
    exact ⟨hres, hWprop γ hγ t htW hres⟩
  · intro γ hγ
    -- witness size
    have hSsz : n - w ≤ (W γ).card := by
      have h1 := hWsz γ hγ
      have h2 : ((n - w : ℕ) : ℝ≥0) ≤ ((W γ).card : ℝ≥0) := by
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
          rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by rw [Nat.cast_tsub]
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [tsub_mul, one_mul, hcardn]
          _ ≤ ((W γ).card : ℝ≥0) := h1
      exact_mod_cast h2
    have hconv : ∀ t : Fin (k+1) → Fin n, Function.Injective t →
        residual dom k t u₁ = 0 →
        ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
          ∀ a, c (t a) = u₁ (t a) :=
      fun t htinj hres => extension_of_residual_eq_zero dom t htinj hres
    -- the ownership count
    set kT := Finset.univ.filter (fun t' : Fin k → Fin n =>
      Function.Injective t' ∧ ∀ a, t' a ∈ W γ) with hkT
    set I := Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
      Function.Injective t ∧ ∀ a, t a ∈ W γ) with hI
    -- every injective k-tuple extends in ≥ |W|−k ways (Fin.snoc)
    have hIcount : kT.card * ((W γ).card - k) ≤ I.card := by
      have hfib : I.card = ∑ t' ∈ kT,
          (I.filter (fun t : Fin (k+1) → Fin n => (fun a : Fin k => t a.castSucc) = t')).card := by
        refine Finset.card_eq_sum_card_fiberwise
          (f := fun (t : Fin (k+1) → Fin n) => fun (a : Fin k) => t a.castSucc) ?_
        intro t ht
        obtain ⟨-, htinj, htmem⟩ := Finset.mem_filter.mp ht
        rw [Finset.mem_coe, hkT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, fun a => htmem _⟩
        intro a b hab
        exact Fin.castSucc_injective k (htinj hab)
      rw [hfib]
      calc kT.card * ((W γ).card - k) = ∑ _t' ∈ kT, ((W γ).card - k) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ t' ∈ kT, (I.filter (fun t : Fin (k+1) → Fin n => (fun a : Fin k => t a.castSucc) = t')).card := by
            refine Finset.sum_le_sum fun t' ht' => ?_
            obtain ⟨-, ht'inj, ht'mem⟩ := Finset.mem_filter.mp ht'
            have himgsub : Finset.univ.image t' ⊆ W γ := by
              intro x hx
              obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
              exact ht'mem a
            have hsd : ((W γ) \ Finset.univ.image t').card = (W γ).card - k := by
              rw [Finset.card_sdiff_of_subset himgsub,
                Finset.card_image_of_injective _ ht'inj, Finset.card_univ,
                Fintype.card_fin]
            rw [← hsd]
            refine Finset.card_le_card_of_injOn
              (fun j => Fin.snoc (α := fun _ => Fin n) t' j) ?_ ?_
            · -- membership of the extension
              intro j hj
              obtain ⟨hjW, hjim⟩ := Finset.mem_sdiff.mp hj
              rw [Finset.mem_coe, Finset.mem_filter]
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
              · -- injectivity of Fin.snoc (α := fun _ => Fin n) t' j
                show Function.Injective (Fin.snoc (α := fun _ => Fin n) t' j)
                intro a b hab
                by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k
                · rw [ha, hb]
                · exfalso
                  have hb' : (b : ℕ) < k := by
                    have := b.2
                    by_contra hc
                    exact hb (Fin.ext (by rw [Fin.val_last]; omega))
                  have hbeq : b = Fin.castSucc ⟨(b : ℕ), hb'⟩ := Fin.ext rfl
                  rw [ha, hbeq, Fin.snoc_last, Fin.snoc_castSucc] at hab
                  exact hjim (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hab.symm⟩)
                · exfalso
                  have ha' : (a : ℕ) < k := by
                    have := a.2
                    by_contra hc
                    exact ha (Fin.ext (by rw [Fin.val_last]; omega))
                  have haeq : a = Fin.castSucc ⟨(a : ℕ), ha'⟩ := Fin.ext rfl
                  rw [hb, haeq, Fin.snoc_last, Fin.snoc_castSucc] at hab
                  exact hjim (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hab⟩)
                · have ha' : (a : ℕ) < k := by
                    have := a.2
                    by_contra hc
                    exact ha (Fin.ext (by rw [Fin.val_last]; omega))
                  have hb' : (b : ℕ) < k := by
                    have := b.2
                    by_contra hc
                    exact hb (Fin.ext (by rw [Fin.val_last]; omega))
                  have haeq : a = Fin.castSucc ⟨(a : ℕ), ha'⟩ := Fin.ext rfl
                  have hbeq : b = Fin.castSucc ⟨(b : ℕ), hb'⟩ := Fin.ext rfl
                  rw [haeq, hbeq, Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
                  rw [haeq, hbeq]
                  exact congrArg Fin.castSucc (ht'inj hab)
              · -- range in W
                show ∀ a, Fin.snoc (α := fun _ => Fin n) t' j a ∈ W γ
                intro a
                by_cases ha : a = Fin.last k
                · rw [ha, Fin.snoc_last]
                  exact hjW
                · have ha' : (a : ℕ) < k := by
                    have := a.2
                    by_contra hc
                    exact ha (Fin.ext (by rw [Fin.val_last]; omega))
                  have haeq : a = Fin.castSucc ⟨(a : ℕ), ha'⟩ := Fin.ext rfl
                  rw [haeq, Fin.snoc_castSucc]
                  exact ht'mem _
              · -- the fiber condition
                show (fun a : Fin k => Fin.snoc (α := fun _ => Fin n) t' j a.castSucc) = t'
                funext a
                rw [Fin.snoc_castSucc]
            · -- injectivity of the extension map
              intro j _ j' _ heq
              have := congrFun heq (Fin.last k)
              simpa [Fin.snoc_last] using this
    -- degenerate count
    have hdeg : (I.filter (fun t => ¬ residual dom k t u₁ ≠ 0)).card
        ≤ kT.card * μ := by
      have hsub3 : I.filter (fun t => ¬ residual dom k t u₁ ≠ 0)
          ⊆ Finset.univ.filter (fun t : Fin (k+1) → Fin n =>
            (Function.Injective t ∧ ∀ a, t a ∈ W γ) ∧
            ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
              ∀ a, c (t a) = u₁ (t a)) := by
        intro t ht
        obtain ⟨htI, htres⟩ := Finset.mem_filter.mp ht
        obtain ⟨-, htinj, htmem⟩ := Finset.mem_filter.mp htI
        push Not at htres
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, ⟨htinj, htmem⟩, hconv t htinj htres⟩
      exact le_trans (Finset.card_le_card hsub3)
        (degenerate_tuples_card_le dom (W γ) hμ)
    -- the owned set contains the nondegenerate injective tuples
    have hown : I.filter (fun t => residual dom k t u₁ ≠ 0) ⊆ 𝒯 γ := by
      intro t ht
      obtain ⟨htI, htres⟩ := Finset.mem_filter.mp ht
      obtain ⟨-, htinj, htmem⟩ := Finset.mem_filter.mp htI
      rw [h𝒯, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨htinj, htmem⟩, htres⟩
    -- assemble
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := I) (p := fun t => residual dom k t u₁ ≠ 0)
    have hkTge : (n - w).descFactorial k ≤ kT.card := by
      refine le_trans ?_ (injective_tuples_card_ge_descFactorial (W γ))
      exact Nat.descFactorial_le _ hSsz
    calc (n - w).descFactorial k * (n - w - k - μ)
        ≤ kT.card * ((W γ).card - k - μ) := by
          refine Nat.mul_le_mul hkTge ?_
          omega
      _ ≤ (𝒯 γ).card := by
          have h1 : kT.card * ((W γ).card - k - μ)
              ≤ kT.card * ((W γ).card - k) - kT.card * μ := by
            rw [← Nat.mul_sub]
          have h2 : kT.card * ((W γ).card - k) - kT.card * μ
              ≤ I.card - kT.card * μ := by omega
          have h3 : I.card - kT.card * μ
              ≤ (I.filter (fun t => residual dom k t u₁ ≠ 0)).card := by omega
          exact le_trans h1 (le_trans h2 (le_trans h3
            (Finset.card_le_card hown)))

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.injective_tuples_card_ge_descFactorial
#print axioms ProximityGap.Ownership.degenerate_tuples_card_le
#print axioms ProximityGap.Ownership.extension_of_residual_eq_zero
#print axioms ProximityGap.Ownership.badScalars_card_mul_le_of_agreement
