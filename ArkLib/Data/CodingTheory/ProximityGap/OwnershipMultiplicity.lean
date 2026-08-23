/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipBound

/-!
# The multiplicity theorem (#371): the first unconditional window bound (k = 1)

The ownership count instantiated at `k = 1`: the residual of a pair is the
difference `u₁(t 1) − u₁(t 0)`, ownership is the number of `u₁`-unequal ordered
pairs in the witness, and if `u₁` takes each value at most `μ` times then every
witness of size `≥ n − w` owns at least `(n−w)·(n−w−μ)` pairs.  Hence

  **`#bad · ((n−w)·(n−w−μ)) ≤ n²`**

— radius-free, valid in the window beyond the ladder reach, where no unconditional
bound existed for these stacks.  At the probe extremal `(13,6,1,w=2,μ=2)` this gives
`#bad ≤ 36/8 → 4` against the true `3`: the count explains the window cap.  The
general-`k` analogue (`μ` → max agreement with degree-`< k` polynomials) is the
ownership route to the full window residual.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The `k = 1` residual is the pair difference. -/
theorem residual_one (dom : Fin n ↪ F) (t : Fin 2 → Fin n) (y : Fin n → F) :
    residual dom 1 t y = y (t 1) - y (t 0) := by
  unfold residual borderedMatrix
  rw [Matrix.det_fin_two]
  have h00 : ((0 : Fin 2) : ℕ) < 1 := by norm_num
  have h11 : ¬ ((1 : Fin 2) : ℕ) < 1 := by norm_num
  rw [if_pos h00, if_pos h00, if_neg h11, if_neg h11]
  simp only [Fin.val_zero, pow_zero, one_mul, mul_one]

open Classical in
/-- **The pair-ownership lower bound**: on a set `S` where every value of `u₁`
appears at most `μ` times, at least `|S|·(|S|−μ)` ordered pairs are `u₁`-unequal. -/
theorem owned_pairs_card_ge (S : Finset (Fin n)) {u₁ : Fin n → F} {μ : ℕ}
    (hμ : ∀ v : F, (S.filter (fun i => u₁ i = v)).card ≤ μ) :
    S.card * (S.card - μ)
      ≤ ((S ×ˢ S).filter (fun p => u₁ p.1 ≠ u₁ p.2)).card := by
  set eqc := ((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).card with heqc
  set uneqc := ((S ×ˢ S).filter (fun p => u₁ p.1 ≠ u₁ p.2)).card with huneqc
  have hsplit : eqc + uneqc = S.card * S.card := by
    rw [heqc, huneqc]
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S ×ˢ S) (p := fun p => u₁ p.1 = u₁ p.2)
    rw [Finset.card_product] at h
    exact h
  -- fiberwise count of the equal pairs
  have heqle : eqc ≤ μ * S.card := by
    rw [heqc]
    have hfib : ((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).card
        = ∑ i ∈ S, (((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).filter
            (fun p => p.1 = i)).card := by
      refine Finset.card_eq_sum_card_fiberwise (f := Prod.fst) ?_
      intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [hfib]
    calc ∑ i ∈ S, (((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).filter
          (fun p => p.1 = i)).card
        ≤ ∑ i ∈ S, μ := by
          refine Finset.sum_le_sum fun i hi => ?_
          -- the fiber injects into the filter of equal u₁-value via snd
          have hinj : ∀ p ∈ ((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).filter
              (fun p => p.1 = i), p.2 ∈ S.filter (fun j => u₁ j = u₁ i) := by
            intro p hp
            obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
            obtain ⟨hpa, hpb⟩ := Finset.mem_filter.mp hp1
            rw [Finset.mem_filter]
            refine ⟨(Finset.mem_product.mp hpa).2, ?_⟩
            rw [← hpb]
            rw [hp2]
          calc (((S ×ˢ S).filter (fun p => u₁ p.1 = u₁ p.2)).filter
              (fun p => p.1 = i)).card
              ≤ (S.filter (fun j => u₁ j = u₁ i)).card := by
                refine Finset.card_le_card_of_injOn Prod.snd hinj ?_
                intro p hp p' hp' hsnd
                have h1 := (Finset.mem_filter.mp hp).2
                have h2 := (Finset.mem_filter.mp hp').2
                exact Prod.ext (h1.trans h2.symm) hsnd
            _ ≤ μ := hμ (u₁ i)
      _ = μ * S.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- assemble in ℕ
  have hmulsub : S.card * (S.card - μ) = S.card * S.card - S.card * μ :=
    Nat.mul_sub _ _ _
  rw [hmulsub]
  have hcomm : S.card * μ = μ * S.card := mul_comm _ _
  omega

open Classical in
/-- **THE MULTIPLICITY THEOREM** — the first unconditional window bound: for `k = 1`
and a direction `u₁` of value-multiplicity ≤ μ, at every radius `δ ≤ w/n`:

  `#bad · ((n−w)·(n−w−μ)) ≤ n²`. -/
theorem badScalars_card_mul_le_of_multiplicity (dom : Fin n ↪ F)
    {w : ℕ} (hw : w ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {μ : ℕ}
    (hμ : ∀ v : F, (Finset.univ.filter (fun i => u₁ i = v)).card ≤ μ) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w) * (n - w - μ))
      ≤ Fintype.card (Fin 2 → Fin n) := by
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ) with hbad
  -- choose witnesses
  have hch : ∀ γ ∈ bad, ∃ S : Finset (Fin n),
      ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card (Fin n)) ∧
      ∀ t : Fin 2 → Fin n, (∀ a, t a ∈ S) →
        residual dom 1 t u₁ ≠ 0 →
        residual dom 1 t u₀ + γ * residual dom 1 t u₁ = 0 := by
    intro γ hγ
    exact mcaEvent_owned_tuples dom (le_refl 1) δ (Finset.mem_filter.mp hγ).2
  choose! W hWsz hWprop using hch
  -- the owned tuple sets
  set 𝒯 : F → Finset (Fin 2 → Fin n) := fun γ =>
    Finset.univ.filter (fun t => (∀ a, t a ∈ W γ) ∧ u₁ (t 0) ≠ u₁ (t 1)) with h𝒯
  refine badScalars_card_mul_le_ownership dom 1 u₀ u₁ bad _ 𝒯 ?_ ?_
  · -- the ownership property
    intro γ hγ t ht
    obtain ⟨htW, htne⟩ := (Finset.mem_filter.mp ht).2
    have hres1 : residual dom 1 t u₁ ≠ 0 := by
      rw [residual_one]
      exact sub_ne_zero.mpr (Ne.symm htne)
    exact ⟨hres1, hWprop γ hγ t htW hres1⟩
  · -- the ownership size
    intro γ hγ
    -- witness size ≥ n − w
    have hSsz : n - w ≤ (W γ).card := by
      have h1 := hWsz γ hγ
      have h2 : ((n - w : ℕ) : ℝ≥0) ≤ ((W γ).card : ℝ≥0) := by
        have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
          rw [Nat.cast_tsub]
        have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
          rw [Fintype.card_fin]
        calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
          _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
              exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
          _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
              rw [tsub_mul, one_mul, hcardn]
          _ ≤ ((W γ).card : ℝ≥0) := h1
      exact_mod_cast h2
    -- tuples ↔ pairs
    have hμW : ∀ v : F, ((W γ).filter (fun i => u₁ i = v)).card ≤ μ := by
      intro v
      exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.subset_univ _))) (hμ v)
    have hpairs := owned_pairs_card_ge (W γ) hμW
    -- card of the tuple set = card of the pair set
    have hbij : (𝒯 γ).card
        = (((W γ) ×ˢ (W γ)).filter (fun p => u₁ p.1 ≠ u₁ p.2)).card := by
      refine Finset.card_nbij (fun t => (t 0, t 1)) ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht
        obtain ⟨-, htW, htne⟩ := ht
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨htW 0, htW 1⟩, htne⟩
      · intro t ht t' ht' heq
        funext a
        have h0 : t 0 = t' 0 := congrArg Prod.fst heq
        have h1 : t 1 = t' 1 := congrArg Prod.snd heq
        fin_cases a
        · exact h0
        · exact h1
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨hpa, hpb⟩ := hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpa
        refine ⟨![p.1, p.2], ?_, rfl⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun a => ?_, hpb⟩
        fin_cases a
        · exact hp1
        · exact hp2
    rw [hbij]
    calc (n - w) * (n - w - μ)
        ≤ (W γ).card * ((W γ).card - μ) := by
          have h1 : n - w - μ ≤ (W γ).card - μ := by omega
          exact Nat.mul_le_mul hSsz h1
      _ ≤ _ := hpairs

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residual_one
#print axioms ProximityGap.Ownership.owned_pairs_card_ge
#print axioms ProximityGap.Ownership.badScalars_card_mul_le_of_multiplicity
