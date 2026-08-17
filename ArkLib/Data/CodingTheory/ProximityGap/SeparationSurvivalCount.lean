/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SeparatingCoordsCount

/-!
# The combined separation+survival count — the GG25 §4.3 line-decodability core (issue #389)

The genuine composition behind GG25 §4.3 curve-decodability: a uniformly random coordinate tuple
both **separates** the list span `H` **and** lands entirely in a codeword's **agreement set** `T`.
For a `τ`-subspace-design `C` (`0 ≤ θ ≤ θ' ≤ 1`, `θ` bounding `τ`), `H ≤ C` with `finrank H ≤ r`,
and `T` of density `≥ θ'`:

  `card_surv_ge` : `(θ'−θ)^r · n^r ≤ |{v : Fin r → ι | v separates H ∧ ∀ j, v j ∈ T}|`,

i.e. `Pr_v[v separates H ∧ v ⊆ T] ≥ (θ'−θ)^r`. The proof is a single peeling induction
(`card_surv_decomp`) in which each step picks a first coordinate that is **both** in `T` **and**
reducing `H` — and there are `≥ (θ'−θ)·n` such (`|T ∩ support(H)| ≥ |T| − |fullVanish(H)| ≥
θ'n − θn`). This unifies the separation factor (`SeparatingCoordsCount.card_separates_ge`, the
`T = univ` case) and the agreement-hitting factor (`IidCoordinateHit`): a positive-probability `v`
separates the list span while every close codeword survives on it, so by
`SeparatingCoordinates.separated_agree_subsingleton` it is determined — exactly the GG25 §4.3
line-decodability conclusion (given the CZ25 list-recovery that produces the low-dimensional `H`).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

/-- The forall-in-`T` predicate splits over the first coordinate. -/
lemma forall_mem_cons {r : ℕ} (T : Finset ι) (i₀ : ι) (w : Fin r → ι) :
    (∀ j, (Fin.cons i₀ w : Fin (r + 1) → ι) j ∈ T) ↔ (i₀ ∈ T ∧ ∀ j, w j ∈ T) := by
  constructor
  · intro hv; exact ⟨by have := hv 0; rwa [Fin.cons_zero] at this,
      fun j => by have := hv j.succ; rwa [Fin.cons_succ] at this⟩
  · rintro ⟨h0, hw⟩ j; refine Fin.cases ?_ ?_ j
    · rwa [Fin.cons_zero]
    · intro j; rw [Fin.cons_succ]; exact hw j

open Classical in
/-- Counting decomposition for the combined predicate over the first coordinate. -/
lemma card_surv_decomp {s r : ℕ} (H : Submodule F (ι → Fin s → F)) (T : Finset ι) :
    (univ.filter (fun v : Fin (r + 1) → ι => Separates H v ∧ ∀ j, v j ∈ T)).card
      = ∑ i₀ ∈ T, (univ.filter (fun w : Fin r → ι =>
          Separates (H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin (r + 1) → ι => v 0)
        (t := T) (fun v hv => (mem_filter.mp hv).2.2 0)]
  refine Finset.sum_congr rfl (fun i₀ hi₀T => ?_)
  have hcons_inj : Function.Injective (fun w : Fin r → ι => (Fin.cons i₀ w : Fin (r + 1) → ι)) := by
    intro w w' hww
    have := congrArg Fin.tail hww; rwa [Fin.tail_cons, Fin.tail_cons] at this
  rw [show ((univ.filter (fun v : Fin (r + 1) → ι => Separates H v ∧ ∀ j, v j ∈ T)).filter
            (fun v => v 0 = i₀))
        = (univ.filter (fun w : Fin r → ι =>
            Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).image
            (fun w : Fin r → ι => (Fin.cons i₀ w : Fin (r + 1) → ι))
      from ?_]
  · exact Finset.card_image_of_injective _ hcons_inj
  · ext v
    simp only [mem_filter, mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨⟨hSep, hmem⟩, hv0⟩
      refine ⟨Fin.tail v, ⟨?_, ?_⟩, by rw [← hv0, Fin.cons_self_tail]⟩
      · exact (separates_cons H i₀ (Fin.tail v)).mp (by rw [← hv0, Fin.cons_self_tail]; exact hSep)
      · exact ((forall_mem_cons T i₀ (Fin.tail v)).mp (by rw [← hv0, Fin.cons_self_tail]; exact hmem)).2
    · rintro ⟨w, ⟨hSep, hmem⟩, rfl⟩
      refine ⟨⟨(separates_cons H i₀ w).mpr hSep, ?_⟩, by simp [Fin.cons_zero]⟩
      exact (forall_mem_cons T i₀ w).mpr ⟨hi₀T, hmem⟩

open Classical in
/-- **The combined separation+survival count (GG25 §4.3 line-decodability core).** For a
`τ`-subspace-design `C` (`0 ≤ θ ≤ θ' ≤ 1`, `θ` bounding `τ`), `H ≤ C` with `finrank H ≤ r`, and an
agreement set `T` of density `≥ θ'`, at least a `(θ'−θ)^r` fraction of the `n^r` tuples both separate
`H` and lie entirely in `T`. -/
theorem card_surv_ge {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθθ' : θ ≤ θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    (θ' - θ) ^ r * (Fintype.card ι : ℝ) ^ r
      ≤ ((univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card : ℝ) := by
  have hd0 : (0 : ℝ) ≤ θ' - θ := by linarith
  induction r generalizing H with
  | zero =>
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    have hone : (univ.filter (fun v : Fin 0 → ι => Separates H v ∧ ∀ j, v j ∈ T)) = univ := by
      ext v; simp only [mem_filter, mem_univ, true_and, iff_true]
      refine ⟨by simp [Separates, hH], fun j => j.elim0⟩
    rw [hone]; simp
  | succ k ih =>
    by_cases hH : H = ⊥
    · have hall : (univ.filter (fun v : Fin (k + 1) → ι => Separates H v ∧ ∀ j, v j ∈ T))
          = Fintype.piFinset (fun _ : Fin (k + 1) => T) := by
        ext v; simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
        exact ⟨fun hv => hv.2, fun hv => ⟨by simp [Separates, hH], hv⟩⟩
      rw [hall, Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
      have hstep : (θ' - θ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) := by nlinarith [hT, hθ0]
      calc (θ' - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          = ((θ' - θ) * (Fintype.card ι : ℝ)) ^ (k + 1) := by rw [mul_pow]
        _ ≤ (T.card : ℝ) ^ (k + 1) := by gcongr
    · have hrank1 : 1 ≤ Module.finrank F H := by
        rw [Nat.one_le_iff_ne_zero]; exact fun h0 => hH (Submodule.finrank_eq_zero.mp h0)
      rw [card_surv_decomp, Nat.cast_sum]
      set Tsupp := T.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))) with hTsupp
      -- `|T ∩ support| ≥ (θ'−θ)·n`
      have hTsuppcard : (θ' - θ) * (Fintype.card ι : ℝ) ≤ (Tsupp.card : ℝ) := by
        have hfull : ((univ.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ)
            ≤ θ * (Fintype.card ι : ℝ) :=
          le_trans (subspaceDesign_fullVanish_card_le h hrank1 hHC rfl)
            (mul_le_mul_of_nonneg_right (hθ _) (by positivity))
        have hsplit : (T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card + Tsupp.card = T.card := by
          rw [hTsupp]
          exact Finset.filter_card_add_filter_neg_card_eq_card
            (fun i₀ : ι => H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))
        have hsub2 : ((T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ)
            ≤ ((univ.filter (fun i₀ : ι => H ≤ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ T))
        have hsplitℝ : ((T.filter (fun i₀ : ι => H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀))).card : ℝ) + (Tsupp.card : ℝ)
            = (T.card : ℝ) := by exact_mod_cast hsplit
        nlinarith [hfull, hsplitℝ, hsub2, hT]
      -- per `i₀ ∈ Tsupp`: IH applies (reducing ⇒ dim drops)
      have hIH : ∀ i₀ ∈ Tsupp, (θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k
            ≤ ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) := by
        intro i₀ hi₀
        rw [hTsupp, mem_filter] at hi₀
        have hlt : H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) < H :=
          lt_of_le_of_ne inf_le_left (fun heq => hi₀.2 (heq ▸ inf_le_right))
        have hdrop : Module.finrank F (H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) : Submodule F (ι → Fin s → F)) ≤ k := by
          have := Submodule.finrank_lt_finrank_of_lt hlt; omega
        exact ih _ (le_trans inf_le_left hHC) hdrop
      calc (θ' - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          = ((θ' - θ) * (Fintype.card ι : ℝ)) * ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by ring
        _ ≤ (Tsupp.card : ℝ) * ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_right hTsuppcard (by positivity)
        _ = ∑ _i₀ ∈ Tsupp, ((θ' - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i₀ ∈ Tsupp, ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) :=
            Finset.sum_le_sum hIH
        _ ≤ ∑ i₀ ∈ T, ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w ∧ ∀ j, w j ∈ T)).card : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by rw [hTsupp]; exact Finset.filter_subset _ _) ?_
            intro i₀ _ _; positivity

end ProximityGap

#print axioms ProximityGap.card_surv_decomp
#print axioms ProximityGap.card_surv_ge
