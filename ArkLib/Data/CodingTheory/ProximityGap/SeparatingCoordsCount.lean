/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignFullVanish

/-!
# The sequential separation count — the `η^r` separation probability, by counting (issue #389)

The counting form of the GG25 §4.3 / `[KRSW23, Tam24]` `η^r` separation probability, established
*without measure theory*: for a `τ`-subspace-design `C` with `0 ≤ θ ≤ 1` bounding `τ`, and `H ≤ C`
with `finrank H ≤ r`, at least a `(1−θ)^r` fraction of all `n^r` coordinate tuples separate `H`:

  `card_separates_ge` : `(1−θ)^r · n^r ≤ |{v : Fin r → ι | v separates H}|`.

Equivalently `Pr_{v ←$ᵖ (Fin r → ι)}[v separates H] ≥ (1−θ)^r` (via the uniform law on `Fin r → ι`).

The proof is a peeling induction decomposing the count over the first coordinate
(`v ↦ (v 0, Fin.tail v)`, `separates_cons`): the reducing first-coordinates are the support of `H`,
of size `≥ (1−θ)·n` (`subspaceDesign_support_card_ge`), and each contributes `≥ (1−θ)^{r−1}·n^{r−1}`
by the inductive hypothesis applied to the strictly-smaller `H ⊓ ker proj_{i₀}`. Together with the
agreement-hitting kernel (`IidCoordinateHit`) this is the full `η^r` ingredient subspace-design
list-decoding needs for curve-decodability. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

/-- `⨅` over `Fin (r+1)` peels off the first index. -/
lemma iInf_fin_succ {α : Type*} [CompleteLattice α] {r : ℕ} (f : Fin (r + 1) → α) :
    ⨅ j, f j = f 0 ⊓ ⨅ j : Fin r, f j.succ := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ)
  · refine le_iInf fun i => ?_
    refine Fin.cases ?_ ?_ i
    · exact inf_le_left
    · exact fun j => le_trans inf_le_right (iInf_le _ j)

/-- `v : Fin r → ι` separates `H` if the listed coordinates pin `H` to `⊥`. -/
def Separates {s r : ℕ} (H : Submodule F (ι → Fin s → F)) (v : Fin r → ι) : Prop :=
  H ⊓ (⨅ j : Fin r, LinearMap.ker
    (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) (v j))) = ⊥

/-- `cons i₀ w` separates `H` iff `w` separates `H ⊓ ker proj_{i₀}`. -/
lemma separates_cons {s r : ℕ} (H : Submodule F (ι → Fin s → F)) (i₀ : ι) (w : Fin r → ι) :
    Separates H (Fin.cons i₀ w)
      ↔ Separates (H ⊓ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w := by
  unfold Separates
  rw [iInf_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [inf_assoc]

open Classical in
/-- Counting decomposition over the first coordinate. -/
lemma card_separates_decomp {s r : ℕ} (H : Submodule F (ι → Fin s → F)) :
    (univ.filter (fun v : Fin (r + 1) → ι => Separates H v)).card
      = ∑ i₀ : ι, (univ.filter (fun w : Fin r → ι =>
          Separates (H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin (r + 1) → ι => v 0)
        (t := (univ : Finset ι)) (fun v _ => mem_univ _)]
  refine Finset.sum_congr rfl (fun i₀ _ => ?_)
  have hcons_inj : Function.Injective (fun w : Fin r → ι => (Fin.cons i₀ w : Fin (r + 1) → ι)) := by
    intro w w' hww
    have := congrArg Fin.tail hww; rwa [Fin.tail_cons, Fin.tail_cons] at this
  rw [show (univ.filter (fun v : Fin (r + 1) → ι => Separates H v)).filter (fun v => v 0 = i₀)
        = (univ.filter (fun w : Fin r → ι =>
            Separates (H ⊓ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w)).image
            (fun w : Fin r → ι => (Fin.cons i₀ w : Fin (r + 1) → ι))
      from ?_]
  · exact Finset.card_image_of_injective _ hcons_inj
  · ext v
    simp only [mem_filter, mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hSep, hv0⟩
      refine ⟨Fin.tail v, ?_, by rw [← hv0, Fin.cons_self_tail]⟩
      exact (separates_cons H i₀ (Fin.tail v)).mp (by rw [← hv0, Fin.cons_self_tail]; exact hSep)
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (separates_cons H i₀ w).mpr hw
      · simp [Fin.cons_zero]

open Classical in
theorem card_separates_ge {s : ℕ} {τ : ℕ → ℝ} {θ : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    (1 - θ) ^ r * (Fintype.card ι : ℝ) ^ r
      ≤ ((univ.filter (fun v : Fin r → ι => Separates H v)).card : ℝ) := by
  induction r generalizing H with
  | zero =>
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    simp only [pow_zero, one_mul]
    have : (univ.filter (fun v : Fin 0 → ι => Separates H v)) = univ := by
      ext v; simp only [mem_filter, mem_univ, true_and, iff_true]
      simp [Separates, hH]
    rw [this]; simp
  | succ k ih =>
    have h1θ : (0 : ℝ) ≤ 1 - θ := by linarith
    by_cases hH : H = ⊥
    · -- every tuple separates `⊥`; the count is `n^{k+1}`
      have hall : (univ.filter (fun v : Fin (k + 1) → ι => Separates H v)) = univ := by
        ext v; simp only [mem_filter, mem_univ, true_and, iff_true]; simp [Separates, hH]
      rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      have hle1 : (1 - θ) ^ (k + 1) ≤ 1 := pow_le_one₀ h1θ (by linarith)
      calc (1 - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          ≤ 1 * (Fintype.card ι : ℝ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = ((Fintype.card ι ^ (k + 1) : ℕ) : ℝ) := by push_cast; ring
    · have hrank1 : 1 ≤ Module.finrank F H := by
        rw [Nat.one_le_iff_ne_zero]; exact fun h0 => hH (Submodule.finrank_eq_zero.mp h0)
      rw [card_separates_decomp, Nat.cast_sum]
      -- the reducing first-coordinates (support of `H`) are `≥ (1−θ)·n`
      have hsupp : (1 - θ) * (Fintype.card ι : ℝ)
          ≤ ((univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))).card : ℝ) := by
        have key : (1 - τ (Module.finrank F H)) * (Fintype.card ι : ℝ)
            ≤ ((univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))).card : ℝ) :=
          subspaceDesign_support_card_ge h hrank1 hHC rfl
        refine le_trans ?_ key
        gcongr
        linarith [hθ (Module.finrank F H)]
      -- each reducing first-coordinate contributes `≥ (1−θ)^k·n^k` by the IH
      have hIH : ∀ i₀ ∈ (univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))),
          (1 - θ) ^ k * (Fintype.card ι : ℝ) ^ k
            ≤ ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w)).card : ℝ) := by
        intro i₀ hi₀
        rw [mem_filter] at hi₀
        have hlt : H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) < H :=
          lt_of_le_of_ne inf_le_left (fun heq => hi₀.2 (heq ▸ inf_le_right))
        have hdrop : Module.finrank F (H ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) : Submodule F (ι → Fin s → F)) ≤ k := by
          have := Submodule.finrank_lt_finrank_of_lt hlt; omega
        exact ih _ (le_trans inf_le_left hHC) hdrop
      calc (1 - θ) ^ (k + 1) * (Fintype.card ι : ℝ) ^ (k + 1)
          = ((1 - θ) * (Fintype.card ι : ℝ)) * ((1 - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by ring
        _ ≤ ((univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))).card : ℝ)
            * ((1 - θ) ^ k * (Fintype.card ι : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_right hsupp (by positivity)
        _ = ∑ _i₀ ∈ (univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))),
              ((1 - θ) ^ k * (Fintype.card ι : ℝ) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i₀ ∈ (univ.filter (fun i₀ : ι => ¬ (H ≤ LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)))),
              ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w)).card : ℝ) :=
            Finset.sum_le_sum hIH
        _ ≤ ∑ i₀ : ι, ((univ.filter (fun w : Fin k → ι => Separates (H ⊓ LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) w)).card : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro i₀ _ _; positivity

end ProximityGap

#print axioms ProximityGap.card_separates_ge
