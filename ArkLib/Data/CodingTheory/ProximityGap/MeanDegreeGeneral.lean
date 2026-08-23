/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PencilDegreeGeneral
import ArkLib.Data.CodingTheory.ProximityGap.MeanDegreeDeepBand

/-!
# THE MEAN-DEGREE LAW AT GENERAL PAIRWISE INTERSECTION (#389, general-`k` complete)

The branch analysis at pairwise intersection `≤ s`, completing the general-`k` lift:

> **`mean_degree_law_deep_general`** — for a family of sets with sizes in `[t, cap]`,
> pairwise intersecting in `≤ s` points (`1 ≤ s < t`), under the deep condition
> `2s·cap·C(n,s)·(n−s) ≤ t²·(t−s)·C(t,s)`:  **`Σ_{A∈S} |A| ≤ 2n`.**

Proof: (i) general Bonferroni (`degree_sum_le_general`) + bootstrap:
`u·t² ≤ n·t² + s·u²`.  (ii) If `2s·u ≤ t²`: cancellation gives `u ≤ 2n`.
(iii) Else: the `s`-subset incidence swap (`Σ_Y d_Y = Σ_A C(|A|,s)`) and the `s`-set
pencil bound give `Σ_A C(|A|,s)·(t−s) ≤ C(n,s)·(n−s)`; with `C(|A|,s) ≥ C(t,s)` and
`|A| ≤ cap`: `u·(t−s)·C(t,s) ≤ cap·C(n,s)·(n−s)`, so `2s·u·(t−s)·C(t,s) ≤
t²·(t−s)·C(t,s)` — contradiction with `2s·u > t²` after cancellation.

At `s = k−1`, `t = k+m+1`, `cap = 2k+m+1` this extends the deep-band supply theorem
to every rate `k` (assembly mirrors `subJohnsonSupplyResidual_deep_band`).
Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {n : ℕ} [NeZero n]

open Classical in
/-- The `s`-subset incidence swap: `Σ_{|Y|=s} #{A ∈ S : Y ⊆ A} = Σ_{A∈S} C(|A|, s)`. -/
theorem subset_incidence_swap (S : Finset (Finset (Fin n))) (s : ℕ) :
    ∑ Y ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      (S.filter (fun A => Y ⊆ A)).card
      = ∑ A ∈ S, A.card.choose s := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.card_filter]
  have h1 : ((Finset.univ : Finset (Fin n)).powersetCard s).filter (fun Y => Y ⊆ A)
      = A.powersetCard s := by
    ext Y
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hc⟩, hsub⟩
      exact ⟨hsub, hc⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨⟨Finset.subset_univ _, hc⟩, hsub⟩
  rw [h1, Finset.card_powersetCard]

open Classical in
/-- **THE GENERAL MEAN-DEGREE LAW (deep condition)**: sizes in `[t, cap]`, pairwise
`≤ s`, and `2s·cap·C(n,s)·(n−s) ≤ t²·(t−s)·C(t,s)` give `Σ|A| ≤ 2n`. -/
theorem mean_degree_law_deep_general {S : Finset (Finset (Fin n))}
    {t s cap : ℕ} (hs : 1 ≤ s) (hst : s + 1 ≤ t)
    (hsize : ∀ A ∈ S, t ≤ A.card) (hcap : ∀ A ∈ S, A.card ≤ cap)
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ s)
    (hdeep : 2 * s * cap * ((n.choose s) * (n - s))
      ≤ t ^ 2 * ((t - s) * t.choose s)) :
    ∑ A ∈ S, A.card ≤ 2 * n := by
  classical
  set u := ∑ A ∈ S, A.card with hu
  set L := S.card with hL
  have hLt : L * t ≤ u := by
    calc L * t = ∑ _A ∈ S, t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ A ∈ S, A.card := Finset.sum_le_sum hsize
  have hBon : u ≤ n + s * (L * L) := by
    have h := degree_sum_le_general hpair
    rw [degree_sum_eq_size_sum, ← hu, ← hL] at h
    have hLL : L * (L - 1) ≤ L * L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have : s * (L * (L - 1)) ≤ s * (L * L) := Nat.mul_le_mul_left _ hLL
    omega
  have hquad : u * t ^ 2 ≤ n * t ^ 2 + s * (u * u) := by
    calc u * t ^ 2 ≤ (n + s * (L * L)) * t ^ 2 := Nat.mul_le_mul_right _ hBon
    _ = n * t ^ 2 + s * ((L * t) * (L * t)) := by ring
    _ ≤ n * t ^ 2 + s * (u * u) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul hLt hLt)) _
  -- the summed s-set pencil bound
  have hpencil : (∑ A ∈ S, A.card.choose s) * (t - s) ≤ n.choose s * (n - s) := by
    have hpt : ∀ Y ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        (S.filter (fun A => Y ⊆ A)).card * (t - s) ≤ n - s := by
      intro Y hY
      obtain ⟨-, hYcard⟩ := Finset.mem_powersetCard.mp hY
      have h := pencil_family_card_le_general (S := S.filter (fun A => Y ⊆ A))
        (Y := Y) (r := t - s) ?_ ?_
      · rwa [hYcard] at h
      · intro A hA
        obtain ⟨hAS, hYA⟩ := Finset.mem_filter.mp hA
        refine ⟨hYA, ?_⟩
        have := hsize A hAS
        omega
      · intro A hA B hB hne
        obtain ⟨hAS, hYA⟩ := Finset.mem_filter.mp hA
        obtain ⟨hBS, hYB⟩ := Finset.mem_filter.mp hB
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · exact Finset.subset_inter hYA hYB
        · rw [hYcard]
          exact hpair A hAS B hBS hne
    calc (∑ A ∈ S, A.card.choose s) * (t - s)
        = (∑ Y ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
            (S.filter (fun A => Y ⊆ A)).card) * (t - s) := by
          rw [subset_incidence_swap]
    _ = ∑ Y ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          (S.filter (fun A => Y ⊆ A)).card * (t - s) := by rw [Finset.sum_mul]
    _ ≤ ∑ _Y ∈ (Finset.univ : Finset (Fin n)).powersetCard s, (n - s) :=
          Finset.sum_le_sum hpt
    _ = n.choose s * (n - s) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin]
  -- two branches
  rcases Nat.lt_or_ge (t ^ 2) (2 * s * u) with hbig | hsmall
  · -- 2s·u > t²: the pencil/cap exclusion
    exfalso
    -- u·(t−s)·C(t,s) ≤ cap·C(n,s)·(n−s)
    have huC : u * ((t - s) * t.choose s) ≤ cap * (n.choose s * (n - s)) := by
      have hC : ∀ A ∈ S, A.card * (t.choose s) ≤ cap * A.card.choose s := by
        intro A hA
        have h1 : t.choose s ≤ A.card.choose s :=
          Nat.choose_le_choose _ (hsize A hA)
        calc A.card * t.choose s ≤ cap * t.choose s :=
            Nat.mul_le_mul_right _ (hcap A hA)
        _ ≤ cap * A.card.choose s := Nat.mul_le_mul_left _ h1
      have hsumC : u * t.choose s ≤ cap * (∑ A ∈ S, A.card.choose s) := by
        calc u * t.choose s = ∑ A ∈ S, A.card * t.choose s := by
              rw [hu, Finset.sum_mul]
        _ ≤ ∑ A ∈ S, cap * A.card.choose s := Finset.sum_le_sum hC
        _ = cap * (∑ A ∈ S, A.card.choose s) := by rw [Finset.mul_sum]
      calc u * ((t - s) * t.choose s) = (u * t.choose s) * (t - s) := by ring
      _ ≤ (cap * (∑ A ∈ S, A.card.choose s)) * (t - s) :=
          Nat.mul_le_mul_right _ hsumC
      _ = cap * ((∑ A ∈ S, A.card.choose s) * (t - s)) := by ring
      _ ≤ cap * (n.choose s * (n - s)) := Nat.mul_le_mul_left _ hpencil
    -- 2s·u·(t−s)·C(t,s) ≤ 2s·cap·C(n,s)(n−s) ≤ t²·(t−s)·C(t,s) < 2s·u·(t−s)·C(t,s)
    have hpos : 0 < (t - s) * t.choose s :=
      Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    have hchain : 2 * s * (u * ((t - s) * t.choose s))
        ≤ t ^ 2 * ((t - s) * t.choose s) := by
      calc 2 * s * (u * ((t - s) * t.choose s))
          ≤ 2 * s * (cap * (n.choose s * (n - s))) :=
            Nat.mul_le_mul_left _ huC
      _ = 2 * s * cap * (n.choose s * (n - s)) := by ring
      _ ≤ t ^ 2 * ((t - s) * t.choose s) := hdeep
    have hfinal : 2 * s * u ≤ t ^ 2 := by
      have h := hchain
      rw [show 2 * s * (u * ((t - s) * t.choose s))
          = (2 * s * u) * ((t - s) * t.choose s) from by ring] at h
      exact Nat.le_of_mul_le_mul_right h hpos
    omega
  · -- 2s·u ≤ t²: cancellation
    have h2uu : 2 * (s * (u * u)) ≤ u * t ^ 2 := by
      calc 2 * (s * (u * u)) = (2 * s * u) * u := by ring
      _ ≤ t ^ 2 * u := Nat.mul_le_mul_right _ hsmall
      _ = u * t ^ 2 := by ring
    have hA : u * t ^ 2 ≤ 2 * (n * t ^ 2) := by omega
    have ht2 : 0 < t ^ 2 := by
      have h0 : 0 < t := by omega
      positivity
    have h := hA
    rw [show 2 * (n * t ^ 2) = (2 * n) * t ^ 2 from by ring] at h
    exact Nat.le_of_mul_le_mul_right h ht2

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.subset_incidence_swap
#print axioms ProximityGap.PairRank.mean_degree_law_deep_general
