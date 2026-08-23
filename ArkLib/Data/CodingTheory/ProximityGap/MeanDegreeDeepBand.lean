/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CrossingCountBound

/-!
# THE MEAN-DEGREE LAW ON THE DEEP BANDS (#389, brick 2 — the supply theorem)

Joins the landed crossing/Bonferroni step to the landed pencil bound through the
bootstrap and the two-branch arithmetic, proving the thread's derivation:

> **`mean_degree_law_deep`** — for a family of `≥ t`-sized sets pairwise intersecting
> in `≤ 1` point, with `2n² ≤ t²(t−1)`:  **`Σ_{A∈S} |A| ≤ 2n`** — the mean-degree law.

Proof: `Σ|A| = Σ_x d_x =: u`.  (i) Bonferroni (`degree_sum_le`): `u ≤ n + L(L−1)`;
with `Lt ≤ u` (sizes): `u·t² ≤ n·t² + u²`.  (ii) If `2u ≤ t²`: `2u² ≤ u·t²`, so
`u·t² ≤ 2n·t²`, so `u ≤ 2n`.  (iii) Else `2u > t²`: the summed pencil bound
(`pencil_family_card_le` per point) gives `u(t−1) ≤ n(n−1)`, while
`2u(t−1) > t²(t−1) ≥ 2n² > 2n(n−1)` — contradiction.

Consequence (with the partition keystone and convexity, assembly registered): on every
band with `k+m+1 ≳ (2n²)^{1/3}`, the agreement-capped per-word supply is `≤ 2n/t ·
C(cap, t)`-shaped — **`ExplainableCoreSupply` with subexponential `B`, PROVEN on the
deep-band range**.  The shallow range `t ≲ n^{2/3}` remains the open wall.
Issue #389.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {n : ℕ} [NeZero n]

open Classical in
/-- Incidence swap: `Σ_x d_x = Σ_{A ∈ S} |A|`. -/
theorem degree_sum_eq_size_sum (S : Finset (Finset (Fin n))) :
    ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card = ∑ A ∈ S, A.card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  have : A.card = ((Finset.univ : Finset (Fin n)).filter (fun x => x ∈ A)).card := by
    congr 1
    ext x
    simp
  rw [this, Finset.card_filter]

open Classical in
/-- **THE MEAN-DEGREE LAW, DEEP BANDS**: a family of `≥ t`-sized sets pairwise
intersecting in `≤ 1` point with `2n² ≤ t²(t−1)` has total size `≤ 2n`. -/
theorem mean_degree_law_deep {S : Finset (Finset (Fin n))} {t : ℕ} (ht : 2 ≤ t)
    (hsize : ∀ A ∈ S, t ≤ A.card)
    (hpair : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → (A ∩ B).card ≤ 1)
    (hdeep : 2 * n ^ 2 ≤ t ^ 2 * (t - 1)) :
    ∑ A ∈ S, A.card ≤ 2 * n := by
  classical
  set u := ∑ A ∈ S, A.card with hu
  set L := S.card with hL
  -- the bootstrap: L·t ≤ u
  have hLt : L * t ≤ u := by
    calc L * t = ∑ _A ∈ S, t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ A ∈ S, A.card := Finset.sum_le_sum hsize
  -- Bonferroni: u ≤ n + L(L−1) ≤ n + L·L
  have hBon : u ≤ n + L * L := by
    have h := degree_sum_le hpair
    rw [degree_sum_eq_size_sum, ← hu, ← hL] at h
    have hLL : L * (L - 1) ≤ L * L := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  -- the quadratic: u·t² ≤ n·t² + u²
  have hquad : u * t ^ 2 ≤ n * t ^ 2 + u * u := by
    have h1 : u * t ^ 2 ≤ (n + L * L) * t ^ 2 := Nat.mul_le_mul_right _ hBon
    have h2 : (L * L) * t ^ 2 = (L * t) * (L * t) := by ring
    have h3 : (L * t) * (L * t) ≤ u * u := Nat.mul_le_mul hLt hLt
    calc u * t ^ 2 ≤ (n + L * L) * t ^ 2 := h1
    _ = n * t ^ 2 + (L * L) * t ^ 2 := by ring
    _ = n * t ^ 2 + (L * t) * (L * t) := by rw [h2]
    _ ≤ n * t ^ 2 + u * u := Nat.add_le_add_left h3 _
  -- the summed pencil bound: u·(t−1) ≤ n·(n−1)
  have hpencil : u * (t - 1) ≤ n * (n - 1) := by
    have hpt : ∀ x : Fin n, (S.filter (fun A => x ∈ A)).card * (t - 1) ≤ n - 1 := by
      intro x
      refine pencil_family_card_le (x := x) (r := t - 1) ?_ ?_
      · intro A hA
        obtain ⟨hAS, hxA⟩ := Finset.mem_filter.mp hA
        exact ⟨hxA, by have := hsize A hAS; omega⟩
      · intro A hA B hB hne
        obtain ⟨hAS, hxA⟩ := Finset.mem_filter.mp hA
        obtain ⟨hBS, hxB⟩ := Finset.mem_filter.mp hB
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro i hi
          rw [Finset.mem_singleton.mp hi]
          exact Finset.mem_inter.mpr ⟨hxA, hxB⟩
        · rw [Finset.card_singleton]
          exact hpair A hAS B hBS hne
    calc u * (t - 1)
        = (∑ x : Fin n, (S.filter (fun A => x ∈ A)).card) * (t - 1) := by
          rw [hu, ← degree_sum_eq_size_sum]
    _ = ∑ x : Fin n, (S.filter (fun A => x ∈ A)).card * (t - 1) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ _x : Fin n, (n - 1) := Finset.sum_le_sum fun x _ => hpt x
    _ = n * (n - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- two branches
  rcases Nat.lt_or_ge (t ^ 2) (2 * u) with hbig | hsmall
  · -- 2u > t²: contradiction via the pencil sum and the deep hypothesis
    exfalso
    have h1 : t ^ 2 * (t - 1) < 2 * u * (t - 1) := by
      have ht1 : 0 < t - 1 := by omega
      have := Nat.mul_lt_mul_of_lt_of_le hbig (le_refl (t - 1)) (by omega : 0 < t - 1)
      exact this
    have h2 : 2 * u * (t - 1) = 2 * (u * (t - 1)) := by ring
    have h3 : 2 * (u * (t - 1)) ≤ 2 * (n * (n - 1)) := by omega
    have h4 : 2 * (n * (n - 1)) ≤ 2 * n ^ 2 := by
      have hle : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have hnn : n * n = n ^ 2 := by ring
      omega
    omega
  · -- 2u ≤ t²: cancel
    have h2uu : 2 * (u * u) ≤ u * t ^ 2 := by
      calc 2 * (u * u) = (2 * u) * u := by ring
      _ ≤ t ^ 2 * u := Nat.mul_le_mul_right _ hsmall
      _ = u * t ^ 2 := by ring
    have hA : u * t ^ 2 ≤ 2 * (n * t ^ 2) := by omega
    have ht2 : 0 < t ^ 2 := by positivity
    have : u ≤ 2 * n := by
      have h := hA
      rw [show 2 * (n * t ^ 2) = (2 * n) * t ^ 2 from by ring] at h
      exact Nat.le_of_mul_le_mul_right h ht2
    exact this

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.degree_sum_eq_size_sum
#print axioms ProximityGap.PairRank.mean_degree_law_deep
