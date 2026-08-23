/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeExact

/-!
# The tight MCA upper bound for the zero code: `ε_mca(⊥, δ) ≤ (⌊δ·n⌋ + 1)/|F|`

This completes the exact characterization of the zero code's MCA error. `MCAZeroCodeExact` /
`MCAZeroCodeExactRange` pin `ε_mca(⊥, δ) = 1/|F|` for `δ·n < 1`. Here we prove the **tight upper
bound for every radius** `δ ≤ 1`:

  `ε_mca(⊥, δ) ≤ (⌊δ·n⌋ + 1)/|F|`,   `n = |ι|`.

Together with the matching constructions this gives `ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` (capped at `1`).

## The slope-counting argument (`badScalar_card_le_floor_succ`)

Fix a stack `u`. For a bad scalar `γ`, the line `ℓ_γ(i) = u₀ᵢ + γ·u₁ᵢ` vanishes on a witness set
`S_γ` with `|S_γ| ≥ (1-δ)n`, so its support `{i : ℓ_γ(i) ≠ 0}` has `≤ ⌊δn⌋` elements
(`line_support_card_le`). Let `P = {i : u₁ᵢ ≠ 0}` and, for each bad `γ`,
`D_γ = {i ∈ P : ℓ_γ(i) = 0}`. Then:

* `D_γ` is **nonempty** — `mcaEvent`'s non-degeneracy gives a coordinate in `S_γ` with
  `(u₀ᵢ,u₁ᵢ) ≠ 0`, and there `u₁ᵢ ≠ 0` (else `u₀ᵢ = ℓ_γ(i) = 0`).
* `|P| ≤ |D_γ| + ⌊δn⌋` — the `P`-coordinates off `D_γ` lie in the `≤⌊δn⌋`-size support.
* The `D_γ` are **pairwise disjoint** — a coordinate `i ∈ P` with `ℓ_γ(i)=0` pins
  `γ = -u₀ᵢ/u₁ᵢ`, so it belongs to at most one `D_γ`.

Disjoint nonempty subsets of `P` give `|B| ≤ ∑_γ |D_γ| = |⋃ D_γ| ≤ |P|`, and with the per-set
lower bound, `|B|·(|P| - ⌊δn⌋) ≤ |P|`, whence `|B| ≤ ⌊δn⌋ + 1`. Averaging over `γ` then bounds
`ε_mca` by `(⌊δn⌋+1)/|F|`.

## References
- Completes `ProximityGap.MCAZeroCode.epsMCA_bot_eq_inv_card` to all radii.
- Issue #140 / #171.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

section UpperBound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- The line `ℓ_γ` of a firing stack has support `≤ ⌊δ·n⌋` (it vanishes on the `≥(1-δ)n` witness
set). -/
theorem line_support_card_le {δ : ℝ≥0} (hδ1 : δ ≤ 1) {u : WordStack F (Fin 2) ι} {γ : F}
    (hev : mcaEvent (F := F) (Cbot : Set (ι → F)) δ (u 0) (u 1) γ) :
    (Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i ≠ 0)).card
      ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ := by
  obtain ⟨S, hS, ⟨w, hwmem, hweq⟩, _hno⟩ := hev
  have hw0 : w = 0 := (mem_Cbot_iff w).mp hwmem
  -- `S ⊆ {ℓ_γ = 0}`.
  have hSsub : S ⊆ Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i = 0) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hi2 := hweq i hi
    rw [hw0] at hi2
    simpa using hi2.symm
  -- `|supp| + |S| ≤ n`.
  have hsum_le : (Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i ≠ 0)).card + S.card
      ≤ Fintype.card ι := by
    have hzle : S.card ≤ (Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i = 0)).card :=
      Finset.card_le_card hSsub
    have hpart : (Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i ≠ 0)).card
        + (Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i = 0)).card = Fintype.card ι := by
      have := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset ι)) (p := fun i => (u 0) i + γ • (u 1) i ≠ 0)
      simpa [Finset.card_univ, not_not] using this
    omega
  -- Pass to `ℝ` and use `|S| ≥ (1-δ)n`.
  apply Nat.le_floor
  have hSr : (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have hc := (NNReal.coe_le_coe).mpr hS
    rw [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one] at hc
    push_cast at hc ⊢
    linarith [hc]
  have hsum_r : ((Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i ≠ 0)).card : ℝ)
      + (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hsum_le
  nlinarith [hSr, hsum_r]

open Classical in
/-- **At most `⌊δ·n⌋ + 1` bad scalars per stack** (every radius `δ ≤ 1`). -/
theorem badScalar_card_le_floor_succ {δ : ℝ≥0} (hδ1 : δ ≤ 1) (u : WordStack F (Fin 2) ι) :
    (Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 := by
  set m : ℕ := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ with hm
  set B : Finset F :=
    Finset.filter (fun γ : F => mcaEvent (F := F) (Cbot : Set (ι → F)) δ (u 0) (u 1) γ) Finset.univ
    with hB
  set P : Finset ι := Finset.univ.filter (fun i => (u 1) i ≠ 0) with hP
  -- For each bad `γ`, the `P`-zeros of `ℓ_γ`.
  let D : F → Finset ι := fun γ => Finset.univ.filter (fun i => (u 1) i ≠ 0 ∧ (u 0) i + γ • (u 1) i = 0)
  have hDsubP : ∀ γ, D γ ⊆ P := by
    intro γ i hi
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.1
  -- Disjointness: a `P`-zero of `ℓ_γ` pins `γ`.
  have hdisj : ∀ γ ∈ B, ∀ γ' ∈ B, γ ≠ γ' → Disjoint (D γ) (D γ') := by
    intro γ _ γ' _ hne
    rw [Finset.disjoint_left]
    intro i hiγ hiγ'
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hiγ hiγ'
    apply hne
    -- `u₀ᵢ + γ u₁ᵢ = 0 = u₀ᵢ + γ' u₁ᵢ` and `u₁ᵢ ≠ 0` ⟹ `γ = γ'`.
    have h1 : (u 0) i + γ • (u 1) i = (u 0) i + γ' • (u 1) i := by rw [hiγ.2, hiγ'.2]
    have h2 : γ • (u 1) i = γ' • (u 1) i := add_left_cancel h1
    rw [smul_eq_mul, smul_eq_mul] at h2
    exact mul_right_cancel₀ hiγ.1 h2
  -- Each `D γ` (for bad `γ`) is nonempty and covers `|P| - m` of `P`.
  have hPle : ∀ γ ∈ B, P.card ≤ (D γ).card + m := by
    intro γ hγ
    rw [hB, Finset.mem_filter] at hγ
    have hsupp := line_support_card_le (F := F) hδ1 hγ.2
    -- `|P| = |P \ D γ| + |D γ|`, and `P \ D γ ⊆ supp ℓ_γ` has `≤ m` elements.
    have hsplit : (P \ D γ).card + (D γ).card = P.card :=
      Finset.card_sdiff_add_card_eq_card (hDsubP γ)
    have hsub : P \ D γ ⊆ Finset.univ.filter (fun i => (u 0) i + γ • (u 1) i ≠ 0) := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      obtain ⟨hiP, hiD⟩ := hi
      have hu1 : (u 1) i ≠ 0 := by
        simpa [P, Finset.mem_filter] using hiP
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hℓ0
      exact hiD (by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hu1, hℓ0⟩)
    have hle : (P \ D γ).card ≤ m := le_trans (Finset.card_le_card hsub) hsupp
    omega
  -- Each `D γ` (for bad `γ`) is nonempty: `mcaEvent`'s non-degeneracy gives a `P`-zero of `ℓ_γ`.
  have hDne : ∀ γ ∈ B, (D γ).Nonempty := by
    intro γ hγ
    rw [hB, Finset.mem_filter] at hγ
    obtain ⟨S, _hS, ⟨w, hwmem, hweq⟩, hno⟩ := hγ.2
    have hw0 : w = 0 := (mem_Cbot_iff w).mp hwmem
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hno
    refine ⟨0, zero_mem_Cbot, 0, zero_mem_Cbot, fun i hi => ?_⟩
    have hℓ : (u 0) i + γ • (u 1) i = 0 := by
      have hi2 := hweq i hi; rw [hw0] at hi2; simpa using hi2.symm
    have hu1z : (u 1) i = 0 := by
      by_contra hu1
      have hmem : i ∈ D γ := by
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hu1, hℓ⟩
      rw [hempty] at hmem; exact absurd hmem (Finset.notMem_empty i)
    have hu0z : (u 0) i = 0 := by rw [hu1z, smul_zero, add_zero] at hℓ; exact hℓ
    exact ⟨by simp only [Pi.zero_apply]; exact hu0z.symm,
           by simp only [Pi.zero_apply]; exact hu1z.symm⟩
  -- The disjoint `D γ` sit inside `P`, so `∑ |D γ| ≤ |P|`.
  have hbu_card : (B.biUnion D).card = ∑ γ ∈ B, (D γ).card := Finset.card_biUnion hdisj
  have hbu_le : (B.biUnion D).card ≤ P.card := by
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hiγ⟩ := hi
    exact hDsubP γ hiγ
  have hsum_le : ∑ γ ∈ B, (D γ).card ≤ P.card := hbu_card ▸ hbu_le
  -- `|B| ≤ ∑ |D γ| ≤ |P|` (each `|D γ| ≥ 1`).
  have hBP : B.card ≤ P.card := by
    have hpos : ∀ γ ∈ B, 1 ≤ (D γ).card := fun γ hγ => (hDne γ hγ).card_pos
    have hconst : ∑ _γ ∈ B, (1 : ℕ) ≤ ∑ γ ∈ B, (D γ).card := Finset.sum_le_sum hpos
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hconst
    exact le_trans hconst hsum_le
  -- `|B| · (|P| - m) ≤ ∑ |D γ| ≤ |P|`.
  have hge : ∀ γ ∈ B, P.card - m ≤ (D γ).card := fun γ hγ => by
    have := hPle γ hγ; omega
  have hsum_ge : B.card * (P.card - m) ≤ ∑ γ ∈ B, (D γ).card := by
    have hconst : ∑ _γ ∈ B, (P.card - m) ≤ ∑ γ ∈ B, (D γ).card := Finset.sum_le_sum hge
    rwa [Finset.sum_const, smul_eq_mul] at hconst
  have hkey : B.card * (P.card - m) ≤ P.card := le_trans hsum_ge hsum_le
  -- Nat arithmetic: from `|B|·(|P|-m) ≤ |P|`, `|B| ≤ |P|`, conclude `|B| ≤ m+1`.
  rcases Nat.eq_zero_or_pos B.card with hb0 | hbpos
  · omega
  · by_cases hpm : P.card ≤ m
    · omega
    · have hq1 : 0 < P.card - m := by omega
      have hkey2 : (B.card - 1) * (P.card - m) ≤ m := by
        rw [Nat.sub_one_mul]; omega
      have hle2 : B.card - 1 ≤ (B.card - 1) * (P.card - m) :=
        Nat.le_mul_of_pos_right _ hq1
      omega

open Classical in
/-- **Tight MCA upper bound for the zero code:** `ε_mca(⊥, δ) ≤ (⌊δ·n⌋ + 1)/|F|` for every
finite field `F`, nonempty `ι` (`n = |ι|`), and radius `δ ≤ 1`. With the matching lower bounds
(`MCAZeroCodeExact*`) this characterizes `ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` (capped at `1`). -/
theorem epsMCA_bot_le_floor_succ_div {δ : ℝ≥0} (hδ1 : δ ≤ 1) :
    epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ
      ≤ ((⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_floor_succ hδ1 u

#print axioms line_support_card_le
#print axioms badScalar_card_le_floor_succ
#print axioms epsMCA_bot_le_floor_succ_div

end UpperBound

end ProximityGap.MCAZeroCode
