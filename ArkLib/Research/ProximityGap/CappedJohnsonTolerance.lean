/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointJohnsonTolerance
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence

/-! # An exact tolerance test at the largest admissible field order

A small alphabet might identify distinct two-site MCA circuits. If this allows a
constant code to attain Johnson on a smaller budget, the list requirement still
forces the tolerance to cover all the circuits on a sufficiently large prime.
This yields both necessity and sufficiency at the largest admissible field order.
-/

namespace ProximityPrize.CappedJohnsonTolerance

open FullPrizeReview ProximityGap JointJohnsonTolerance
open scoped NNReal ENNReal

/-- The two-site circuit budget and the at-least-one-agreement list budget. -/
def required (n : ℕ) : ℕ := max n (n.choose 2)

/-- Existence of a field and supplied domain below the published ceiling
whose two operational cutoffs equal the finite Johnson radius. -/
def realizable (n k : ℕ) (ε : ℝ≥0) : Prop :=
  ∃ (F I : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : Fintype I)
    (_ : Nonempty I) (D : I ↪ F), Nonempty (ReedSolomon.Smooth D) ∧
      Fintype.card I = n ∧ Fintype.card F < 2 ^ 256 ∧ both D ε k

/-- Multiplying the tolerance by a large benchmark field covers both integer budgets
whenever a supplied smaller field exhibits joint equality. -/
theorem lower_budget {I F : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0)
    (rate : hasPrizeRate (Fintype.card I) 1) (joint : both D ε 1)
    {p : ℕ} (largest : Fintype.card F ≤ p)
    (large : (Fintype.card I).choose 2 * ((Fintype.card I).choose 2).choose 2 ≤ p) :
    required (Fintype.card I) ≤ ⌊ε * (p : ℝ≥0)⌋₊ := by
  classical
  let n := Fintype.card I
  let q := Fintype.card F
  let N := n.choose 2
  let B := RankReview.budget F ε
  have hlen : 1 < Fintype.card I := by rcases rate with h | h | h | h <;> omega
  obtain ⟨_, mc, hlist⟩ := (supplied_iff D ε rate).mp joint
  have b_le : B ≤ ⌊ε * (p : ℝ≥0)⌋₊ := Nat.floor_mono
    (mul_le_mul_of_nonneg_left (by exact_mod_cast largest) (by positivity))
  apply max_le (hlist.trans b_le)
  by_cases covered : N ≤ B
  · exact covered.trans b_le
  have missed : q < (B + 1).choose 2 := by
    by_contra! h
    let _ : SampleableType F := SampleableType.ofFintype _
    have spec := RankReview.mcaAnswer_correct D ε 1 1 le_rfl
    rw [mc] at spec
    have safe := spec.mpr trivial
    change CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F)
      (ReedSolomon.code D 1) ((1 : ℝ≥0) : ℝ) ≤ (ε : ℝ≥0∞) at safe
    rw [← epsMCA_eq_mcaError] at safe
    exact covered ((ToleranceCircuitCriterion.endpoint_iff D (by decide) hlen ε h).mp safe)
  have qsmall := missed.le.trans (Nat.choose_le_choose 2 (show B + 1 ≤ N by omega))
  have Nq : N * q ≤ p := (Nat.mul_le_mul_left N qsmall).trans large
  have budget_pos : 1 ≤ ε * (q : ℝ≥0) := by
    have h : 1 ≤ RankReview.budget F ε := le_trans (by omega) hlist
    exact_mod_cast ((Nat.le_floor_iff (by positivity : 0 ≤ ε * (q : ℝ≥0))).mp h)
  have qp : (0 : ℝ≥0) < q := by exact_mod_cast Fintype.card_pos (α := F)
  apply Nat.le_floor
  calc
    (N : ℝ≥0) ≤ (p : ℝ≥0) / q := (le_div_iff₀ qp).mpr (by exact_mod_cast Nq)
    _ ≤ ε * p := (div_le_iff₀ qp).mpr (by
      calc
        (p : ℝ≥0) = 1 * p := (one_mul _).symm
        _ ≤ (ε * q) * p := mul_le_mul_of_nonneg_right budget_pos (by positivity)
        _ = (ε * p) * q := by ring)

/-- Once the largest admissible order is supplied by a prime, admissibility of
simultaneous equality at dimension one is exactly one numerical inequality. -/
theorem at_maximal_prime {n p : ℕ} [Fact p.Prime] (hr : hasPrizeRate n 1)
    (dyad : ∃ t : ℕ, n = 2 ^ t) (divides : n ∣ p - 1) (field : p < 2 ^ 256)
    (maximal : ∀ q : ℕ, IsPrimePow q → n ∣ q - 1 → q < 2 ^ 256 → q ≤ p)
    (large : n.choose 2 * (n.choose 2).choose 2 ≤ p) (ε : ℝ≥0) :
    realizable n 1 ε ↔ required n ≤ ⌊ε * (p : ℝ≥0)⌋₊ := by
  constructor
  · rintro ⟨F, I, _, _, _, _, _, D, ⟨sm⟩, size, cap, equal⟩
    subst n
    classical
    let _ : Fintype (ReedSolomon.Smooth.H D) := Fintype.ofFinite _
    obtain ⟨z, _⟩ := SmoothDomainMcaEquivalence.coset_equiv D
    have dvd := Subgroup.card_subgroup_dvd_card (ReedSolomon.Smooth.H D)
    simp only [Nat.card_eq_fintype_card, ← Fintype.card_congr z, Fintype.card_units] at dvd
    exact lower_budget D ε hr equal (maximal _ (FiniteField.isPrimePow_card F) dvd cap) large
  · intro budget
    have hn : 0 < n := by rcases hr with h | h | h | h <;> omega
    let _ : NeZero n := ⟨hn.ne'⟩
    obtain ⟨D, ⟨sm⟩⟩ := SmoothPowerMcaDescent.exists_prime_domain (p := p) divides dyad
    refine ⟨ZMod p, Fin n, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, D, ⟨sm⟩, Fintype.card_fin n, by simpa only [ZMod.card] using field, ?_⟩
    have bound : required n ≤ RankReview.budget (ZMod p) ε := by
      simpa only [RankReview.budget, ZMod.card] using budget
    apply (supplied_iff D ε (by simpa only [Fintype.card_fin] using hr)).mpr
    refine ⟨rfl, ConstantJohnsonTolerance.mca_all_safe D ε ?_, ?_⟩
    · simpa only [Fintype.card_fin] using (le_max_right n (n.choose 2)).trans bound
    · simpa only [Fintype.card_fin] using (le_max_left n (n.choose 2)).trans bound

end ProximityPrize.CappedJohnsonTolerance
