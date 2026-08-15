/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80YArcEquivalenceConverse
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80W (#466, 2026-07-10): the SAME-ARC PAIR-COUNT identity — the arc-occupancy ℓ²
  discrepancy EQUALS the same-arc pair excess, welding the KM-arc certificate (G78/G80) and
  the decoupling lag-decorrelation mass (G80D) into ONE object (axiom-clean).

## The weld

The doctrine-v2 synthesis found both constant-loss engines fail on the SAME missing input:
KM needs arc-occupancy uniformity of the dilated subgroup; Bourgain–Demeter decoupling needs
lag-decorrelation (`Σ A² − Σ A(b)A(bu) = ½Σ(A(b)−A(bu))²`, the G80D defect identity). This
lane proves the exact combinatorial bridge showing they are two faces of one object:

* `pairCount_eq_sum_sq_occupancy` : `#{(x,y) ∈ S² : same arc} = Σ_j n_j²` — the same-arc
  PAIR COUNT is exactly the second moment of the arc occupancies (biUnion partition of the
  diagonal-fiber product).
* `sum_sq_dev_eq_pairCount_excess` : for the uniform reference `m = #S/K`,
  `Σ_j (n_j − #S/K)² = pairCount − #S²/K` — the ℓ² arc discrepancy IS the same-arc pair
  excess over the uniform count.
* `l1_dev_le_sqrt_card_mul_l2` : Cauchy–Schwarz `Σ_j |n_j − m| ≤ √K·√(Σ_j (n_j − m)²)`.
* `charSum_le_of_pair_excess` (CAPSTONE) : if the same-arc pair count exceeds `#S²/K` by at
  most `Δ`, then `‖∑_{y∈S} e(val(y)/p)‖ ≤ √K·√Δ + #S·(2π/K)`.

At `S = b·μ_n` the same-arc pair count is `#{(x,y) ∈ μ_n² : b(x−y) lands in a length-(p/K)
arc-difference window}` — anti-concentration of the DIFFERENCE set `μ_n − μ_n` under dilation,
exactly the decorrelation shape G80D isolated. So a difference-anti-concentration bound of
strength `Δ` feeds the arc consumer directly: the two engine hypotheses are formally one.

## Loss accounting (honest)

The ℓ²→ℓ¹ step costs `√K`: pair excess `Δ` gives `M ≤ √(KΔ) + 2πn/K`, optimal
`K ≈ (2πn)^{2/3}/Δ^{1/3}` giving `M ≲ (2πn·√Δ)^{1/3}·…` — to reach the prize
`M = O(√(n log q))` one needs `Δ = O(n·log q·√(log q/n)·K)`-scale, i.e. pair excess within a
CONSTANT factor of the uniform count on the balanced window. The sup-form certificate (G80X,
`ε ≍ log q` per arc) and the pair-form certificate (`Δ` here) are both exactly-pinned faces of
the one missing non-Fourier input. No claim of producing either. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity

open ArkLib.ProximityGap.Frontier.G80ZArcArithmeticInstantiation
open ArkLib.ProximityGap.Frontier.G80YArcEquivalenceConverse

/-- **Same-arc pair count = second moment of occupancies**: partitioning the same-arc pairs
by their common arc index. -/
theorem pairCount_eq_sum_sq_occupancy {α : Type*} [DecidableEq α]
    (S : Finset α) {K : ℕ} (κ : α → ℕ) (hκ : ∀ x ∈ S, κ x ∈ Finset.range K) :
    ((S ×ˢ S).filter (fun q => κ q.1 = κ q.2)).card
      = ∑ j ∈ Finset.range K, ((S.filter (fun x => κ x = j)).card) ^ 2 := by
  have hpart : (S ×ˢ S).filter (fun q => κ q.1 = κ q.2)
      = (Finset.range K).biUnion
          (fun j => (S.filter (fun x => κ x = j)) ×ˢ (S.filter (fun x => κ x = j))) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_biUnion]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      exact ⟨κ x, hκ x hx, ⟨⟨hx, rfl⟩, ⟨hy, hxy.symm⟩⟩⟩
    · rintro ⟨j, _, ⟨⟨hx, hjx⟩, ⟨hy, hjy⟩⟩⟩
      exact ⟨⟨hx, hy⟩, by rw [hjx, hjy]⟩
  rw [hpart, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_product, sq]
  · intro j _ j' _ hjj'
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x, y⟩ hmem hmem'
    simp only [mem_product, mem_filter] at hmem hmem'
    exact hjj' (hmem.1.2.symm.trans hmem'.1.2)

/-- **The ℓ² arc discrepancy is the same-arc pair excess**: at the uniform reference mass
`m = #S/K`, `Σ_j (n_j − #S/K)² = pairCount − #S²/K`. -/
theorem sum_sq_dev_eq_pairCount_excess {α : Type*} [DecidableEq α]
    (S : Finset α) {K : ℕ} (hK : 0 < K) (κ : α → ℕ)
    (hκ : ∀ x ∈ S, κ x ∈ Finset.range K) :
    ∑ j ∈ Finset.range K,
        (((S.filter (fun x => κ x = j)).card : ℝ) - (S.card : ℝ) / K) ^ 2
      = (((S ×ˢ S).filter (fun q => κ q.1 = κ q.2)).card : ℝ)
        - (S.card : ℝ) ^ 2 / K := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsum : ∑ j ∈ Finset.range K, ((S.filter (fun x => κ x = j)).card : ℝ)
      = (S.card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hκ).symm
  have hsq : ∑ j ∈ Finset.range K, (((S.filter (fun x => κ x = j)).card : ℝ)) ^ 2
      = (((S ×ˢ S).filter (fun q => κ q.1 = κ q.2)).card : ℝ) := by
    rw [pairCount_eq_sum_sq_occupancy S κ hκ]
    push_cast
    rfl
  have hexpand : ∀ j ∈ Finset.range K,
      (((S.filter (fun x => κ x = j)).card : ℝ) - (S.card : ℝ) / K) ^ 2
        = (((S.filter (fun x => κ x = j)).card : ℝ)) ^ 2
          - 2 * ((S.card : ℝ) / K) * ((S.filter (fun x => κ x = j)).card : ℝ)
          + ((S.card : ℝ) / K) ^ 2 := by
    intro j _
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- **Cauchy–Schwarz for the deviation vector**: `Σ_j |n_j − m| ≤ √K · √(Σ_j (n_j − m)²)`. -/
theorem l1_dev_le_sqrt_card_mul_l2 {K : ℕ} (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range K, |f j| ≤
      Real.sqrt K * Real.sqrt (∑ j ∈ Finset.range K, (f j) ^ 2) := by
  have hcs : (∑ j ∈ Finset.range K, |f j|) ^ 2 ≤
      (Finset.range K).card * ∑ j ∈ Finset.range K, |f j| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have habs : ∑ j ∈ Finset.range K, |f j| ^ 2 = ∑ j ∈ Finset.range K, (f j) ^ 2 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sq_abs (f j)
  rw [habs, Finset.card_range] at hcs
  have hnonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, |f j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hrhs : Real.sqrt K * Real.sqrt (∑ j ∈ Finset.range K, (f j) ^ 2)
      = Real.sqrt ((K : ℝ) * ∑ j ∈ Finset.range K, (f j) ^ 2) := by
    rw [Real.sqrt_mul (by positivity)]
  rw [hrhs]
  calc ∑ j ∈ Finset.range K, |f j|
      = Real.sqrt ((∑ j ∈ Finset.range K, |f j|) ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ ≤ Real.sqrt ((K : ℝ) * ∑ j ∈ Finset.range K, (f j) ^ 2) := Real.sqrt_le_sqrt hcs

/-- **CAPSTONE — pair-excess ⟹ character-sum bound.** If the same-arc pair count exceeds the
uniform count `#S²/K` by at most `Δ`, then
`‖∑_{y∈S} e(val(y)/p)‖ ≤ √K·√Δ + #S·(2π/K)`. The G80D difference-decorrelation object feeds
the arc consumer directly. -/
theorem charSum_le_of_pair_excess {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    {K : ℕ} (hK : 2 ≤ K) (Δ : ℝ)
    (hpair : (((S ×ˢ S).filter
        (fun q => arcIndex K q.1 = arcIndex K q.2)).card : ℝ)
      ≤ (S.card : ℝ) ^ 2 / K + Δ) :
    ‖∑ y ∈ S, Complex.exp ((charPhase y : ℂ) * Complex.I)‖ ≤
      Real.sqrt K * Real.sqrt Δ + (S.card : ℝ) * (2 * Real.pi / K) := by
  have hK0 : 0 < K := by omega
  set m : ℝ := (S.card : ℝ) / K with hm
  -- ℓ² discrepancy = pair excess ≤ Δ
  have hl2 : ∑ j ∈ Finset.range K,
      (((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m) ^ 2 ≤ Δ := by
    rw [hm, sum_sq_dev_eq_pairCount_excess S hK0 (arcIndex K)
      (fun y _ => arcIndex_mem_range K hK0 y)]
    linarith
  have hΔ0 : (0 : ℝ) ≤ Δ := le_trans (Finset.sum_nonneg fun j _ => sq_nonneg _) hl2
  -- ℓ¹ ≤ √K·√Δ
  have hl1 : ∑ j ∈ Finset.range K,
      |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m| ≤
        Real.sqrt K * Real.sqrt Δ := by
    calc ∑ j ∈ Finset.range K,
        |((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m|
        ≤ Real.sqrt K * Real.sqrt (∑ j ∈ Finset.range K,
            (((S.filter (fun y => arcIndex K y = j)).card : ℝ) - m) ^ 2) :=
          l1_dev_le_sqrt_card_mul_l2 _
      _ ≤ Real.sqrt K * Real.sqrt Δ := by
          gcongr
  -- G80Y converse with the ℓ¹ bound
  have h := charSum_le_of_arc_l1_discrepancy S hK (arcIndex K)
    (fun y _ => arcIndex_mem_range K hK0 y) charPhase (2 * Real.pi / K) m
    (fun y _ => arcIndex_width K hK0 y)
  linarith

end ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity.pairCount_eq_sum_sq_occupancy
#print axioms
  ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity.sum_sq_dev_eq_pairCount_excess
#print axioms
  ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity.l1_dev_le_sqrt_card_mul_l2
#print axioms
  ArkLib.ProximityGap.Frontier.G80WArcPairCountIdentity.charSum_le_of_pair_excess
