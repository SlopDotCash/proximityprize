/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.CapacityBoundaryReview
import ArkLib.Research.ProximityGap.Frontier.BoundaryPairSeparation

/-! # The literal MCA maximum and the capacity comparison at a supplied tolerance

Let `B = floor(εq)` and `N = choose n (k+1)`. If the field permits separation
of `B+1` supports, radius one is safe precisely when `N ≤ B`. This includes
every budget with `B² < q`. Without any separation hypothesis, endpoint safety
still imposes the second-moment inequality `Nq ≤ B(q+N-1)`.
-/

namespace ProximityPrize.ToleranceCircuitCriterion

open Code ProximityGap FullPrizeReview Polynomial
open ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]

/-- Endpoint safety at arbitrary tolerance forces the second-moment bound.
It also bounds the size of every family of minimal supports whose pairs can be
separated over the field. Both inequalities apply without a field-size condition. -/
theorem necessary (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (ε : ℝ≥0) (good : epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) 1 ≤ ε) :
    let N := (Fintype.card I).choose (k + 1)
    let q := Fintype.card F
    let B := RankReview.budget F ε
    N * q ≤ B * (q + N - 1) ∧ ∀ m ≤ N, m.choose 2 ≤ q → m ≤ B := by
  classical
  let n := Fintype.card I
  let e := (Fintype.equivFin I).symm
  let x := e.toEmbedding.trans D
  let r : ℝ≥0 := 1 - ((k + 1 : ℕ) : ℝ≥0) / n
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hrat : ((k + 1 : ℕ) : ℝ≥0) / n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hkn)
  have hr : (1 - r) * (Fintype.card (Fin n) : ℝ≥0) = ((k + 1 : ℕ) : ℝ≥0) := by
    rw [Fintype.card_fin, tsub_tsub_cancel_of_le hrat, div_mul_cancel₀ _ hn.ne']
  have hlo : (k : ℝ≥0) < (1 - r) * (Fintype.card (Fin n) : ℝ≥0) := by
    rw [hr]
    exact_mod_cast Nat.lt_succ_self k
  rw [MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e x D (fun _ => rfl)] at good
  have shell : epsMCA (F := F) (SpikeFloor.rsCode x k : Set (Fin n → F)) r ≤ ε := by
    rw [BoundarySecurityBudget.rsCode_eq_code]
    exact (epsMCA_mono _ (tsub_le_self : r ≤ 1)).trans good
  have bound (Q : F[X]) :
      (Finset.univ.filter (fun c : F => mcaEvent (F := F) (SpikeFloor.rsCode x k : Set (Fin n → F))
        r (fun i => Q.eval (x i)) (fun i => x i ^ k) c)).card ≤ RankReview.budget F ε := by
    let u := finMapTwoWords (fun i => Q.eval (x i)) (fun i => x i ^ k)
    have h := OpenCoreConverse.incidence_le_of_epsMCA_le
      (F := F) (SpikeFloor.rsCode x k : Set (Fin n → F)) (ε : ℝ≥0∞) shell u
    rw [mul_comm] at h
    apply Nat.le_floor
    exact_mod_cast h
  constructor
  · obtain ⟨Q, hQ⟩ := Ownership.boundary_production_failure x hk hlo hr.le
    exact hQ.trans (Nat.mul_le_mul_right _ (bound Q))
  · intro m hm hq
    obtain ⟨Q, hQ⟩ := BoundaryPairSeparation.partial_mass x hk hlo hr.le hm hq
    exact (by simpa only [Polynomial.eval_pow, Polynomial.eval_X] using hQ :
      m ≤ (Finset.univ.filter (fun c : F => mcaEvent (F := F)
        (SpikeFloor.rsCode x k : Set (Fin n → F)) r (fun i => Q.eval (x i))
        (fun i => x i ^ k) c)).card).trans (bound Q)

/-- The square-budget window is contained in the pair-separation window. -/
theorem pair_bound_of_square {B q : ℕ} (h : B ^ 2 < q) : (B + 1).choose 2 ≤ q := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  apply Nat.le_of_lt
  rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) B]

/-- Radius-one MCA safety at the supplied tolerance is exactly the circuit test
when the field separates one more support than the allowed number of labels. -/
theorem endpoint_iff (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (ε : ℝ≥0) (hsep : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) 1 ≤ ε ↔
      (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε := by
  classical
  constructor
  · intro good
    by_contra! hlarge
    have := (necessary D hk hkn ε good).2 _ hlarge hsep
    omega
  · intro covered
    rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
    exact (epsMCA_one_le_choose_div D k).trans
      (ENNReal.div_le_div_right (by exact_mod_cast covered) _)

/-- At the sponsor's capacity radius, the relative minimum distance `(n-k+1)/n`,
the same numerical test decides MCA safety on every injective domain. -/
theorem capacity_iff (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (ε : ℝ≥0) (hsep : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F))
        (((Fintype.card I - k + 1 : ℕ) : ℝ≥0) / Fintype.card I) ≤ ε ↔
      (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε := by
  classical
  have hn : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [epsMCA_eq_epsMCA_one_of_le_succ D k, endpoint_iff D hk hkn ε hsep]
  rw [tsub_mul, one_mul, div_mul_cancel₀ _ hn, tsub_le_iff_right]
  exact_mod_cast (show Fintype.card I ≤ k + 1 + (Fintype.card I - k + 1) by omega)

/-- The literal maximum exists exactly in the circuit-covering regime; its value is one. -/
theorem attained_iff (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hkn : k < Fintype.card I)
    (ε δ : ℝ≥0) (hsep : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F) :
    IsGreatest (MCAThresholdLedger.mcaGoodRadii (F := F)
      (ReedSolomon.code D k : Set (I → F)) ε) δ ↔
      δ = 1 ∧ (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε := by
  classical
  constructor
  · intro hs
    obtain rfl := ProximityGap.Frontier.MCAGoodRadiusMaximum.greatest_good_radius_eq_one _ _ _ hs
    exact ⟨rfl, (endpoint_iff D hk hkn ε hsep).mp hs.1.2⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨le_rfl, (endpoint_iff D hk hkn ε hsep).mpr h⟩, fun _ hi => hi.1⟩

/-- The binomial comparison decides whether all MCA radii are safe or a first failure
occurs at least two errors below the sponsor's capacity radius. -/
theorem capacity_dichotomy [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] {k : ℕ}
    (hk : 0 < k) (hr : hasPrizeRate (Fintype.card I) k) (ε : ℝ≥0)
    (hsep : (RankReview.budget F ε + 1).choose 2 ≤ Fintype.card F) :
    if (Fintype.card I).choose (k + 1) ≤ RankReview.budget F ε then
      RankReview.mcaAnswer D ε k = none
    else ∃ e, RankReview.mcaAnswer D ε k = some e ∧ e.val ≤ Fintype.card I - (k + 1) := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k < Fintype.card I := by rcases hr with h | h | h | h <;> omega
  have correct := (RankReview.correctForEveryDomain D ε k hr).1
  have atOne := endpoint_iff D hk hkn ε hsep
  split_ifs with h
  · apply correctBoundary_unique Fintype.card_pos correct
    intro δ hδ
    simp only [iff_true]
    rw [← epsMCA_eq_mcaError]
    exact (epsMCA_mono _ hδ).trans (atOne.mpr h)
  · cases he : RankReview.mcaAnswer D ε k with
    | none =>
      have step := correct 1 le_rfl
      rw [he] at step
      apply False.elim (h (atOne.mp ?_))
      rw [epsMCA_eq_mcaError]
      exact step.mpr trivial
    | some e => exact ⟨e, rfl, CapacityBoundaryReview.mca_ceiling D ε hr he⟩

end ProximityPrize.ToleranceCircuitCriterion
