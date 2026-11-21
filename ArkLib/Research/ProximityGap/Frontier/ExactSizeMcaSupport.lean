/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportRank
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-! # Fixed-size witnesses for the affine-line MCA rank test

It suffices to enumerate one layer of the support lattice for each scalar. An individually
unexplainable row has an inconsistent interpolation circuit of size `k + 1`. Keep this circuit
and enough other positions to meet the requested agreement count. -/

namespace ProximityGap.ExactSizeMcaSupport

open Code Finset ProjectiveQuotientSupport SimultaneousSupportRank
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

omit [Fintype I] [Nonempty I] [Fintype F] in
private theorem circuit (D : I ↪ F) (k : ℕ) (u : I → F) (S : Finset I)
    (h : ¬ ∃ c ∈ ReedSolomon.code D k, ∀ i ∈ S, c i = u i) :
    ∃ U ⊆ S, U.card = k + 1 ∧ ¬ ∃ c ∈ ReedSolomon.code D k, ∀ i ∈ U, c i = u i := by
  classical
  have hk : k < S.card := by
    by_contra! hsmall
    let p := Lagrange.interpolate S D u
    have hp : p.degree < k :=
      (Lagrange.degree_interpolate_lt u D.injective.injOn).trans_le (by exact_mod_cast hsmall)
    exact h ⟨fun i => p.eval (D i),
      ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p hp (fun _ => rfl),
      fun _ hi => Lagrange.eval_interpolate_at_node u D.injective.injOn hi⟩
  have hcount := CircuitDensity.detecting_density (ReedSolomon.code D k) u S k
    (fun _ hc _ hd _ hcard hag => ReedSolomon.eq_of_agree_of_card_le hc hd hcard hag)
    (card_pos.mp (by omega)) h
  obtain ⟨U, hU⟩ := card_pos.mp ((Nat.choose_pos (show k ≤ S.card - 1 by omega)).trans_le hcount)
  obtain ⟨hm, hn⟩ := mem_filter.mp hU
  exact ⟨U, (mem_powersetCard.mp hm).1, (mem_powersetCard.mp hm).2, hn⟩

omit [Nonempty I] [Fintype F] in
/-- At every radius a bad scalar admits a support of exactly the larger of the required
agreement count and the smallest inconsistent Reed–Solomon circuit size. -/
theorem event_iff (D : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u v : I → F) (g : F) :
    mcaEvent (ReedSolomon.code D k : Set (I → F)) δ u v g ↔
      ∃ S : Finset I, S.card = max (Fintype.card I - ⌊δ * Fintype.card I⌋₊) (k + 1) ∧
        (∃ w ∈ ReedSolomon.code D k, ∀ i ∈ S, w i = u i + g • v i) ∧
        ¬ pairJointAgreesOn (ReedSolomon.code D k : Set (I → F)) S u v := by
  classical
  constructor
  · rintro ⟨S, hs, ⟨w, hw, hfold⟩, hj⟩
    have hn : ¬ ∃ c ∈ ReedSolomon.code D k, ∀ i ∈ S, c i = v i := by
      rintro ⟨c, hc, hfit⟩
      apply hj
      refine ⟨w - g • c, (ReedSolomon.code D k).sub_mem hw ((ReedSolomon.code D k).smul_mem g hc),
        c, hc, fun i hi => ⟨?_, hfit i hi⟩⟩
      change w i - g * c i = u i
      rw [hfold i hi, hfit i hi]
      simp
    obtain ⟨U, hUS, hU, hbad⟩ := circuit D k v S hn
    have ht := (relDist_floor_bound_iff_complement_bound _ _ δ).mpr hs
    obtain ⟨T, hUT, hTS, hT⟩ := exists_subsuperset_card_eq hUS
      (hU ▸ le_max_right (Fintype.card I - ⌊δ * Fintype.card I⌋₊) (k + 1))
      (max_le ht (hU ▸ card_le_card hUS))
    refine ⟨T, by simpa only [hU] using hT, ⟨w, hw, fun i hi => hfold i (hTS hi)⟩, ?_⟩
    rintro ⟨_, _, c, hc, hfit⟩
    exact hbad ⟨c, hc, fun i hi => (hfit i (hUT hi)).2⟩
  · rintro ⟨S, hs, hw, hj⟩
    refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ δ).mp ?_, hw, hj⟩
    rw [hs]
    exact le_max_left _ _

omit [Nonempty I] [Fintype F] in
/-- The bad-scalar event is constant throughout the last `k + 2` agreement levels,
including level zero. This holds separately for each received pair and scalar. -/
theorem event_saturated (D : I ↪ F) (k : ℕ) (δ δ' : ℝ≥0) (u v : I → F) (g : F)
    (h : Fintype.card I - ⌊δ * Fintype.card I⌋₊ ≤ k + 1)
    (h' : Fintype.card I - ⌊δ' * Fintype.card I⌋₊ ≤ k + 1) :
    mcaEvent (ReedSolomon.code D k : Set (I → F)) δ u v g ↔
      mcaEvent (ReedSolomon.code D k : Set (I → F)) δ' u v g := by
  rw [event_iff, event_iff, max_eq_right h, max_eq_right h']

omit [Nonempty I] in
/-- The canonical worst-case MCA probability also stays constant across that range. -/
theorem error_saturated (D : I ↪ F) (k : ℕ) (δ δ' : ℝ≥0)
    (h : Fintype.card I - ⌊δ * Fintype.card I⌋₊ ≤ k + 1)
    (h' : Fintype.card I - ⌊δ' * Fintype.card I⌋₊ ≤ k + 1) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ =
      epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ' := by
  unfold epsMCA
  simp_rw [event_saturated D k δ δ' _ _ _ h h']

/-- The radius-one error already occurs at the closed ball with `n - (k + 1)` errors. -/
theorem error_one_eq_grid (D : I ↪ F) (k : ℕ) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) 1 =
      epsMCA (F := F) (ReedSolomon.code D k : Set (I → F))
        (gridPt (ι := I) (Fintype.card I - (k + 1))) := by
  apply error_saturated
  · simp
  · rw [gridPt_mul_card, Nat.floor_natCast]
    omega

omit [Fintype F] in
private theorem supports_of_events [Finite F] (D : I ↪ F) (k : ℕ) (δ : ℝ≥0)
    (G : Finset F) (x : (I → F) × (I → F))
    (hx : ∀ g : G, mcaEvent (ReedSolomon.code D k : Set (I → F)) δ x.1 x.2 (g : F)) :
    ∃ S : G → Finset I,
      (∀ g, (S g).card = max (Fintype.card I - ⌊δ * Fintype.card I⌋₊) (k + 1)) ∧
      ∀ g, Module.finrank F ↥(space (ReedSolomon.code D k) G S ⊓
        jointSpace (ReedSolomon.code D k) (S g)) <
        Module.finrank F (space (ReedSolomon.code D k) G S) := by
  classical
  let _ := Fintype.ofFinite F
  choose T hT hfold hbad using fun (g : G) => (event_iff D k δ x.1 x.2 (g : F)).mp (hx g)
  refine ⟨T, hT, ?_⟩
  have hspace : x ∈ space (ReedSolomon.code D k) G T := by
    apply (Submodule.mem_iInf _).mpr
    intro g
    exact (quotient_mk_mem_quotientSupportSubmodule_iff (ReedSolomon.code D k) (T g)
      (x.1 + (g : F) • x.2)).mpr (hfold g)
  intro g
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne inf_le_left
  intro heq
  have hj := (inf_eq_left.mp heq) hspace
  exact hbad g ((pairJointAgreesOn_iff_quotientSupport (ReedSolomon.code D k) (T g) x.1 x.2).mpr hj)

/-- The exact support-rank criterion uses one support cardinality at each radius. -/
theorem canonical_failure_iff [SampleableType F]
    (D : I ↪ F) (k B : ℕ) (δ : ℝ≥0) :
    (B : ℝ≥0∞) / Fintype.card F <
        CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k)
          (δ : ℝ) ↔
      ∃ (G : Finset F) (_ : G.card = B + 1) (S : G → Finset I),
        (∀ g, (S g).card = max (Fintype.card I - ⌊δ * Fintype.card I⌋₊) (k + 1)) ∧
        ∀ g, Module.finrank F ↥(space (ReedSolomon.code D k) G S ⊓
          jointSpace (ReedSolomon.code D k) (S g)) <
          Module.finrank F (space (ReedSolomon.code D k) G S) := by
  classical
  let C := ReedSolomon.code D k
  rw [SimultaneousSupportRank.canonical_failure_iff]
  constructor
  · rintro ⟨G, hG, S, hcard, hdim⟩
    obtain ⟨x, hx⟩ := (simultaneous_rank C δ G).mpr ⟨S, hcard, hdim⟩
    exact ⟨G, hG, supports_of_events D k δ G x hx⟩
  · rintro ⟨G, hG, S, hS, hd⟩
    refine ⟨G, hG, S, fun g => (relDist_floor_bound_iff_complement_bound _ _ δ).mp ?_, hd⟩
    rw [hS]
    exact le_max_left _ _

omit [Fintype F] in
/-- Simultaneously put a selected bad label at zero and, when the budget is positive,
a second selected label at one, preserving all bad events by affine reparametrization. -/
private theorem anchor_labels [Finite F] (C : Submodule F (I → F)) (δ : ℝ≥0)
    (G : Finset F) (B : ℕ) (hG : G.card = B + 1) (u v : I → F)
    (hbad : ∀ g : G, mcaEvent (C : Set (I → F)) δ u v (g : F)) :
    ∃ H : Finset F, H.card = B + 1 ∧ 0 ∈ H ∧ (0 < B → 1 ∈ H) ∧
      ∃ x : (I → F) × (I → F), ∀ g : H, mcaEvent (C : Set (I → F)) δ x.1 x.2 (g : F) := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨a, ha, b, hba, hb⟩ :
      ∃ a ∈ G, ∃ b, b ≠ a ∧ (0 < B → b ∈ G) := by
    by_cases h : 0 < B
    · obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (show 1 < G.card by omega)
      exact ⟨a, ha, b, hne.symm, fun _ => hb⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < G.card by omega)
      exact ⟨a, ha, a + 1, by simp, fun h' => (h h').elim⟩
  have hd := sub_ne_zero.mpr hba
  let σ := (MCAEquivariance.mulRightEquiv (b - a) hd).trans (MCAEquivariance.addLeftEquiv a)
  let H := G.map σ.symm.toEmbedding
  have hmem (g : F) : g ∈ H ↔ a + g * (b - a) ∈ G := Finset.mem_map_equiv
  refine ⟨H, (Finset.card_map ..).trans hG, (hmem _).mpr (by simpa using ha),
    fun h => (hmem _).mpr (by simpa using hb h), ⟨u + a • v, (b - a) • v⟩, ?_⟩
  intro g
  apply (MCAEquivariance.mcaEvent_smul_right C hd (g : F)).mpr
  apply (MCAEquivariance.mcaEvent_shift C a _).mpr
  exact hbad ⟨_, (hmem g).mp g.property⟩

/-- The canonical test can enumerate only sets containing zero and, for positive budgets,
one. All support assignments have the same explicitly determined size. -/
theorem anchored_failure_iff [SampleableType F]
    (D : I ↪ F) (k B : ℕ) (δ : ℝ≥0) :
    (B : ℝ≥0∞) / Fintype.card F <
        CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D k)
          (δ : ℝ) ↔
      ∃ (G : Finset F) (_ : G.card = B + 1), 0 ∈ G ∧ (0 < B → 1 ∈ G) ∧
        ∃ S : G → Finset I,
          (∀ g, (S g).card = max (Fintype.card I - ⌊δ * Fintype.card I⌋₊) (k + 1)) ∧
          ∀ g, Module.finrank F ↥(space (ReedSolomon.code D k) G S ⊓
            jointSpace (ReedSolomon.code D k) (S g)) <
            Module.finrank F (space (ReedSolomon.code D k) G S) := by
  classical
  constructor
  · intro h
    obtain ⟨G, hG, S, hs, hd⟩ := (SimultaneousSupportRank.canonical_failure_iff _ _ _).mp h
    obtain ⟨x, hx⟩ := (simultaneous_rank _ δ G).mpr ⟨S, hs, hd⟩
    obtain ⟨H, hH, hz, ho, y, hy⟩ := anchor_labels _ δ G B hG x.1 x.2 hx
    exact ⟨H, hH, hz, ho, supports_of_events D k δ H y hy⟩
  · rintro ⟨G, hG, _, _, S, hS, hd⟩
    exact (canonical_failure_iff D k B δ).mpr ⟨G, hG, S, hS, hd⟩

#print axioms anchored_failure_iff
#print axioms canonical_failure_iff
#print axioms error_saturated

end ProximityGap.ExactSizeMcaSupport
