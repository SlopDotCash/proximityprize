/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseIncidences
import ArkLib.Research.ProximityGap.Frontier.EighthTransverseCollisions
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeFourHeadEndpoints
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorCoreFreshDecode
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness

/-! # The actual four-head transverse attack at the second-prime eighth rate -/

set_option autoImplicit false
noncomputable section
namespace ArkLib.ProximityGap.Frontier.EighthTransverseAttack
open Finset Polynomial Code _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open SecondPrimeSmoothSeed EighthTransverseMobius EighthTransverseCollisions
open PrizeShapePrimeP30Second
open scoped NNReal ENNReal
local instance : Fact P.Prime := ⟨prime_P⟩

/-- Error radius of the physical four-head construction on the production domain. -/
abbrev radius : ℝ≥0 := 679477248 / 1073741824

/-- The same received pair realizes every finite non-pole label in the union
once its polynomial heads agree on the four cores and meet at each fresh site. -/
theorem union_events {k : ℕ} (hl : 134217728 ≤ k) (hu : k ≤ 394264575)
    (recvA recvB : Fin N → F) (A B : Fin 4 → F[X]) (core : Fin 4 → Finset (Fin N))
    (loci : Fin 16 → Finset (Fin N)) (foreign : Fin 16 → Fin N → Fin 4)
    (degree : ∀ h, (A h).degree < (134217728 : WithBot ℕ) ∧
      (B h).degree < (134217728 : WithBot ℕ))
    (cores : ∀ h, 394264575 ≤ (core h).card)
    (agree : ∀ h, ∀ i ∈ core h, (A h).eval (dom i) = recvA i ∧ (B h).eval (dom i) = recvB i)
    (fresh : ∀ l, ∀ i ∈ loci l, (chart l).den (dom i) ≠ 0 →
      let h := foreign l i
      let z := (chart l).value (dom i)
      (B h).eval (dom i) ≠ recvB i ∧
        (A h).eval (dom i) + z * (B h).eval (dom i) = recvA i + z * recvB i) :
    ∀ γ ∈ (univ.biUnion fun l => labels dom l (loci l)),
      mcaEvent (ReedSolomon.code dom k : Set (Fin N → F)) radius recvA recvB γ := by
  classical
  intro γ hγ
  obtain ⟨l, _, hit⟩ := mem_biUnion.mp hγ
  obtain ⟨i, hr, rfl⟩ := mem_image.mp hit
  let h := foreign l i
  let z := (chart l).value (dom i)
  have ⟨mismatch, hit⟩ := fresh l i (mem_filter.mp hr).1 (mem_filter.mp hr).2
  let u : WordStack F (Fin 2) (Fin N) := ![recvA, recvB]
  have da : (A h).degree < (k : WithBot ℕ) := (degree h).1.trans_le (by exact_mod_cast hl)
  have db : (B h).degree < (k : WithBot ℕ) := (degree h).2.trans_le (by exact_mod_cast hl)
  apply HalfPredecessorCoreFreshDecode.mcaEvent_of_affine_core_fresh dom k radius u z (core h) i
    (A h) (B h)
  · exact fun hi => mismatch (agree h i hi).2
  · exact da
  · exact db
  · apply (degree_add_le _ _).trans_lt
    apply max_lt da
    by_cases hz : z = 0
    · simp [hz]
    · rw [degree_C_mul hz]
      exact db
  · exact hu.trans (cores h)
  · rw [Fintype.card_fin]
    apply le_trans (b := ((394264575 + 1 : ℕ) : ℝ≥0))
    · rw [tsub_mul, one_mul]
      norm_num [radius, N, tsub_le_iff_right]
    · exact_mod_cast Nat.add_le_add_right (cores h) 1
  · exact agree h
  · simpa [u, eval_add, eval_mul, eval_C] using hit
  · exact fun eq => mismatch (congrArg Prod.snd eq)

/-- A literal family of events at this radius supplies its canonical MCA
probability at every positive interleaving width. -/
theorem mass_of_events {k : ℕ} (width : ℕ) [NeZero width] (recvA recvB : Fin N → F)
    (G : Finset F) (count : 2148807811 ≤ G.card)
    (hit : ∀ γ ∈ G, mcaEvent (ReedSolomon.code dom k : Set (Fin N → F)) radius recvA recvB γ) :
    (2148807811 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) radius := by
  rw [epsMCA_interleaved_eq]
  let u : WordStack F (Fin 2) (Fin N) := ![recvA, recvB]
  have hm := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ _ u G hit
  rw [ZMod.card] at hm
  exact (ENNReal.div_le_div_right (by exact_mod_cast count) _).trans hm

open EighthMobiusSites EighthTransverseCore

/-- The union is realized by one concrete pair of received rows for every
dimension in the range of the polynomial degrees and the fixed cores. -/
theorem actual_events {k : ℕ} (hl : 134217728 ≤ k) (hu : k ≤ 394264575) :
    ∃ G : Finset F, 2148807811 ≤ G.card ∧ ∀ γ ∈ G,
      mcaEvent (ReedSolomon.code dom k : Set (Fin N → F)) radius recvA recvB γ := by
  let G := univ.biUnion fun l => labels dom l (loci l)
  refine ⟨G, smooth_union_mass loci total_loci.ge ?_, ?_⟩
  · intro l hl i hi
    rw [← fiber_mod, variable_fiber hl hi]
  · apply union_events hl hu recvA recvB (EighthTransverseRows.rowA locator)
      (EighthTransverseRows.rowB locator) core loci foreign
    · exact EighthTransverseRows.degrees locator locator_natDegree
    · exact fun h => (card_core h).ge
    · exact fun _ _ hi => core_agrees hi
    · exact fun _ _ hi hr => EighthTransverseIncidences.fresh hi hr

/-- At 679477248 errors, all positive widths have probability at least
2148807811 divided by the order of the second named prime field. -/
theorem label_mass {k : ℕ} (hl : 134217728 ≤ k) (hu : k ≤ 394264575)
    (width : ℕ) [NeZero width] :
    (2148807811 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)) radius := by
  obtain ⟨G, count, hit⟩ := actual_events hl hu
  exact mass_of_events width recvA recvB G count hit

/-- The production eighth-rate test fails at the new error count, and its
operational supremum is bounded by the same grid radius. -/
theorem eighth (width : ℕ) [NeZero width] :
    let code := ((ReedSolomon.code dom 134217728 : Set (Fin N → F)) ^⋈ (Fin width))
    let tol : ℝ≥0∞ := 1 / (2 : ℝ≥0∞) ^ 128
    tol < epsMCA (F := F) code radius ∧ mcaDeltaStar (F := F) code tol ≤ radius := by
  dsimp only
  have hb : 1 / (2 : ℝ≥0∞) ^ 128 < (2148807811 : ℝ≥0∞) / (P : ℝ≥0∞) := by
    by_contra! h
    have count := (BoundarySecurityBudget.count_ratio_le_iff prime_P.pos
      (by decide : 0 < 2 ^ 128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h :
        ((2148807811 : ℕ) : ℝ≥0∞) / P ≤ 1 / ((2 ^ 128 : ℕ) : ℝ≥0∞))
    exact (by decide : ¬ 2148807811 ≤ P / 2 ^ 128) count
  have bad := hb.trans_le (label_mass le_rfl (by decide) width)
  exact ⟨bad, mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms actual_events
#print axioms label_mass
#print axioms eighth

end ArkLib.ProximityGap.Frontier.EighthTransverseAttack
