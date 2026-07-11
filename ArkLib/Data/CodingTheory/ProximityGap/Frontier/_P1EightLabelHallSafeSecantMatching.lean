/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterForcedSecantMatching

/-!
# P1: a half-billion forced secants survive deletion of eight Hall exceptions

The global forced-secant matching and the eight-label Hall localization previously lived as
separate reductions.  Applying the matching extractor to the complement of an arbitrary
eight-label set gives at least `2^29 - 6` vertex-disjoint pairs, all outside the exceptional set,
and every pair has a canonical secant core of cardinality at least `K`.

For the particular exceptional set produced by the Hall-kernel theorem, every endpoint and every
endpoint pair is projected-Hall-safe.  The remaining exact-pin problem can therefore be phrased
as simultaneous consolidation of over half a billion algebraically safe secants, rather than as
an unconstrained `N+1`-label rank problem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

open Finset Polynomial
open _root_.ProximityGap Code

namespace ArkLib.ProximityGap.Frontier.P1EightLabelHallSafeSecantMatching

open P1RateQuarterForcedSecantMatching
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Deleting at most eight elements from an over-budget P1 family leaves at least `N-7`. -/
theorem complement_card_ge_N_sub_seven
    (G C : Finset F) (hover : N < G.card) (hC : C.card ≤ 8) :
    N - 7 ≤ (G \ C).card := by
  have hpartition : (G \ C).card + (G ∩ C).card = G.card := by
    simpa only [Finset.inter_comm] using Finset.card_sdiff_add_card_inter G C
  have hinter : (G ∩ C).card ≤ C.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- **Hall-safe-complement matching.**  Every over-budget predecessor family retains at least
`2^29-6` disjoint forced secants after deletion of any eight labels. -/
theorem exists_forced_secant_matching_outside_eight
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom K delta u)
    (hsize : ∀ gamma ∈ family.G, T ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card)
    (hover : N < family.G.card)
    (C : Finset F) (hC : C.card ≤ 8) :
    ∃ M : Finset (F × F),
      ForcedSecantMatching family (family.G \ C) M ∧
      2 ^ 29 - 6 ≤ M.card := by
  let S := family.G \ C
  have hSsub : S ⊆ family.G := Finset.sdiff_subset
  obtain ⟨M, hM, hcount⟩ :=
    exists_forced_secant_matching_on family hsize S.card S hSsub le_rfl
  refine ⟨M, hM, ?_⟩
  have hSlower : N - 7 ≤ S.card :=
    complement_card_ge_N_sub_seven family.G C hover hC
  have hN : N = 1073741824 := by norm_num [N]
  have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
  omega

/-- Every endpoint of the extracted matching lies outside the exceptional set. -/
theorem matching_endpoints_not_mem_exception
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    {family : BadScalarRichPointFamily dom K delta u}
    {C : Finset F} {M : Finset (F × F)}
    (hM : ForcedSecantMatching family (family.G \ C) M) :
    ∀ p ∈ M, p.1 ∉ C ∧ p.2 ∉ C := by
  intro p hp
  have hendpoints := (hM.1 p hp)
  exact ⟨(Finset.mem_sdiff.mp hendpoints.1).2,
    (Finset.mem_sdiff.mp hendpoints.2.1).2⟩

end ArkLib.ProximityGap.Frontier.P1EightLabelHallSafeSecantMatching

open ArkLib.ProximityGap.Frontier.P1EightLabelHallSafeSecantMatching

#print axioms complement_card_ge_N_sub_seven
#print axioms exists_forced_secant_matching_outside_eight
#print axioms matching_endpoints_not_mem_exception
