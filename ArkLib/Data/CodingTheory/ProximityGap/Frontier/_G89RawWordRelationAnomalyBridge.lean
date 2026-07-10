/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R367SignedShadowPairDiscrepancy

/-!
# G89: remove the histogram weights from the relation anomaly

The `NR(v) NR(w)` weights in R367 count ordered pairs of raw index words with shadows `v,w`.
This file makes that interpretation exact.  The shadow off-diagonal condition is retained: merely
distinct words are not enough, since antipodal characteristic-zero cancellations can give two
distinct words the same shadow.

Consequently the single-embedding collision indicator on raw words gives exactly R367's signed
discrepancy and hence R366's `relationAnomaly`, with no inequality or unproved counting socket.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G89RawWordRelationAnomalyBridge

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R367SignedShadowPairDiscrepancy
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-- Ordered raw word pairs whose characteristic-zero shadows are genuinely distinct. -/
def rawShadowOffDiag (n m r : ℕ) : Finset ((Fin r → Fin n) × (Fin r → Fin n)) :=
  ((Finset.univ : Finset (Fin r → Fin n)) ×ˢ Finset.univ).filter fun p =>
    tupleVec n m r p.1 ≠ tupleVec n m r p.2

/-- The map from a raw ordered word pair to its ordered shadow pair. -/
def shadowPair (n m r : ℕ)
    (p : (Fin r → Fin n) × (Fin r → Fin n)) :
    (Fin m → ℤ) × (Fin m → ℤ) :=
  (tupleVec n m r p.1, tupleVec n m r p.2)

/-- A shadow-pair fiber has exactly the product of its two histogram multiplicities. -/
theorem card_rawShadowOffDiag_fiber
    (n m r : ℕ) (p : (Fin m → ℤ) × (Fin m → ℤ))
    (hp : p ∈ (keysR n m r).offDiag) :
    ((rawShadowOffDiag n m r).filter (fun q => shadowPair n m r q = p)).card =
      NR n m r p.1 * NR n m r p.2 := by
  classical
  have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  have hset :
      (rawShadowOffDiag n m r).filter (fun q => shadowPair n m r q = p) =
        ((Finset.univ : Finset (Fin r → Fin n)).filter
            (fun t => tupleVec n m r t = p.1)) ×ˢ
          ((Finset.univ : Finset (Fin r → Fin n)).filter
            (fun u => tupleVec n m r u = p.2)) := by
    ext q
    simp only [rawShadowOffDiag, shadowPair, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hpq⟩
      exact ⟨congrArg Prod.fst hpq, congrArg Prod.snd hpq⟩
    · rintro ⟨hleft, hright⟩
      refine ⟨?_, Prod.ext hleft hright⟩
      intro heq
      apply hpne
      calc
        p.1 = tupleVec n m r q.1 := hleft.symm
        _ = tupleVec n m r q.2 := heq
        _ = p.2 := hright
  rw [hset, Finset.card_product]
  rfl

/-- Generic exact de-weighting: summing a statistic over raw shadow-off-diagonal word pairs is
the same as summing it over shadow pairs with the `NR(v) NR(w)` fiber weight. -/
theorem sum_rawShadowOffDiag_eq_sum_shadowOffDiag
    (n m r : ℕ) (f : ((Fin m → ℤ) × (Fin m → ℤ)) → ℝ) :
    (∑ q ∈ rawShadowOffDiag n m r, f (shadowPair n m r q)) =
      ∑ p ∈ (keysR n m r).offDiag,
        (NR n m r p.1 * NR n m r p.2 : ℝ) * f p := by
  classical
  let Q := rawShadowOffDiag n m r
  let P := (keysR n m r).offDiag
  have hmaps : ∀ q ∈ Q, shadowPair n m r q ∈ P := by
    intro q hq
    simp only [Q, rawShadowOffDiag, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hq
    rw [Finset.mem_offDiag]
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ q.1),
      Finset.mem_image_of_mem _ (Finset.mem_univ q.2), hq⟩
  calc
    (∑ q ∈ rawShadowOffDiag n m r, f (shadowPair n m r q)) =
        ∑ p ∈ P, ∑ q ∈ Q.filter (fun q => shadowPair n m r q = p),
          f (shadowPair n m r q) := by
      exact (Finset.sum_fiberwise_of_maps_to (g := shadowPair n m r)
        (f := fun q => f (shadowPair n m r q)) hmaps).symm
    _ = ∑ p ∈ P,
        (NR n m r p.1 * NR n m r p.2 : ℝ) * f p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hcard := card_rawShadowOffDiag_fiber n m r p hp
      rw [show (∑ q ∈ Q.filter (fun q => shadowPair n m r q = p),
            f (shadowPair n m r q)) =
          ∑ _q ∈ Q.filter (fun q => shadowPair n m r q = p), f p by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcard]
      push_cast
      ring
    _ = ∑ p ∈ (keysR n m r).offDiag,
        (NR n m r p.1 * NR n m r p.2 : ℝ) * f p := rfl

/-- Raw-word signed discrepancy at one field embedding.  Its collision test is stated directly
as equality of the two finite-field tuple sums. -/
noncomputable def rawWordSignedDiscrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) : ℝ :=
  ∑ q ∈ rawShadowOffDiag n m r,
    ((Fintype.card F : ℝ) *
      (if gsumR g n r q.1 = gsumR g n r q.2 then 1 else 0) - 1)

/-- The raw ordered-word discrepancy is exactly R367's histogram-weighted discrepancy. -/
theorem rawWordSignedDiscrepancy_eq_signedShadowPairDiscrepancy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    rawWordSignedDiscrepancy g n m r = signedShadowPairDiscrepancy g n m r := by
  classical
  unfold rawWordSignedDiscrepancy
  calc
    (∑ q ∈ rawShadowOffDiag n m r,
        ((Fintype.card F : ℝ) *
          (if gsumR g n r q.1 = gsumR g n r q.2 then 1 else 0) - 1)) =
      ∑ q ∈ rawShadowOffDiag n m r,
        ((Fintype.card F : ℝ) *
          (if evalVec g m (shadowPair n m r q).1 =
            evalVec g m (shadowPair n m r q).2 then 1 else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro q _
      unfold shadowPair
      rw [gsumR_eq_evalVec_tupleVec g n m r hm hn hg q.1,
        gsumR_eq_evalVec_tupleVec g n m r hm hn hg q.2]
    _ = ∑ p ∈ (keysR n m r).offDiag,
        (NR n m r p.1 * NR n m r p.2 : ℝ) *
          ((Fintype.card F : ℝ) *
            (if evalVec g m p.1 = evalVec g m p.2 then 1 else 0) - 1) :=
      sum_rawShadowOffDiag_eq_sum_shadowOffDiag n m r (fun p =>
        (Fintype.card F : ℝ) *
          (if evalVec g m p.1 = evalVec g m p.2 then 1 else 0) - 1)
    _ = signedShadowPairDiscrepancy g n m r := by
      unfold signedShadowPairDiscrepancy
      simp only [Nat.cast_mul]

/-- **Exact single-embedding raw-word form of the centered relation anomaly.** -/
theorem rawWordSignedDiscrepancy_eq_relationAnomaly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n m r : ℕ) (hm : 0 < m) (hn : n = 2 * m) (hg : g ^ m = -1) :
    rawWordSignedDiscrepancy g n m r = relationAnomaly g n m r := by
  rw [rawWordSignedDiscrepancy_eq_signedShadowPairDiscrepancy g n m r hm hn hg,
    signedShadowPairDiscrepancy_eq_relationAnomaly]

end ArkLib.ProximityGap.Frontier.G89RawWordRelationAnomalyBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G89RawWordRelationAnomalyBridge.card_rawShadowOffDiag_fiber
#print axioms
  ArkLib.ProximityGap.Frontier.G89RawWordRelationAnomalyBridge.sum_rawShadowOffDiag_eq_sum_shadowOffDiag
#print axioms
  ArkLib.ProximityGap.Frontier.G89RawWordRelationAnomalyBridge.rawWordSignedDiscrepancy_eq_relationAnomaly
