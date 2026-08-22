/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R367SignedShadowPairDiscrepancy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83MMaximalCommonCancellation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R322SignedWalkEndpointEnvelope

/-!
# G91: exact maximal-cancellation bag decomposition of the relation anomaly

G89 removes the `NR` histogram weights by lifting to ordered raw words.  Here those word pairs are
grouped by their unique maximal common multiset.  A triple `(L,R,P)` consists of the two residual
cores and common padding.  Its exact ordered endpoint multiplicity is

`countPerms (L + P) * countPerms (R + P)`.

This formula retains repetitions and stabilizers exactly; no factorial ceiling is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.G91MaximalCancellationBagDiscrepancy

open ArkLib.ProximityGap.Frontier.G83MMaximalCommonCancellation
open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope
open ArkLib.ProximityGap.Frontier.R366CenteredRelationAnomaly

/-- The G89 raw domain, repeated here so this independently checkable frontier file does not
require an olean for the concurrently introduced G89 module. -/
def rawShadowOffDiag (n m r : ℕ) : Finset ((Fin r → Fin n) × (Fin r → Fin n)) :=
  ((Finset.univ : Finset (Fin r → Fin n)) ×ˢ Finset.univ).filter fun p =>
    tupleVec n m r p.1 ≠ tupleVec n m r p.2

/-- The canonical residual-left, residual-right, common-padding bag triple. -/
structure CancellationBagTriple (A : Type*) where
  left : Multiset A
  right : Multiset A
  padding : Multiset A
deriving DecidableEq

/-- Canonical maximal-common cancellation of the value bags of an ordered word pair. -/
def cancellationBagTriple {n r : ℕ}
    (q : (Fin r → Fin n) × (Fin r → Fin n)) : CancellationBagTriple (Fin n) where
  left := leftCore (tupleMultiset q.1) (tupleMultiset q.2)
  right := rightCore (tupleMultiset q.1) (tupleMultiset q.2)
  padding := commonPart (tupleMultiset q.1) (tupleMultiset q.2)

/-- The finite set of maximal-cancellation triples actually arising from shadow-off-diagonal
ordered word pairs. -/
def cancellationBagTriples (n m r : ℕ) : Finset (CancellationBagTriple (Fin n)) :=
  (rawShadowOffDiag n m r).image cancellationBagTriple

/-- A tuple's shadow depends only on its value multiset, including repeated values. -/
theorem tupleVec_eq_of_tupleMultiset_eq {n m r : ℕ}
    {t u : Fin r → Fin n} (h : tupleMultiset t = tupleMultiset u) :
    tupleVec n m r t = tupleVec n m r u := by
  funext j
  have hj := congrArg Multiset.sum
    (congrArg (Multiset.map (fun a => vecOf n m a j)) h)
  simpa [tupleVec, tupleMultiset, List.map_ofFn, List.sum_ofFn] using hj

/-- Every raw pair in a fixed canonical triple fiber has the reconstructed endpoint bags. -/
theorem tupleMultisets_eq_reconstruct_of_cancellationBagTriple_eq {n r : ℕ}
    {q : (Fin r → Fin n) × (Fin r → Fin n)} {T : CancellationBagTriple (Fin n)}
    (hT : cancellationBagTriple q = T) :
    tupleMultiset q.1 = T.left + T.padding ∧
      tupleMultiset q.2 = T.right + T.padding := by
  subst T
  exact ⟨(left_reconstruct (tupleMultiset q.1) (tupleMultiset q.2)).symm,
    (right_reconstruct (tupleMultiset q.1) (tupleMultiset q.2)).symm⟩

/-- Conversely, the reconstructed endpoint bags determine the canonical triple, provided the
triple is known to arise canonically. -/
theorem cancellationBagTriple_eq_of_tupleMultisets_eq_reconstruct {n m r : ℕ}
    {T : CancellationBagTriple (Fin n)} (hT : T ∈ cancellationBagTriples n m r)
    {q : (Fin r → Fin n) × (Fin r → Fin n)}
    (hleft : tupleMultiset q.1 = T.left + T.padding)
    (hright : tupleMultiset q.2 = T.right + T.padding) :
    cancellationBagTriple q = T := by
  rw [cancellationBagTriples, Finset.mem_image] at hT
  obtain ⟨q₀, hq₀, rfl⟩ := hT
  obtain ⟨hleft₀, hright₀⟩ :=
    tupleMultisets_eq_reconstruct_of_cancellationBagTriple_eq
      (q := q₀) (T := cancellationBagTriple q₀) rfl
  have hleftBag : tupleMultiset q.1 = tupleMultiset q₀.1 := hleft.trans hleft₀.symm
  have hrightBag : tupleMultiset q.2 = tupleMultiset q₀.2 := hright.trans hright₀.symm
  unfold cancellationBagTriple
  rw [hleftBag, hrightBag]

/-- The shadow-off-diagonal guard is automatic for every pair with the reconstructed endpoint
bags of an actually arising triple. -/
theorem mem_rawShadowOffDiag_of_reconstructed_bags {n m r : ℕ}
    {T : CancellationBagTriple (Fin n)} (hT : T ∈ cancellationBagTriples n m r)
    {q : (Fin r → Fin n) × (Fin r → Fin n)}
    (hleft : tupleMultiset q.1 = T.left + T.padding)
    (hright : tupleMultiset q.2 = T.right + T.padding) :
    q ∈ rawShadowOffDiag n m r := by
  rw [cancellationBagTriples, Finset.mem_image] at hT
  obtain ⟨q₀, hq₀, hq₀T⟩ := hT
  have hrec₀ := tupleMultisets_eq_reconstruct_of_cancellationBagTriple_eq hq₀T
  have hvecLeft : tupleVec n m r q.1 = tupleVec n m r q₀.1 :=
    tupleVec_eq_of_tupleMultiset_eq (hleft.trans hrec₀.1.symm)
  have hvecRight : tupleVec n m r q.2 = tupleVec n m r q₀.2 :=
    tupleVec_eq_of_tupleMultiset_eq (hright.trans hrec₀.2.symm)
  simp only [rawShadowOffDiag, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and] at hq₀ ⊢
  rwa [hvecLeft, hvecRight]

/-- **Exact stabilizer weight.** The raw-pair fiber of an arising maximal-cancellation triple has
the product of the two endpoint multinomial counts. -/
theorem card_cancellationBagTriple_fiber_eq_countPerms {n m r : ℕ}
    (T : CancellationBagTriple (Fin n)) (hT : T ∈ cancellationBagTriples n m r) :
    ((rawShadowOffDiag n m r).filter (fun q => cancellationBagTriple q = T)).card =
      (T.left + T.padding).countPerms * (T.right + T.padding).countPerms := by
  classical
  have hcardLeft : (T.left + T.padding).card = r := by
    rw [cancellationBagTriples, Finset.mem_image] at hT
    obtain ⟨q, hq, rfl⟩ := hT
    change (leftCore (tupleMultiset q.1) (tupleMultiset q.2) +
      commonPart (tupleMultiset q.1) (tupleMultiset q.2)).card = r
    rw [left_reconstruct]
    simp [tupleMultiset]
  have hcardRight : (T.right + T.padding).card = r := by
    rw [cancellationBagTriples, Finset.mem_image] at hT
    obtain ⟨q, hq, rfl⟩ := hT
    change (rightCore (tupleMultiset q.1) (tupleMultiset q.2) +
      commonPart (tupleMultiset q.1) (tupleMultiset q.2)).card = r
    rw [right_reconstruct]
    simp [tupleMultiset]
  have hset :
      (rawShadowOffDiag n m r).filter (fun q => cancellationBagTriple q = T) =
        ((Finset.univ : Finset (Fin r → Fin n)).filter
            (fun t => tupleMultiset t = T.left + T.padding)) ×ˢ
          ((Finset.univ : Finset (Fin r → Fin n)).filter
            (fun u => tupleMultiset u = T.right + T.padding)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hq, hqT⟩
      exact tupleMultisets_eq_reconstruct_of_cancellationBagTriple_eq hqT
    · rintro ⟨hleft, hright⟩
      exact ⟨mem_rawShadowOffDiag_of_reconstructed_bags hT hleft hright,
        cancellationBagTriple_eq_of_tupleMultisets_eq_reconstruct hT hleft hright⟩
  have hCL := tupleMultiset_fiber_card_eq_countPerms
    (A := Fin n) r (T.left + T.padding) hcardLeft
  have hCR := tupleMultiset_fiber_card_eq_countPerms
    (A := Fin n) r (T.right + T.padding) hcardRight
  rw [hset, Finset.card_product]
  simpa using congrArg₂ (· * ·) hCL hCR

/-- Generic exact regrouping by canonical maximal-cancellation triples. -/
theorem sum_rawShadowOffDiag_eq_sum_cancellationBagTriples
    (n m r : ℕ) (f : CancellationBagTriple (Fin n) → ℝ) :
    (∑ q ∈ rawShadowOffDiag n m r, f (cancellationBagTriple q)) =
      ∑ T ∈ cancellationBagTriples n m r,
        ((T.left + T.padding).countPerms * (T.right + T.padding).countPerms : ℝ) * f T := by
  classical
  rw [show (∑ q ∈ rawShadowOffDiag n m r, f (cancellationBagTriple q)) =
      ∑ T ∈ cancellationBagTriples n m r,
        ∑ q ∈ (rawShadowOffDiag n m r).filter (fun q => cancellationBagTriple q = T),
          f (cancellationBagTriple q) by
    exact (Finset.sum_fiberwise_of_maps_to (g := cancellationBagTriple)
      (f := fun q => f (cancellationBagTriple q))
      (fun q hq => Finset.mem_image_of_mem cancellationBagTriple hq)).symm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show (∑ q ∈ (rawShadowOffDiag n m r).filter
      (fun q => cancellationBagTriple q = T), f (cancellationBagTriple q)) =
      ∑ _q ∈ (rawShadowOffDiag n m r).filter
        (fun q => cancellationBagTriple q = T), f T by
    apply Finset.sum_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2]]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_cancellationBagTriple_fiber_eq_countPerms T hT]
  push_cast
  ring

end ArkLib.ProximityGap.Frontier.G91MaximalCancellationBagDiscrepancy

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G91MaximalCancellationBagDiscrepancy.tupleVec_eq_of_tupleMultiset_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G91MaximalCancellationBagDiscrepancy.card_cancellationBagTriple_fiber_eq_countPerms
#print axioms
  ArkLib.ProximityGap.Frontier.G91MaximalCancellationBagDiscrepancy.sum_rawShadowOffDiag_eq_sum_cancellationBagTriples
