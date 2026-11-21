/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateEighthFullWiring
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket

/-!
# Shortening the rate-one-eighth bad-scalar bound

A witness with at most `N/2 - 1` errors on an original domain of length `n` retains
its error count on a longer domain of length `N` after locator extension. The longer
domain may be arbitrary. Its code dimension is `k + (N-n)`. The existing one-eighth
incidence theorem therefore controls the original bad scalars whenever this dimension
fits its rate requirement.
-/

open Finset Code
open _root_.ProximityGap
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.ShortenedDomainGoodSide

open LocatorShortening

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n N k : ℕ}

open Classical in
/-- Uniform original-domain bound at the predecessor of `(N/2)/n`. -/
theorem predecessor_badCount_le [NeZero n] [NeZero N]
    (dom : Fin n ↪ F) (hN : n ≤ N) (hfield : N ≤ Fintype.card F)
    (heven : N = 2 * (N / 2)) (hlarge : 1699 ≤ N / 2) (ha : N / 2 ≤ n)
    (hk : 1 ≤ k) (hrate : 8 * (k + (N - n)) ≤ N)
    (u : WordStack F (Fin 2) (Fin n)) :
    (Finset.univ.filter fun γ : F =>
      mcaEvent (ReedSolomon.code dom k : Set (Fin n → F))
        (PrizeShapeRateHalfBracket.predecessorRadius n (N / 2)) (u 0) (u 1) γ).card ≤ N := by
  classical
  obtain ⟨old, dom', hrestrict⟩ := exists_extended_domain dom hN hfield
  let u' : WordStack F (Fin 2) (Fin N) := fun b => RSLocatorExtension.extendWord old dom' (u b)
  let δ := PrizeShapeRateHalfBracket.predecessorRadius n (N / 2)
  let δ' := R382HalfRadiusPinConnector.halfPredecessorRadius N
  have hsize (a : ℕ) (h : (1 - δ) * n ≤ (a : ℝ≥0)) :
      (1 - δ') * N ≤ ((a + (N - n) : ℕ) : ℝ≥0) := by
    change (1 - (((N / 2 - 1 : ℕ) : ℝ≥0) / n)) * n ≤ (a : ℝ≥0) at h
    change (1 - (((N / 2 - 1 : ℕ) : ℝ≥0) / N)) * N ≤ _
    rw [agreement_mass n (N / 2 - 1)] at h
    rw [agreement_mass N (N / 2 - 1)]
    have hnat : n - (N / 2 - 1) ≤ a := by exact_mod_cast h
    exact_mod_cast (by omega : N - (N / 2 - 1) ≤ a + (N - n))
  have htransfer := RSLocatorExtension.badScalar_card_le_extension old dom' hk hsize (u 0) (u 1)
  rw [hrestrict] at htransfer
  exact htransfer.trans
    (HalfPredecessorRateEighthFullWiring.halfPredecessor_badScalar_filter_card_le_length
      dom' heven hlarge (by omega : 1 ≤ k + (N - n)) hrate u')

end ArkLib.ProximityGap.Frontier.ShortenedDomainGoodSide

#print axioms ArkLib.ProximityGap.Frontier.ShortenedDomainGoodSide.predecessor_badCount_le
