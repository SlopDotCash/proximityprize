/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSupplyTheorem

/-!
# Supply-size profile bookkeeping for sub-Johnson ownership (#389)

This file isolates the purely combinatorial profile step used in capped
sub-Johnson supply arguments.  If all agreement sets have size at least `t` and at
most `cap`, then exact-minimal sets `|A| = t` contribute exactly one `t`-subset,
while every strict-large set is charged to its size mass by
`C(|A|,t)·t ≤ |A|·C(cap-1,t-1)`.

The point is diagnostic: any improvement beyond the domain-blind Johnson
incidence bound must control the strict-large mass, not the exact-minimal layer.
-/

open Finset

namespace ProximityGap.PairRank

variable {α : Type} [DecidableEq α]

/-- The reusable convexity edge:
`C(a,t)·t ≤ a·C(cap-1,t-1)` whenever `a ≤ cap` and `1 ≤ t`. -/
theorem choose_mul_le_card_mul_cap_pred {a cap t : ℕ} (ha : a ≤ cap) (ht : 1 ≤ t) :
    a.choose t * t ≤ a * (cap - 1).choose (t - 1) :=
  choose_mul_le_of_le ha ht

open Classical in
/-- Split the total `t`-subset supply into the exact-minimal layer and the
strict-large layer.  If the strict-large agreement-set size mass is at most `M`,
then

`(∑ A∈S, C(|A|,t))·t ≤ #{A∈S | |A|=t}·t + M·C(cap-1,t-1)`.
-/
theorem supply_size_profile_mul_le (S : Finset (Finset α)) {t cap M : ℕ}
    (ht : 1 ≤ t)
    (hmin : ∀ A ∈ S, t ≤ A.card)
    (hcap : ∀ A ∈ S, A.card ≤ cap)
    (hmass : ∑ A ∈ S.filter (fun A => t < A.card), A.card ≤ M) :
    (∑ A ∈ S, A.card.choose t) * t
      ≤ (S.filter (fun A => A.card = t)).card * t
        + M * (cap - 1).choose (t - 1) := by
  classical
  let C := (cap - 1).choose (t - 1)
  have hpoint : ∀ A ∈ S,
      A.card.choose t * t ≤ (if A.card = t then t else A.card * C) := by
    intro A hA
    by_cases hAcard : A.card = t
    · simpa [hAcard]
    · have hstrict : t < A.card := lt_of_le_of_ne (hmin A hA) (Ne.symm hAcard)
      exact le_trans (choose_mul_le_card_mul_cap_pred (hcap A hA) ht) (by rw [if_neg hAcard])
  calc
    (∑ A ∈ S, A.card.choose t) * t
        = ∑ A ∈ S, A.card.choose t * t := by
            rw [Finset.sum_mul]
    _ ≤ ∑ A ∈ S, (if A.card = t then t else A.card * C) := by
            exact Finset.sum_le_sum hpoint
    _ = ∑ A ∈ S.filter (fun A => A.card = t),
          (if A.card = t then t else A.card * C)
        + ∑ A ∈ S.filter (fun A => ¬ A.card = t),
          (if A.card = t then t else A.card * C) := by
            exact (Finset.sum_filter_add_sum_filter_not S (fun A => A.card = t)
              (fun A => if A.card = t then t else A.card * C)).symm
    _ = (S.filter (fun A => A.card = t)).card * t
        + ∑ A ∈ S.filter (fun A => ¬ A.card = t), A.card * C := by
            congr 1
            · calc
                ∑ A ∈ S.filter (fun A => A.card = t),
                    (if A.card = t then t else A.card * C)
                    = ∑ _A ∈ S.filter (fun A => A.card = t), t := by
                        refine Finset.sum_congr rfl ?_
                        intro A hA
                        rw [if_pos (Finset.mem_filter.mp hA).2]
                _ = (S.filter (fun A => A.card = t)).card * t := by
                        rw [Finset.sum_const, smul_eq_mul]
            · refine Finset.sum_congr rfl ?_
              intro A hA
              rw [if_neg (Finset.mem_filter.mp hA).2]
    _ = (S.filter (fun A => A.card = t)).card * t
        + (∑ A ∈ S.filter (fun A => ¬ A.card = t), A.card) * C := by
            rw [Finset.sum_mul]
    _ = (S.filter (fun A => A.card = t)).card * t
        + (∑ A ∈ S.filter (fun A => t < A.card), A.card) * C := by
            congr 2
            apply Finset.sum_congr
            · apply Finset.filter_congr
              intro A hA
              constructor
              · intro hne
                exact lt_of_le_of_ne (hmin A hA) (Ne.symm hne)
              · intro hlt
                exact ne_of_gt hlt
            · intro A _
              rfl
    _ ≤ (S.filter (fun A => A.card = t)).card * t + M * C := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_right C hmass)
              ((S.filter (fun A => A.card = t)).card * t)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.choose_mul_le_card_mul_cap_pred
#print axioms ProximityGap.PairRank.supply_size_profile_mul_le
