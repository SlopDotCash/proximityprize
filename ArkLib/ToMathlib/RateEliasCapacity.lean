/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Lattice2
import ArkLib.Data.CodingTheory.ProximityGap.LDThresholdJohnsonSq

/-!
# Johnson-capacity route for `OrdinaryRSCapacityAtPrizeRates`

The lower-side hypothesis `OrdinaryRSCapacityAtPrizeRates domain τ ℓ` (defined in
`GrandChallengesLattice.lean`) asks, for each ABF26 prize rate `r ∈ {1/2,1/4,1/8,1/16}`,
for an *upper* bound on the maximised list size of the ordinary Reed-Solomon code at the
proposed predecessor lattice radius:

  `Λ(RS_{k_r}, (τ r).val / n) ≤ ℓ r`.

The proven Elias volume bound `linear_lambda_ge_elias_volume_eli57` is a *lower* bound on
`Λ`; it lives on the **obstruction** side of this frontier (see
`not_ordinaryRSCapacityAtPrizeRates_of_elias_volume_gt`) and cannot establish the cap.

The cap is supplied instead by the **Johnson** capacity machinery: the proven
`ProximityGap.Lambda_le_of_johnson_sq` (ABF26 Theorem 3.2, optimal-`β` squared form) gives
exactly `Λ(C, j/n) ≤ ℓ` from a concrete, `norm_num`-checkable polynomial inequality in
`(n, q, ℓ, j, minDist C)`.  This file packages that reduction at the four prize rates.

The remaining payload after this reduction is the per-rate squared Johnson inequality plus the
two standard RS facts `minDist = n - k + 1` and `finrank = k`.  The squared Johnson inequality
holding at a given `(τ r, ℓ r)` is the genuine capacity content; whenever the proposed radius
sits inside the Johnson list-decoding region of the rate-`r` RS code, the inequality is a finite
numeric check.  This is the provable lower side of the Lambda-Elias frontier; the genuinely open
research boundary is only the strip between the Johnson radius and the full list-decoding
capacity radius (the Johnson→capacity gap), which is not needed for the cap when `(τ r, ℓ r)`
lands in the Johnson region.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable
open ProximityGap.GrandChallengesLattice

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Per-rate Johnson cap for the ordinary-RS prize capacity, abstract `minDist` form.**

For each prize rate, the proven optimal-`β` squared Johnson bound
(`Lambda_le_of_johnson_sq`) gives the maximised list-size cap
`Λ(RS_{k_r}, (τ r).val / n) ≤ ℓ r` directly from the squared Johnson polynomial inequality
`hsq`.  This is exactly `OrdinaryRSCapacityAtPrizeRates`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  intro r
  have hbase :
      Lambda
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        ((((((τ r).val : ℕ) : ℝ≥0)) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
          (ℓ r : ℕ∞) :=
    Lambda_le_of_johnson_sq
      (C := (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      (j := (τ r).val) (ℓ := ℓ r) hq1 (hP r) (hsq r)
  -- `OrdinaryRSCapacityAtPrizeRates` uses the same radius up to the trivial `((τ r).val : ℕ)`
  -- coercion identity, so the goal matches `hbase` definitionally.
  exact hbase

/-- **Per-rate Johnson cap with the RS distance specialised.**

Same as `ordinaryRSCapacityAtPrizeRates_of_johnson_sq`, but the squared Johnson inequality is
phrased with the closed-form Reed-Solomon minimum distance `n - k + 1` already substituted,
supplied via the standard RS facts behind `hminDist`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDistance
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hminDist : ∀ r : Fin 4,
      Code.minDist
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) =
        Fintype.card ι - ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1)
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityAtPrizeRates_of_johnson_sq domain τ ℓ hq1 hP ?_
  intro r
  simpa [hminDist r] using hsq r

/-- **Per-rate Johnson cap from RS degree side conditions.**

The numerics-facing form: from `0 < k_r` and `k_r ≤ n`, the standard RS fact
`minDist = n - k + 1` (`ReedSolomon.minDist_eq'`) is discharged automatically, leaving only the
squared Johnson arithmetic certificate at the closed-form distance.  This mirrors
`listPrizeLatticeResolved_of_johnson_sq_rsDegreeLe_and_elias_next`, but lands directly on the
capacity predicate `OrdinaryRSCapacityAtPrizeRates`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDegreeLe
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDistance
    domain τ ℓ hq1 hP ?_ hsq
  intro r
  haveI : NeZero ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ := ⟨(hdeg_pos r).ne'⟩
  exact ReedSolomon.minDist_eq' (α := domain) (hdeg_le r)

/-! ## Pointwise (native finite-list) route — the issue's preferred target

The reductions above land on the maximised-`Λ` predicate `OrdinaryRSCapacityAtPrizeRates`.
The issue body flags `OrdinaryRSCapacityPointwiseAtPrizeRates` — the *native finite
combinatorial* statement that, for every received word `f`, the finite list
`closeCodewordsRelFinset RS_{k_r} f ((τ r).val / n)` has cardinality `≤ ℓ r` — as the
preferred route.  The lemmas below discharge that predicate directly from the same per-rate
squared Johnson certificate, routing through the proven pointwise card bound
`JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist` (which lands on
`Finset.card`) rather than the maximised-`Λ` packaging.  At the grid radius `(τ r).val / n` the
floor `⌊((τ r).val / n) · n⌋ = (τ r).val` is exact (`floor_grid_mul`), so the radius-side
hypotheses are stated directly in the lattice index. -/

/-- **Per-rate pointwise Johnson cap for the ordinary-RS prize capacity, abstract `minDist`
form.**

For each prize rate and *each received word* `f`, the proven optimal-`β` squared Johnson
pointwise bound (`closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist`) gives the
native finite close-list cap
`(closeCodewordsRelFinset RS_{k_r} f ((τ r).val / n)).card ≤ ℓ r` directly from the squared
Johnson polynomial inequality `hsq`.  This is exactly the issue's preferred
`OrdinaryRSCapacityPointwiseAtPrizeRates`. -/
theorem ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  intro r f
  classical
  have hδ : (0 : ℝ) ≤ (((((τ r).val : ℕ) : ℝ≥0) /
      (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hfl : ⌊(((((τ r).val : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
      * (Fintype.card ι : ℝ)⌋₊ = (τ r).val :=
    floor_grid_mul (ι := ι) (τ r).val
  exact JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist
    (C := (ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
    (f := f)
    (δ := (((((τ r).val : ℕ) : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ))
    (ℓ := ℓ r) hδ hq1
    (by rw [hfl]; exact hP r) (by rw [hfl]; exact hsq r)

/-- **Per-rate pointwise Johnson cap with the RS distance specialised.**

Same as `ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq`, but the squared Johnson
inequality is phrased with the closed-form Reed-Solomon minimum distance `n - k + 1` already
substituted, supplied via the standard RS facts behind `hminDist`. -/
theorem ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq_rsDistance
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hminDist : ∀ r : Fin 4,
      Code.minDist
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) =
        Fintype.card ι - ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1)
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq domain τ ℓ hq1 hP ?_
  intro r
  simpa [hminDist r] using hsq r

/-- **Per-rate pointwise Johnson cap from RS degree side conditions.**

The numerics-facing pointwise form: from `0 < k_r` and `k_r ≤ n`, the standard RS fact
`minDist = n - k + 1` (`ReedSolomon.minDist_eq'`) is discharged automatically, leaving only the
squared Johnson arithmetic certificate at the closed-form distance.  Pointwise sibling of
`ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDegreeLe`. -/
theorem ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq_rsDegreeLe
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityPointwiseAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq_rsDistance
    domain τ ℓ hq1 hP ?_ hsq
  intro r
  haveI : NeZero ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ := ⟨(hdeg_pos r).ne'⟩
  exact ReedSolomon.minDist_eq' (α := domain) (hdeg_le r)

/-- The pointwise Johnson reduction agrees with the maximised-`Λ` one: feeding the same
squared Johnson certificate through the pointwise route and then `Lambda_le_natCast` recovers
exactly `OrdinaryRSCapacityAtPrizeRates`.  This certifies that the issue's preferred pointwise
target and the maximised-`Λ` target are discharged from one and the same numeric payload. -/
theorem ordinaryRSCapacityAtPrizeRates_of_pointwise_johnson_sq
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ :=
  GrandChallengesLattice.ordinaryRSCapacityAtPrizeRates_of_pointwise domain τ ℓ
    (ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq domain τ ℓ hq1 hP hsq)

/-! ## End-to-end: Johnson capacity ⊕ adjacent Elias certificate resolve the LD prize

The capacity reductions above land on the named lower-side predicate
`OrdinaryRSCapacityAtPrizeRates`.  The proven
`GrandChallengesLattice.listPrizeLatticeResolved_of_ordinaryRSCapacityAtPrizeRates_and_elias_next`
consumes that predicate (plus the interleaving budget and the adjacent Elias-volume failure
certificate) to resolve the faithful four-rate list-decoding lattice prize.  Composing the two
gives a single criterion whose only remaining content is the per-rate Johnson capacity
inequality `hsq` and the per-rate adjacent Elias-volume inequality `hvol_next` — both finite
numeric checks at the concrete prize degrees `k_r = ⌊ρ_r · n⌋`. -/

/-- **Johnson-capacity ⊕ Elias closing of the faithful four-rate list-decoding lattice prize.**

For each prize rate, the squared Johnson inequality `hsq` supplies the ordinary-RS list-size
cap `Λ(RS_{k_r}, (τ r).val / n) ≤ ℓ r` (the lower side of the Lambda-Elias frontier, via
`Lambda_le_of_johnson_sq`), and the Elias-volume inequality `hvol_next` certifies the failure
at the adjacent index `(τ r).val + 1`.  Together they pin the faithful list-decoding lattice
threshold at `τ`.  This is the capacity-resolved analogue of
`listPrizeLatticeResolved_of_johnson_sq_and_elias_next`, routed explicitly through the named
`OrdinaryRSCapacityAtPrizeRates` predicate. -/
theorem listPrizeLatticeResolved_of_ordinaryRSCapacity_johnson_sq_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ :=
  listPrizeLatticeResolved_of_ordinaryRSCapacityAtPrizeRates_and_elias_next
    domain m τ ℓ hm hnext
    (ordinaryRSCapacityAtPrizeRates_of_johnson_sq domain τ ℓ hq1 hP hsq)
    hpow hvol_next hne

end ProximityGap
#print axioms ProximityGap.ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq
#print axioms ProximityGap.ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq_rsDistance
#print axioms ProximityGap.ordinaryRSCapacityPointwiseAtPrizeRates_of_johnson_sq_rsDegreeLe
#print axioms ProximityGap.ordinaryRSCapacityAtPrizeRates_of_pointwise_johnson_sq
