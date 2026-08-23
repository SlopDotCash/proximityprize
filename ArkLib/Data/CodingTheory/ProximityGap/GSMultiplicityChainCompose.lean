/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.MatchingExtractor
import ArkLib.ToMathlib.BivariateDegreeToolkit
import ArkLib.Data.CodingTheory.ProximityGap.GSMultiplicityCore

/-!
# GS multiplicity count gap discharged in the real BCIKS20 §5 chain (issues #93/#94/#8)

Composes the GSMultiplicityCore count-from-radius result into the in-tree §5 theorem
Q_vanishes_on_close_codeword_graph: Q_vanishes_on_close_codeword_graph_of_Qdeg derives the graph
vanishing (eval_on_Z Q z).eval Pz = 0 with the FREE count side condition REPLACED by {the Johnson
radius dist/n < proximity_gap_johnson + #A = n-dist + the Q_deg weighted-degree budget transported
through the Z-specialization and reconciled with proximity_gap_degree_bound}. So the §5 graph
vanishing now rests on {Q_multiplicity (proven) + Q_deg (proven) + the list-decoding radius (given)}
-- the free count hypothesis is gone. Q_graph_factor_dvd_of_Qdeg gives the matching-factor form.
-/


/-!
# Core 3 — composing the keystone with the structure's own `Q_deg` (free count fully gone)

`GSMultiplicityCore.Q_vanishes_on_close_codeword_graph_of_radius` already discharges the *raw count*
side condition `natWeightedDegree (eval_on_Z Q z) 1 k < m·#A` of the BCIKS20 §5 keystone
`Agreement.Q_vanishes_on_close_codeword_graph`, but at the cost of a **named**
weighted-degree-budget hypothesis

  `hwdeg : natWeightedDegree (eval_on_Z Q z) 1 k ≤ proximity_gap_degree_bound k n m`.

This file removes that named hypothesis entirely.  It is not an analytic premise: it is exactly
`ModifiedGuruswami.Q_deg` (a *proven field* of the `h_gs` solution the keystone already takes),
transported through `Z ↦ z` and reconciled with `proximity_gap_degree_bound`.

## The two pieces of bookkeeping

* **Transport.**  `BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le` (proven):
  specialising `Z ↦ z` never raises the `(1,k)`-weighted degree, i.e.
  `natWeightedDegree (eval_on_Z Q z) 1 k ≤ natWeightedDegree Q 1 k`.

* **Degree-constant reconciliation.**  `ModifiedGuruswami.Q_deg` reads
  `natWeightedDegree Q 1 k < D_X ((k+1)/n) n m` (a strict `ℕ < ℝ` bound against the *real*
  `D_X ρ n m = (m+1/2)·√ρ·n`).  And `proximity_gap_degree_bound k n m = ⌊D_X ((k+1)/n) n m⌋₊` —
  *definitionally the floor of the same real* (both unfold to `⌊(m+1/2)·√((k+1:ℚ)/n)·n⌋₊`).  A
  natural number strictly below a nonnegative real is `≤` its floor (`Nat.le_floor`), so
  `Q_deg` gives `natWeightedDegree Q 1 k ≤ proximity_gap_degree_bound k n m` with **no** extra
  hypothesis.

Chaining the two: `natWeightedDegree (eval_on_Z Q z) 1 k ≤ natWeightedDegree Q 1 k ≤
proximity_gap_degree_bound k n m` — exactly the `hwdeg` that
`Q_vanishes_on_close_codeword_graph_of_radius` consumes, now *derived* from `h_gs.Q_deg`.

## Deliverable

`Q_vanishes_on_close_codeword_graph_of_Qdeg` — the §5 graph-vanishing
`(eval_on_Z Q z).eval (Pz hS) = 0` with the free count **and** the named degree budget both gone;
the remaining hypotheses are precisely

* `h_gs : ModifiedGuruswami …` (proven — carries `Q_multiplicity` *and* `Q_deg`),
* the genuine Johnson-radius datum `dist/n < proximity_gap_johnson k n m`,
* the cardinality bookkeeping `A.card = n - dist` and `dist ≤ n`, `k+1 ≤ n`, `1 ≤ m`,
* the agreement matching `hA` and nonvanishing `hQz_ne` already required by the keystone.

`sorry`/`admit`/`axiom`/`native_decide`-free.
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace Core3Compose

open ProximityGap Trivariate RatFunc GuruswamiSudan

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-! ## The degree-constant reconciliation: `D_X` ↔ `proximity_gap_degree_bound`

`proximity_gap_degree_bound k n m` is *by definition* `⌊D_X ((k+1)/n) n m⌋₊`. -/

/-- `proximity_gap_degree_bound k n m = ⌊D_X ((k+1)/n) n m⌋₊`: the integer GS degree budget is the
floor of the real `D_X` bound at rate `(k+1)/n`.  Both unfold to `⌊(m+1/2)·√((k+1:ℚ)/n)·n⌋₊`. -/
theorem proximity_gap_degree_bound_eq_floor_D_X (k n m : ℕ) :
    proximity_gap_degree_bound k n m = ⌊ProximityGap.D_X ((k + 1) / (n : ℚ)) n m⌋₊ := by
  unfold proximity_gap_degree_bound ProximityGap.D_X
  norm_num

/-- **Degree-constant reconciliation.**  A `(1,k)`-weighted degree (a natural number) that is
strictly below the *real* `D_X ((k+1)/n) n m` bound — i.e. the content of `ModifiedGuruswami.Q_deg`
— is `≤` the integer GS degree budget `proximity_gap_degree_bound k n m`.  Pure `Nat.le_floor`
bookkeeping over the identity `proximity_gap_degree_bound = ⌊D_X⌋₊`; no analytic input. -/
theorem natWeightedDegree_le_proximity_gap_degree_bound_of_lt_D_X
    {d k m : ℕ}
    (hd : (d : ℝ) < ProximityGap.D_X ((k + 1) / (n : ℚ)) n m) :
    d ≤ proximity_gap_degree_bound k n m := by
  rw [proximity_gap_degree_bound_eq_floor_D_X]
  exact Nat.le_floor (le_of_lt hd)

/-- **`Q_deg`, transported and reconciled.**  From the `ModifiedGuruswami` solution `Q` (whose
`Q_deg` field gives `natWeightedDegree Q 1 k < D_X ((k+1)/n) n m`), the specialised interpolant
satisfies the integer GS weighted-degree budget
`natWeightedDegree (eval_on_Z Q z) 1 k ≤ proximity_gap_degree_bound k n m`.

This is exactly the `hwdeg` hypothesis of
`Core3GSMultiplicity.Q_vanishes_on_close_codeword_graph_of_radius`, now *derived* from the proven
`Q_deg` field — `Z ↦ z` only shrinks the weighted degree
(`BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le`), and the strict real bound floors to
the integer budget. -/
theorem Qdeg_eval_on_Z_le_proximity_gap_degree_bound
    {m k : ℕ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F} {z : F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k ≤
      proximity_gap_degree_bound k n m := by
  -- Transport: `Z ↦ z` does not raise the `(1,k)`-weighted degree.
  have htransport :
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k ≤
        Bivariate.natWeightedDegree Q 1 k :=
    ArkLib.BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le Q z k
  -- Reconcile the trivariate `Q_deg` real bound with the integer GS budget.
  have hQdeg : Bivariate.natWeightedDegree Q 1 k ≤ proximity_gap_degree_bound k n m :=
    natWeightedDegree_le_proximity_gap_degree_bound_of_lt_D_X (n := n) h_gs.Q_deg
  exact le_trans htransport hQdeg

/-! ## The composition: keystone with `Q_deg` consumed, free count fully discharged -/

variable [DecidableEq (RatFunc F)] [Finite F]

/-- **BCIKS20 §5 graph vanishing from the Johnson radius alone — free count *and* degree budget
gone.**

This is `Core3GSMultiplicity.Q_vanishes_on_close_codeword_graph_of_radius` with its remaining named
weighted-degree-budget hypothesis `hwdeg` discharged from the solution's own `Q_deg` field
(via `Qdeg_eval_on_Z_le_proximity_gap_degree_bound`).

The §5 graph-vanishing `(eval_on_Z Q z).eval (Pz hS) = 0` now rests on exactly:

* `h_gs : ModifiedGuruswami …` — proven; supplies **both** `Q_multiplicity` (the order-`m`
  agreement) **and** `Q_deg` (the weighted-degree budget);
* `hradius : dist/n < proximity_gap_johnson k n m` — the genuine list-decoding premise;
* `hcard : A.card = n - dist`, `hdist : dist ≤ n`, `hk : k+1 ≤ n`, `hm : 1 ≤ m` — cardinality /
  combinatorial bookkeeping;
* `hA`, `hQz_ne` — the agreement matching and nonvanishing already demanded by the keystone.

The free Johnson-count side condition is **gone**, and so is the named degree budget. -/
theorem Q_vanishes_on_close_codeword_graph_of_Qdeg [DecidableEq (Polynomial F)]
    {m k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hcard : A.card = n - dist) :
    (Trivariate.eval_on_Z Q z).eval (Pz hS) = 0 := by
  classical
  exact Core3GSMultiplicity.Q_vanishes_on_close_codeword_graph_of_radius
      (F := F) (h_gs := h_gs) hS hQz_ne A hA hk hm hdist hradius
      (Qdeg_eval_on_Z_le_proximity_gap_degree_bound (z := z) h_gs) hcard

/-- `pg_eval_on_Z` form of `Q_vanishes_on_close_codeword_graph_of_Qdeg` (matching the extraction
toolbox API), with the free count and degree budget both discharged from `h_gs`. -/
theorem Q_vanishes_on_close_codeword_graph_pg_of_Qdeg [DecidableEq (Polynomial F)]
    {m k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hcard : A.card = n - dist) :
    (pg_eval_on_Z (F := F) Q z).eval (Pz hS) = 0 := by
  classical
  exact Core3GSMultiplicity.Q_vanishes_on_close_codeword_graph_pg_of_radius
      (F := F) (h_gs := h_gs) hS hQz_ne A hA hk hm hdist hradius
      (Qdeg_eval_on_Z_le_proximity_gap_degree_bound (z := z) h_gs) hcard

/-- Matching-factor divisibility form: `X - C (Pz hS) ∣ pg_eval_on_Z Q z` from the Johnson radius
alone (free count and degree budget discharged from `h_gs`). -/
theorem Q_graph_factor_dvd_of_Qdeg [DecidableEq (Polynomial F)]
    {m k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hcard : A.card = n - dist) :
    Polynomial.X - Polynomial.C (Pz hS) ∣ pg_eval_on_Z (F := F) Q z := by
  classical
  exact Polynomial.dvd_iff_isRoot.mpr
      (Q_vanishes_on_close_codeword_graph_pg_of_Qdeg
        (F := F) (h_gs := h_gs) hS hQz_ne A hA hk hm hdist hradius hcard)

end Core3Compose

end ArkLib
