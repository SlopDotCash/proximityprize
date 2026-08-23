/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBoundaryBound
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryGenericFarExact
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Unconditional δ* up to capacity in the large-field regime (#389)

The universal boundary bound `universal_badSet_card_le` bounds `#badSet ≤ C(n,k+1)` for **every**
stack at **every** radius below capacity (agreement `> k`) — it has no upper bound on the radius,
only the lower one.  Lifted to `ε_mca` and the threshold ledger, this gives an **unconditional**
good-side `δ*` statement that reaches capacity whenever the field is large enough:

* `rsCode_epsMCA_le_uniform` — `ε_mca(rsCode dom k, δ) ≤ C(n,k+1)/|F|` for every `δ` below
  capacity (agreement `> k`), uniformly (no boundary restriction).
* `rsCode_mcaDeltaStar_ge_of_large_field` — if `C(n,k+1) ≤ ε*·|F|` then **every** radius below
  capacity is `mcaDeltaStar`-good: `δ ≤ mcaDeltaStar(rsCode dom k, ε*)`, with NO list-decoding or
  GKL24 residual.

This is the first **unconditional, capacity-reaching** good side for explicit RS, and it pins the
solved/open boundary of the δ* programme exactly: the threshold is at capacity once
`|F| ≥ C(n,k+1)/ε*` (the very-large-field part of the prize regime), and what remains open is
precisely the complementary regime `|F| < C(n,k+1)/ε*` — where the boundary value `C(n,k+1)/|F|`
exceeds `ε*` and the sharper sub-Johnson supply bound (the recognized wall) is needed.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Uniform `ε_mca` bound below capacity.** For every radius with agreement `> k`,
`ε_mca(rsCode dom k, δ) ≤ C(n,k+1)/|F|` — the boundary value, but valid at every radius below
capacity, not just the boundary band. -/
theorem rsCode_epsMCA_le_uniform (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le (F := F) (A := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (n.choose (k + 1))
    (fun u => universal_badSet_card_le dom hk hlo (u 0) (u 1))

/-- **Unconditional δ* reaches capacity in the large-field regime.** If `C(n,k+1) ≤ ε*·|F|`, then
every radius below capacity (agreement `> k`) is `mcaDeltaStar`-good — with NO list-decoding /
GKL24 residual.  Hence `δ* = ` capacity once the field is large enough. -/
theorem rsCode_mcaDeltaStar_ge_of_large_field (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ1 : δ ≤ 1) (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    {εstar : ℝ≥0∞}
    (hε : (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_of_good (F := F) (A := F) _ εstar hδ1
    (le_trans (rsCode_epsMCA_le_uniform dom hk hlo) hε)

/-- **Bad-side complement: δ* drops below capacity once `C(n,k+1) > ε*·|F|`.** At the boundary
radius (under `C(n,k+1)² ≤ |F|`) the bad-scalar sup is *attained*, so `ε_mca = C(n,k+1)/|F|`
exactly (`epsMCA_eq_boundary_choose_of_genericFar`); if that exceeds `ε*`, the boundary radius is
bad and `mcaDeltaStar ≤ δ`.  Together with `rsCode_mcaDeltaStar_ge_of_large_field` this is the
sharp **dichotomy**: for `C(n,k+1)² ≤ |F|`, the threshold reaches capacity *iff* `C(n,k+1) ≤ ε*·|F|`. -/
theorem rsCode_mcaDeltaStar_le_of_boundary_bad (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F)
    {εstar : ℝ≥0∞}
    (hε : εstar < (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ :=
  mcaDeltaStar_le_of_bad (F := F) (A := F) _ εstar
    (by rw [epsMCA_eq_boundary_choose_of_genericFar dom hk hlo hhi hsmall]; exact hε)

/-- **THE BOUNDARY δ\* DICHOTOMY (headline form).** At the boundary radius the MCA value is the
single exact constant `ε_mca = C(n,k+1)/|F|` (`epsMCA_eq_boundary_choose_of_genericFar`, attained
under `C(n,k+1)² ≤ |F|`).  Whether `δ*` reaches the boundary radius is therefore decided entirely
by comparing that one constant to `ε*`:

* `C(n,k+1)/|F| ≤ ε*`  ⟹  the boundary radius is good, so `δ ≤ mcaDeltaStar`;
* `ε* < C(n,k+1)/|F|`  ⟹  the boundary radius is bad, so `mcaDeltaStar ≤ δ`.

Both directions route through the *same* exact equality — the boundary radius is the exact pivot,
and `ε* ⋚ C(n,k+1)/|F|` is the whole story.  Unconditional; no sum-product / GKL24 residual. -/
theorem rsCode_boundary_deltaStar_dichotomy (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ1 : δ ≤ 1)
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hsmall : (n.choose (k + 1)) ^ 2 ≤ Fintype.card F)
    (εstar : ℝ≥0∞) :
    ((n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar →
        δ ≤ mcaDeltaStar (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar)
    ∧ (εstar < (n.choose (k + 1) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) →
        mcaDeltaStar (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ) := by
  have hEq := epsMCA_eq_boundary_choose_of_genericFar dom hk hlo hhi hsmall
  refine ⟨fun hle => le_mcaDeltaStar_of_good (F := F) (A := F) _ εstar hδ1 ?_,
          fun hlt => mcaDeltaStar_le_of_bad (F := F) (A := F) _ εstar ?_⟩
  · rw [hEq]; exact hle
  · rw [hEq]; exact hlt

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_epsMCA_le_uniform
#print axioms ProximityGap.Ownership.rsCode_mcaDeltaStar_ge_of_large_field
#print axioms ProximityGap.Ownership.rsCode_mcaDeltaStar_le_of_boundary_bad
#print axioms ProximityGap.Ownership.rsCode_boundary_deltaStar_dichotomy
