/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TowerMomentBridge
import ArkLib.Data.CodingTheory.ProximityGap.EvenTowerSupplyGrowth
import ArkLib.Data.CodingTheory.ProximityGap.CubicCosetSupplyGrowth

/-!
# A lower bound on the supply residual, forced by tower words (#389)

`ExplainableCoreSupply dom k m B` (the named open residual) asserts every word admits at most `B`
explainable `(k+m+1)`-cores.  The bold pinning hypothesis needs `B` to be *polynomial* in `n`.
This file shows the residual is **forced from below** by the explicit tower words: any valid `B`
must dominate the tower-word zero-sum count, which the even-tower growth bound makes at least
`C(|R|, (k+1)/2)` for odd `k` (the cubic-coset bound covers `k = 2`).  How fast that grows
depends on how `k` scales with `n`:

* **fixed dimension** (`k` constant as `n → ∞`): `C(|R|, j)` with `j = (k+1)/2` fixed is
  `Θ(n^j)`, a polynomial lower bound — consistent with a polynomial-supply picture;
* **fixed rate** (`k ≈ ρ n`): then `j = (k+1)/2` grows linearly in `n`, and `C(n/2, j)` is
  **exponential** in `n` for `j` an interior fraction of `n/2`.  So at constant rate this lower
  bound already rules out any polynomial `B`; `DeepBandSupplyExponential` proves this obstruction
  for `μ_n` at rate `→ 1/2`.

An exponent depending on `n` (`n^{(k+1)/2}` with `k ∝ n`) is not a uniform polynomial bound, so
this file is a polynomial lower constraint only in the fixed-dimension regime.

* **`supply_ge_towerZeroSum`** — any deep-band supply bound `B` (i.e. `ExplainableCoreSupply
  dom k 0 B`) dominates the zero-sum-`(k+1)`-subset count of the domain (instantiate the residual
  at the tower word `x^{k+1}`, then `tower_degenerateSets_eq`).
* **`evenSupply_ge_choose`** — on a negation-closed domain, the supply bound at code dimension
  `2j−1` is `≥ C(|R|, j)` (the antipodal growth lower bound): `Θ(n^j)` for fixed `j`, exponential
  in `n` when `j` grows proportionally to `n`.
* **`cubicSupply_forces_ge`** — on a cube-closed domain, the supply bound at code dimension `2`
  is `≥ |R|` (`= n/3` when `R` is a full set of coset representatives; the multiplicative-coset
  lower bound).

Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The supply residual dominates the tower zero-sum count.**  If every word admits at most `B`
explainable `(k+1)`-cores, then in particular the tower word `x^{k+1}` does — and its explainable
`(k+1)`-cores are exactly the zero-sum `(k+1)`-subsets. -/
theorem supply_ge_towerZeroSum (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {B : ℕ}
    (hsupply : ExplainableCoreSupply dom k 0 B) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
        (fun S => ∑ i ∈ S, dom i = 0)).card ≤ B := by
  have h := hsupply (fun i => (dom i) ^ (k + 1))
  rw [← tower_degenerateSets_eq dom hk]
  exact h

open Classical in
/-- **Even-tower forcing.**  On a negation-closed domain, the supply bound at code dimension
`2j−1` is at least `C(|R|, j)` — `Θ(n^j)` for fixed `j`, but exponential in `n` when `j` is a
fixed fraction of `|R|` (constant rate). -/
theorem evenSupply_ge_choose (dom : Fin n ↪ F) (ν : Fin n → Fin n) (R : Finset (Fin n))
    (j : ℕ) (hj : 1 ≤ j) {B : ℕ} (hν : ∀ i ∈ R, dom (ν i) = - dom i)
    (hνR : ∀ i ∈ R, ν i ∉ R) (hsupply : ExplainableCoreSupply dom (2 * j - 1) 0 B) :
    (R.card).choose j ≤ B := by
  have h1 := supply_ge_towerZeroSum dom (by omega : 1 ≤ 2 * j - 1) hsupply
  rw [show 2 * j - 1 + 1 = 2 * j from by omega] at h1
  exact le_trans (zeroSum_evenSubsets_antipodal_ge dom ν R j hν hνR) h1

open Classical in
/-- **Cubic forcing.**  On a cube-closed domain (`3 ∣ n`), the supply bound at code dimension `2`
is at least `|R|` (`= n/3` for a full set of coset representatives). -/
theorem cubicSupply_forces_ge (dom : Fin n ↪ F) (τ : Fin n → Fin n) (ζ : F)
    (R : Finset (Fin n)) (hζ : 1 + ζ + ζ ^ 2 = 0) (hζ1 : ζ ≠ 1)
    (hτ : ∀ i, dom (τ i) = ζ * dom i) (h0 : ∀ i ∈ R, dom i ≠ 0)
    (hτR : ∀ i ∈ R, τ i ∉ R ∧ τ (τ i) ∉ R) {B : ℕ}
    (hsupply : ExplainableCoreSupply dom 2 0 B) :
    R.card ≤ B :=
  le_trans (zeroSum_triples_coset_ge dom τ ζ R hζ hζ1 hτ h0 hτR)
    (supply_ge_towerZeroSum dom (by norm_num : 1 ≤ 2) hsupply)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.supply_ge_towerZeroSum
#print axioms ProximityGap.PairRank.evenSupply_ge_choose
#print axioms ProximityGap.PairRank.cubicSupply_forces_ge
