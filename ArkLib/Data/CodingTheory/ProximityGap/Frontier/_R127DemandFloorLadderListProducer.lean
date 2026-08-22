/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R125DemandFloorMaximalOrbitProducer
import ArkLib.Data.CodingTheory.ProximityGap.LadderListCliffGeneral

/-!
# Ladder-list route to the maximal demand-tail producer

R125 reduces the deep demand tail to the pointwise allowance

`Bad r (4g) ≤ (4g) * C(2g,r-1) + 1`.

The general ladder-cliff theorem proves that a production-field ladder list has cardinality
bounded by `C(n/2,r-1)` after multiplying by `r`.  This file records the exact adapter from
that theorem to the R125 allowance when `n = 4g`.  The remaining mathematical wall is then a
clean word-domination statement: the relevant bad family must be pointwise majorized by the
ladder list count.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer

open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer
open ProximityGap.LadderList
open ProximityGap.SpikeFloor ProximityGap.LadderListModP

variable {p n ν r k g : ℕ} [Fact p.Prime] {root lam : ZMod p}
variable {dom : Fin n ↪ ZMod p}

/-- The production-field ladder list count appearing in `ladder_list_card_mul_le`. -/
noncomputable def ladderListCount
    (p n r k : ℕ) [Fact p.Prime] (lam : ZMod p) (dom : Fin n ↪ ZMod p) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Fin n → ZMod p)).filter
      (fun c => c ∈ (rsCode dom k : Submodule (ZMod p) (Fin n → ZMod p)) ∧
        2 * r ≤ (Finset.univ.filter
          (fun i => c i = ladderWord dom r lam i)).card)).card

/-- The ladder-cliff theorem bounds the ladder list by the maximal R125 binomial cap. -/
theorem ladder_list_count_le_maximalTailOP
    (hn4 : n = 4 * g)
    (hr : 1 ≤ r)
    (hν : 1 ≤ ν)
    (hroot : IsPrimitiveRoot root (2 ^ ν))
    (hn : n = 2 ^ ν)
    (hdomain : ∀ i, (dom i) ^ n = 1)
    (hk1 : 1 ≤ k)
    (hk2 : k ≤ 2 * r - 2)
    (hk3 : 2 * r - 3 ≤ k)
    (hp : (2 * r) ^ 2 ^ (ν - 1) < p) :
    ladderListCount p n r k lam dom ≤ maximalTailOP g r := by
  have hmul :
      r * ladderListCount p n r k lam dom ≤ (n / 2).choose (r - 1) := by
    simpa [ladderListCount] using
      (ladder_list_card_mul_le (p := p) (n := n) (ν := ν) (r := r) (k := k)
        (g := root) (lam := lam) (dom := dom) hr hν hroot hn hdomain hk1 hk2 hk3 hp)
  have hself : ladderListCount p n r k lam dom ≤
      r * ladderListCount p n r k lam dom := by
    calc
      ladderListCount p n r k lam dom = 1 * ladderListCount p n r k lam dom := by
        rw [one_mul]
      _ ≤ r * ladderListCount p n r k lam dom := by
        exact Nat.mul_le_mul_right _ hr
  have hhalf : n / 2 = 2 * g := by
    rw [hn4]
    omega
  calc
    ladderListCount p n r k lam dom ≤ r * ladderListCount p n r k lam dom := hself
    _ ≤ (n / 2).choose (r - 1) := hmul
    _ = maximalTailOP g r := by
      rw [hhalf, maximalTailOP]

/--
If a bad-count family is pointwise controlled by the corresponding ladder list count, then the
R125 maximal-binomial allowance follows at that `(g,r)`.
-/
theorem bad_le_maximal_allowance_of_ladder_list_majorant
    (Bad : ℕ → ℕ → ℕ)
    (hn4 : n = 4 * g)
    (hr : 1 ≤ r)
    (hν : 1 ≤ ν)
    (hroot : IsPrimitiveRoot root (2 ^ ν))
    (hn : n = 2 ^ ν)
    (hdomain : ∀ i, (dom i) ^ n = 1)
    (hk1 : 1 ≤ k)
    (hk2 : k ≤ 2 * r - 2)
    (hk3 : 2 * r - 3 ≤ k)
    (hp : (2 * r) ^ 2 ^ (ν - 1) < p)
    (hBad : Bad r (4 * g) ≤ (4 * g) * ladderListCount p n r k lam dom + 1) :
    Bad r (4 * g) ≤ (4 * g) * maximalTailOP g r + 1 := by
  have hcount : ladderListCount p n r k lam dom ≤ maximalTailOP g r :=
    ladder_list_count_le_maximalTailOP (p := p) (n := n) (ν := ν) (r := r) (k := k)
      (g := g) (root := root) (lam := lam) (dom := dom)
      hn4 hr hν hroot hn hdomain hk1 hk2 hk3 hp
  exact hBad.trans (by gcongr)

end ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer.ladderListCount
#print axioms
  ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer.ladder_list_count_le_maximalTailOP
#print axioms
  ArkLib.ProximityGap.Frontier.R127DemandFloorLadderListProducer.bad_le_maximal_allowance_of_ladder_list_majorant
