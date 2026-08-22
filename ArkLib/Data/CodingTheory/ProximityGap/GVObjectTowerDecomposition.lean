/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerTowerFactorization
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCurve

/-!
# The tower-level decomposition of the García–Voloch object (#389)

Combining the curve form `r(c) = #{w∈μ_n : (w+1)^n = c^n}` (`repCount_eq_curve`) with the 2-adic
tower factorization (`pow_two_pow_eq_iff`), the García–Voloch object for the 2-power subgroup
`μ_{2^k}` decomposes into tower levels:

> **`repCount_le_tower_levels`** — `r(c) ≤ 1 + ∑_{j<k} L_j(c)`, where
> `L_j(c) = #{w∈μ_{2^k} : (w+1)^{2^j} = −c^{2^j}}` counts the `w` with `(w+1)/c` of order `2^{j+1}`.

Each `L_j` is the common-root count of `X^{2^k}−1` with a degree-`2^j` polynomial — a separate,
lower-degree intersection. This is the structural skeleton for any level-by-level bound on the GV
object (the interior δ\* residual for 2-power NTT domains). Axiom-clean. Issue #389.
-/

open Finset
open ArkLib.ProximityGap.TwoPowerTower

namespace ArkLib.ProximityGap.GVTowerDecomp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The tower-level bound on the GV object.** `r(c) ≤ 1 + ∑_{j<k} #{w∈μ_{2^k} : (w+1)^{2^j} =
−c^{2^j}}`. -/
theorem repCount_le_tower_levels {k : ℕ} {c : F} (hc : c ≠ 0) :
    AdditiveEnergyRepBound.repCount (muN F (2 ^ k)) c
      ≤ 1 + ∑ j ∈ Finset.range k,
          ((muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))).card := by
  classical
  rw [repCount_eq_curve Nat.one_le_two_pow hc]
  have hcongr : (muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ k) = c ^ (2 ^ k))
      = (muN F (2 ^ k)).filter
          (fun w => w + 1 = c ∨ ∃ j ∈ Finset.range k, (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j)) := by
    apply Finset.filter_congr
    intro w _
    exact pow_two_pow_eq_iff (w + 1) c k
  rw [hcongr, Finset.filter_or]
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : ((muN F (2 ^ k)).filter (fun w => w + 1 = c)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have : a + 1 = b + 1 := by rw [ha.2, hb.2]
    exact add_right_cancel this
  have h2 : ((muN F (2 ^ k)).filter
        (fun w => ∃ j ∈ Finset.range k, (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))).card
      ≤ ∑ j ∈ Finset.range k,
          ((muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))).card := by
    have hset : (muN F (2 ^ k)).filter
          (fun w => ∃ j ∈ Finset.range k, (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))
        = (Finset.range k).biUnion
            (fun j => (muN F (2 ^ k)).filter (fun w => (w + 1) ^ (2 ^ j) = -c ^ (2 ^ j))) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      tauto
    rw [hset]
    exact Finset.card_biUnion_le
  omega

end ArkLib.ProximityGap.GVTowerDecomp

#print axioms ArkLib.ProximityGap.GVTowerDecomp.repCount_le_tower_levels
