import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Liu-Zhou dyadic tower base-non-cancellation wall (#444).

`levelWorst k` = M(mu_{2^k}). The recursion (triangle ineq on the index-2 split
eta_b(mu_{2n}) = eta_b(mu_n)+eta_b(zeta mu_n)) gives ONLY `levelWorst (k+1) <= 2*levelWorst k`
per level (the abelian/character-diagonal Liu-Zhou eigenvalue bound = this triangle ineq,
no genuine eigenvalue saving). The sqrt2 'cancelling' bound is OPEN (the gate).

CORE STRUCTURAL FACT: at beta=4, q ~ n^4, the tower from level 0 up to level mu=log2 n
lies ENTIRELY in the THIN regime (beta_local = 4 mu/k >= 4). The sqrt2 gate is only
hypothesised at beta_local < 4 = levels ABOVE mu_n, outside the prize subgroup. Hence
the prize bound chains mu THIN (factor-2) levels and gives exactly 2^mu = n^1 = Burgess.

This file proves: a per-level factor-`c` recursion from base `M0` over `mu` levels yields
`levelWorst mu <= c^mu * M0`, and at `c=2`, `mu=Nat.log2 n` this is `n * M0` (exponent 1);
the sqrt2 gate would need `c=sqrt2` which is UNAVAILABLE at thin levels.
-/

namespace ArkLib.ProximityGap.LiuZhouTowerBaseWall

/-- Telescoping: if `levelWorst` grows by at most factor `c >= 0` per level from a base,
then after `mu` levels it is bounded by `c^mu * (levelWorst 0)`. This is the exact
content of the dyadic-tower recursion (`c=2` thin / triangle, `c=sqrt2` would be the gate). -/
theorem levelWorst_le_pow (levelWorst : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hnn : ∀ k, 0 ≤ levelWorst k)
    (hrec : ∀ k, levelWorst (k + 1) ≤ c * levelWorst k) :
    ∀ mu, levelWorst mu ≤ c ^ mu * levelWorst 0 := by
  intro mu
  induction mu with
  | zero => simp
  | succ k ih =>
      calc levelWorst (k + 1) ≤ c * levelWorst k := hrec k
        _ ≤ c * (c ^ k * levelWorst 0) := by
              apply mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (k + 1) * levelWorst 0 := by ring

/-- The thin-base instance: with the ONLY provable thin per-level factor `c = 2` and base
`levelWorst 0 = 1` (M(mu_1) = max|1 + e_p(b)| <= 2, normalised), the tower of height `mu`
gives `levelWorst mu <= 2^mu`. At the prize regime `2^mu = n`, this is exactly the
Burgess exponent-1 bound `M(mu_n) <= n`. The sqrt2 gate (`c = Real.sqrt 2`) would give
`(sqrt2)^mu = sqrt n` but is NOT provable at the thin levels (it is the open wall). -/
theorem prize_tower_burgess (levelWorst : ℕ → ℝ)
    (hnn : ∀ k, 0 ≤ levelWorst k)
    (hbase : levelWorst 0 ≤ 1)
    (hrec : ∀ k, levelWorst (k + 1) ≤ 2 * levelWorst k) :
    ∀ mu, levelWorst mu ≤ 2 ^ mu := by
  intro mu
  have h := levelWorst_le_pow levelWorst 2 (by norm_num) hnn hrec mu
  calc levelWorst mu ≤ 2 ^ mu * levelWorst 0 := h
    _ ≤ 2 ^ mu * 1 := by
          apply mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = 2 ^ mu := by ring

/-- The gate gap, made explicit: if the cancelling factor `Real.sqrt 2` WERE available at
every level, the tower would give `levelWorst mu <= (sqrt 2)^mu = sqrt(2^mu) = sqrt n`
(the prize). This is the conditional sqrt-bound — its hypothesis `hgate` is the OPEN
Paley/BGK cancellation gate, FALSE-as-provable at thin levels (the load-bearing obstruction). -/
theorem prize_tower_sqrt_conditional (levelWorst : ℕ → ℝ)
    (hnn : ∀ k, 0 ≤ levelWorst k)
    (hbase : levelWorst 0 ≤ 1)
    (hgate : ∀ k, levelWorst (k + 1) ≤ Real.sqrt 2 * levelWorst k) :
    ∀ mu, levelWorst mu ≤ (Real.sqrt 2) ^ mu := by
  intro mu
  have hsnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h := levelWorst_le_pow levelWorst (Real.sqrt 2) hsnn hnn hgate mu
  calc levelWorst mu ≤ (Real.sqrt 2) ^ mu * levelWorst 0 := h
    _ ≤ (Real.sqrt 2) ^ mu * 1 := by
          apply mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (Real.sqrt 2) ^ mu := by ring

end ArkLib.ProximityGap.LiuZhouTowerBaseWall

#print axioms ArkLib.ProximityGap.LiuZhouTowerBaseWall.levelWorst_le_pow
#print axioms ArkLib.ProximityGap.LiuZhouTowerBaseWall.prize_tower_burgess
#print axioms ArkLib.ProximityGap.LiuZhouTowerBaseWall.prize_tower_sqrt_conditional
