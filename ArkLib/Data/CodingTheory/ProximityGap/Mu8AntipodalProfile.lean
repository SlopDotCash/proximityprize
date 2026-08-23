/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity

/-!
# The complete tower-supply profile of the FRI domain `μ_8 ⊂ F₁₇` (#389)

A machine-checked confirmation, at the prize-relevant 2-power domain `μ_8 = ⟨2⟩ ⊂ F₁₇`, of the
antipodal-exactness prediction for 2-power subgroups (the combinatorial heart of the
even-moment / Lam–Leung structure: above the coincidence threshold, the zero-sum-`2r`-subset
counts of `μ_{2^k}` are exactly the antipodal binomials `C(n/2, r)`, and all odd-size counts
vanish).  `μ_8` is coincidence-free, so its full profile is *exactly* the binomial row:

| `2r`-subset size | 0 | 2 | 4 | 6 | 8 |
|---|---|---|---|---|---|
| zero-sum count | `1` | `4` | `6` | `4` | `1` |
| `= C(4, r)` | ✓ | ✓ | ✓ | ✓ | ✓ |

and the odd-size zero-sum counts are all `0`.  Via the orchard identity this is the **exact
deep-band supply** of every tower word on `μ_8`:

* `x²` supply `= 4`, `x⁴` supply `= 6`, `x⁶` supply `= 4` (the even tower, `= C(4, r)`);
* `x³` supply `= 0`, `x⁵` supply `= 0` (the odd tower — no cube/odd roots in a 2-power group).

So on the FRI domain the tower-word supply is pinned *exactly*, not just bounded — the antipodal
lower bound `coset_union_growth` is tight here, with no characteristic-`17` slack.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

section FRIProfile

local instance factP17Profile : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `μ_8 = ⟨2⟩ ⊂ F₁₇`, the 2-power FRI domain (antipodal pairs `(1,16),(2,15),(4,13),(8,9)`). -/
def friMu8vals : Fin 8 → ZMod 17 := ![1, 2, 4, 8, 16, 15, 13, 9]

/-- The FRI domain `μ_8 ⊂ F₁₇` as an embedding (injective by `decide`). -/
def friMu8 : Fin 8 ↪ ZMod 17 := ⟨friMu8vals, by decide⟩

/-! ### The even profile: zero-sum `2r`-subset counts `= C(4, r)` -/

/-- Zero-sum `2`-subsets: `4 = C(4,1)` (the four antipodal pairs). -/
theorem mu8_zeroSum_pairs :
    (((Finset.univ : Finset (Fin 8)).powersetCard 2).filter
        (fun T => ∑ i ∈ T, friMu8 i = 0)).card = 4 := by decide

set_option maxHeartbeats 4000000 in
/-- Zero-sum `4`-subsets: `6 = C(4,2)` (pairs of antipodal pairs). -/
theorem mu8_zeroSum_quads :
    (((Finset.univ : Finset (Fin 8)).powersetCard 4).filter
        (fun T => ∑ i ∈ T, friMu8 i = 0)).card = 6 := by decide

set_option maxHeartbeats 4000000 in
/-- Zero-sum `6`-subsets: `4 = C(4,3)` (triples of antipodal pairs). -/
theorem mu8_zeroSum_sextics :
    (((Finset.univ : Finset (Fin 8)).powersetCard 6).filter
        (fun T => ∑ i ∈ T, friMu8 i = 0)).card = 4 := by decide

/-! ### The odd profile: all odd-size zero-sum counts vanish -/

/-- Zero-sum `3`-subsets: `0` (no cube/odd-root structure in a 2-power group). -/
theorem mu8_zeroSum_triples :
    (((Finset.univ : Finset (Fin 8)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, friMu8 i = 0)).card = 0 := by decide

set_option maxHeartbeats 4000000 in
/-- Zero-sum `5`-subsets: `0`. -/
theorem mu8_zeroSum_quintics :
    (((Finset.univ : Finset (Fin 8)).powersetCard 5).filter
        (fun T => ∑ i ∈ T, friMu8 i = 0)).card = 0 := by decide

/-! ### The exact tower supplies on `μ_8` (via the orchard identity) -/

open Classical in
/-- **Exact `x²` supply `= 4 = C(4,1)`.** -/
theorem friSupply_sq_eq_four :
    ((Finset.univ.filter (fun c =>
        c ∈ (rsCode friMu8 1 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 1 + 1 ≤ (agreeSet c (fun i => (friMu8 i) ^ (1 + 1))).card)).card) = 4 := by
  rw [general_orchard_card friMu8 (by norm_num : (1 : ℕ) ≤ 1)]; exact mu8_zeroSum_pairs

open Classical in
/-- **Exact `x⁴` supply `= 6 = C(4,2)`.** -/
theorem friSupply_quartic_eq_six :
    ((Finset.univ.filter (fun c =>
        c ∈ (rsCode friMu8 3 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 3 + 1 ≤ (agreeSet c (fun i => (friMu8 i) ^ (3 + 1))).card)).card) = 6 := by
  rw [general_orchard_card friMu8 (by norm_num : (1 : ℕ) ≤ 3)]; exact mu8_zeroSum_quads

open Classical in
/-- **Exact `x⁶` supply `= 4 = C(4,3)`.** -/
theorem friSupply_sextic_eq_four :
    ((Finset.univ.filter (fun c =>
        c ∈ (rsCode friMu8 5 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 5 + 1 ≤ (agreeSet c (fun i => (friMu8 i) ^ (5 + 1))).card)).card) = 4 := by
  rw [general_orchard_card friMu8 (by norm_num : (1 : ℕ) ≤ 5)]; exact mu8_zeroSum_sextics

open Classical in
/-- **Exact `x³` supply `= 0`** — the odd tower vanishes on a 2-power group. -/
theorem friSupply_cubic_eq_zero :
    ((Finset.univ.filter (fun c =>
        c ∈ (rsCode friMu8 2 : Submodule (ZMod 17) (Fin 8 → ZMod 17))
          ∧ 2 + 1 ≤ (agreeSet c (fun i => (friMu8 i) ^ (2 + 1))).card)).card) = 0 := by
  rw [general_orchard_card friMu8 (by norm_num : (1 : ℕ) ≤ 2)]; exact mu8_zeroSum_triples

end FRIProfile

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.friSupply_sq_eq_four
#print axioms ProximityGap.PairRank.friSupply_quartic_eq_six
#print axioms ProximityGap.PairRank.friSupply_sextic_eq_four
#print axioms ProximityGap.PairRank.friSupply_cubic_eq_zero
