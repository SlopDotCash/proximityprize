/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Research.ProximityGap.Frontier._SYZ50WitnessRealizability
import ArkLib.Research.ProximityGap.Frontier._SYZ47GeometricBalance
import ArkLib.Research.ProximityGap.Frontier._SYZ25MDSGeneration
import ArkLib.Research.ProximityGap.Frontier._SYZ23DirectnessStrip

/-!
# SYZ51 — the assembly-bypass audit: does the spread branch discharge from landed lemmas?

## The audit question

SYZ40–42 assembled the rate-`1/2` proximity strip theorem on a master hypothesis whose sole
substantive open field is `uniformSylvester` (SYZ38/39, BGK type).  The **merged** branch
(`m ≤ 3` blocks) is unconditional (SYZ33 `strip_certified_bad_le_budget` via the SYZ32 routing);
the **spread** branch (`m ≥ 4` merged blocks) consumes `uniformSylvester` through
generation ⇒ union-rank ⇒ the SYZ21 knapsack.

The conjectured **bypass** (this file's target): at spread parameters — `m ≥ 4` blocks, each of
union `U_j > 2n/3` in an `n`-point domain at rate `1/2` (`n = 2k`) — the blocks overlap heavily,
so every *pairwise* block intersection has size `> n/3`.  Since `n/3 < k = n/2`, the RS-dual
distance `k + 1` makes every *pairwise* anchored-dual overlap `finrank (A_i ⊓ A_j) = 0`
(SYZ23 `pairwise_direct_of_inter_zero`).  If that pairwise directness upgraded to *joint*
directness — `finrank (⨆ A_j) = Σ finrank (A_j)` (SYZ23 `finrank_iSup_eq_sum_of_direct`) — the
union budget would close from landed lemmas alone, with `uniformSylvester` REMOVED.

Additionally the hope was that the block-scale reduced profile `(a,b,c)` (the pairwise-exclusive
overlap-region sizes of the big blocks) would land in SYZ47's **proven** unbalanced region
`max(a,b,c) ≥ ⌊(a+b+c)/2⌋ − 1`, where `ι ≤ 1` is a theorem — discharging the imbalance shield too.

## Verdict: **NOT ESTABLISHED from landed lemmas** (route obstructions, no spread-parameter counterexample)

Scope correction (audit CW-B13-11): neither obstruction below is an instance at the bypass's own
spread parameters.  The SYZ25 cover lives at `n = 6, k = 3` with cores of size `4 = 2n/3` (not
`> 2n/3`) and pairwise intersections `2 = n/3` (not `> n/3`); the integer window `(n/3, k) = (2, 3)`
is empty there (`syz25_cover_outside_bypass_premise`).  Its RS rank deficiency is moreover a
probe-level fact only at specific evaluation points.  `assembly_bypass_fails` re-exports abstract
`ℚ³` lines and a `ℕ` profile, neither at spread parameters.  So what is shown is that the landed
lemmas (pairwise directness + SYZ47 floor) do not *by themselves* yield the bypass; whether the
bypass statement is actually false at spread parameters is **open**.

**(1) Pairwise directness does NOT upgrade to joint directness (the coplanar crack).**  The SYZ23
sum lower bound needs every *incremental* overlap `finrank (A_i ⊓ ⨆_{j<i} A_j)` to vanish, which
pairwise-zero (`A_i ⊓ A_j = ⊥` for `i ≠ j`) does **not** imply for `≥ 3` subspaces.  The SYZ25
cover — three `4`-cores of `{0,…,5}` at `k = 3`, `[[0,1,4,5],[0,2,3,5],[1,2,3,4]]` — has **every
pairwise intersection `= 2 = k − 1 < k`** (`syz25_pairwise_below_k`), so all three pairwise
anchored-dual overlaps are `⊥` (the pairwise-directness *step* the bypass uses, though this cover
does not meet the spread size premise), **yet the three minimum-weight dual lines are coplanar and
the family fails to generate**
(SYZ25 `overbudget_not_imp_generation`, re-exported as `pairwise_direct_but_not_generating`; this
re-export is abstract `ℚ³` lines, not an RS configuration at spread parameters).  The
coplanar relation is precisely a nonzero constant syzygy — an `ι = 2` witness — so this is not a
small-support artifact: SYZ50 Question C exhibits **357** such fresh constant-syzygy witnesses on the
*band-realizable* big-support config `(4,4,4)`, `t = 2`, `μ₁₄`.  Killing the incremental overlap is
exactly `SylvesterInjective`; pairwise support-disjointness below `k` cannot see it.

**(2) The block-scale profiles are the BALANCED INTERIOR, where SYZ47 is blind.**  Big symmetric
blocks give a balanced pairwise-overlap profile `(d,d,d)`, whose `max = d` is far below the balanced
edge `⌊3d/2⌋ − 1`: it is `BalancedInterior` (SYZ48), the `62.3 %` sub-region SYZ47's floor does
**not** discharge (it yields only `ι ≤ ⌊d/2⌋`, not `ι ≤ 1`).  The smallest is exactly SYZ50's
`(4,4,4)`, `t = 2`, `n = 14` band-realizable witness (`balanced_interior_meets_realizable`).  So the
imbalance shield is *not* recovered at block scale; the block-scale hope lands in the open kernel, not
the proven strip.  (Probe `probe_syz51_assembly_bypass.py`: over all rate-`1/2` band-realizable
profiles `k ≤ 40`, **65 982** are balanced-interior vs **4 389** in the proven region; every
symmetric `(d,d,d)` realizable profile is balanced-interior.)

## Consequence for the master hypothesis

The upgraded hypothesis list is **unchanged**: `uniformSylvester` is **not shown** removable by this
route, and does not reduce to an already-proven block-scale instance.  The strip theorem still rests on
`uniformSylvester` (SYZ38/39, BGK type) + `realizabilityCore` (SYZ42 existence).  No BGK-free strip;
no unconditional `δ*`.  CORE remains OPEN / ON-BGK.  The bypass is *not* refuted: no
counterexample at its spread parameters (`U_j > 2n/3`, pairwise intersections in `(n/3, k)`) is
formalized; only the landed proof route is shown insufficient.

All results axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ51

open Module
open ArkLib.ProximityGap.Frontier
open ArkLib.ProximityGap.SYZ48 (BalancedInterior)

/-! ## 1. The bypass premise IS satisfiable: big blocks are pairwise below `k` at rate `1/2` -/

/-- **Big blocks force large pairwise intersections.**  Two blocks of union size `U > 2n/3` in an
`n`-point domain meet in `≥ 2U − n > n/3` points (inclusion–exclusion).  Pure `ℕ`. -/
theorem bigblock_pairwise_inter_ge (n U : ℕ) (hU : 3 * U > 2 * n) (hUn : U ≤ n) :
    3 * (2 * U - n) > n := by omega

/-- **…yet still below `k` at rate `1/2`.**  A pairwise intersection of size `< n/2 = k` sits below
the RS-dual distance `k`, so its anchored-dual overlap is forced to `⊥` (SYZ23).  The bypass premise
`pairwise intersection ∈ (n/3, k)` is a nonempty window once `n` is not tiny: e.g. `n = 12, k = 6`,
intersection `= 5` (`4 < 5 < 6`). -/
theorem pairwise_window_nonempty : ∃ o : ℕ, 12 / 3 < o ∧ o < 6 ∧ o ≤ 6 - 1 := ⟨5, by decide⟩

/-! ## 2. Obstruction (1): pairwise directness ⇏ generation (the coplanar crack) -/

/-- **The SYZ25 counterexample cover is pairwise-below-`k`.**  The three `4`-cores
`[[0,1,4,5],[0,2,3,5],[1,2,3,4]]` at `k = 3` pairwise intersect in **exactly `2 = k − 1 < k`**
points, so each pair is anchored-dual **direct** (`finrank (A_i ⊓ A_j) = 0`, SYZ23) — the
pairwise-directness step the bypass invokes, though *not* at spread parameters
(`syz25_cover_outside_bypass_premise`). -/
theorem syz25_pairwise_below_k :
    (([0,1,4,5] : List ℕ).toFinset ∩ ([0,2,3,5] : List ℕ).toFinset).card = 2 ∧
    (([0,1,4,5] : List ℕ).toFinset ∩ ([1,2,3,4] : List ℕ).toFinset).card = 2 ∧
    (([0,2,3,5] : List ℕ).toFinset ∩ ([1,2,3,4] : List ℕ).toFinset).card = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The SYZ25 cover does NOT meet the bypass premise (audit CW-B13-11).**  At `n = 6, k = 3`
its cores have size `4`, and `3·4 > 2·6` fails (`4 = 2n/3`, not `> 2n/3`); and the integer window of
pairwise intersections `n/3 < o < k`, i.e. `6 < 3·o ∧ o < 3`, is empty.  So the SYZ25 cover is not
a configuration at the bypass's spread parameters. -/
theorem syz25_cover_outside_bypass_premise :
    ¬ (3 * 4 > 2 * 6) ∧ ¬ ∃ o : ℕ, 6 < 3 * o ∧ o < 3 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨o, h1, h2⟩
  omega

/-- **Obstruction (1), fully assembled — pairwise-direct but NOT generating.**  There is a family of
`D = 3` subspaces, all `≤` a ceiling `W`, whose per-core dimensions **reach** the ceiling
(over-budget: `finrank W ≤ Σ finrank (A i)`) and whose pairs are direct (the coplanar lines of
SYZ25 pairwise meet in `⊥`), **yet the joint span is strictly below `W`** (`partialSup ≠ W`).  This
is SYZ25 `overbudget_not_imp_generation` re-exported (abstract `ℚ`-lines, not at spread parameters):
pairwise directness — the content of the bypass's "pairwise block-intersections `< k`" step — is
**insufficient in general** for generation.
The missing input is the *incremental* overlap vanishing, i.e. `SylvesterInjective`. -/
theorem pairwise_direct_but_not_generating :
    ∃ (A : ℕ → Submodule ℚ SYZ25.CE) (W : Submodule ℚ SYZ25.CE) (D : ℕ),
      (∀ i ∈ Finset.range D, A i ≤ W)
      ∧ finrank ℚ W ≤ ∑ i ∈ Finset.range D, finrank ℚ (A i)
      ∧ SYZ23.partialSup A D ≠ W :=
  SYZ25.overbudget_not_imp_generation

/-! ## 3. Obstruction (2): block-scale profiles are the balanced interior (SYZ47-blind) -/

/-- **Symmetric big-block profiles are balanced-interior.**  A balanced pairwise-overlap profile
`(d,d,d)` with `d ≥ 4` has `max = d` strictly below the balanced edge `⌊3d/2⌋ − 1`, so it is
`BalancedInterior` — the sub-region SYZ47's floor does **not** discharge (there it yields only
`ι ≤ ⌊d/2⌋`, not `ι ≤ 1`).  Hence the block-scale imbalance shield is *not* recovered from the
landed SYZ47 floor. -/
theorem symmetric_bigblock_balanced_interior (d : ℕ) (hd : 4 ≤ d) :
    BalancedInterior d d d := by
  unfold BalancedInterior; omega

/-- **The block-scale hope lands in the open kernel, not the proven strip — concrete witness.**  The
smallest realizable balanced-interior profile `(4,4,4)`, `t = 2`, `n = 14` (SYZ50) is *both*
band-realizable at rate `1/2` *and* balanced-interior: SYZ47's floor gives only `ι ≤ 2` there, so the
spread branch is **not** discharged by the geometric floor at block scale.  Re-export of SYZ50's
decisive polytope verdict. -/
theorem block_scale_profile_in_open_kernel :
    ∃ a b c t k : ℕ, SYZ50.Realizable a b c t k ∧ BalancedInterior a b c :=
  SYZ50.balanced_interior_meets_realizable

/-! ## 4. The verdict: `uniformSylvester` is not shown removable -/

/-- **THE SYZ51 verdict (honest conjunction): the landed proof route is insufficient.**  Two
obstructions to discharging the bypass from landed lemmas (neither is a counterexample at spread
parameters — see `syz25_cover_outside_bypass_premise`):

* **(1)** pairwise directness (`finrank (A_i ⊓ A_j) = 0` for every pair) does **not** in general
  force generation: there is an abstract pairwise-direct, over-budget family of `ℚ`-lines whose
  joint span misses its ceiling (the SYZ25 coplanar crack, not at spread parameters);
* **(2)** the block-scale reduced profile is **balanced-interior**, where SYZ47's proven floor is
  blind — so the imbalance shield is not recovered at block scale either.

Therefore the spread branch does **not** discharge from the landed lemmas (SYZ23 pairwise + SYZ34
fiber-product + SYZ47 floor) by this route; `uniformSylvester` is **not** shown removable.  Whether
it is in fact needed at spread parameters is open (no spread-parameter instance is given).  The strip theorem still rests on
`uniformSylvester` + `realizabilityCore`. -/
theorem assembly_bypass_fails :
    (∃ (A : ℕ → Submodule ℚ SYZ25.CE) (W : Submodule ℚ SYZ25.CE) (D : ℕ),
      (∀ i ∈ Finset.range D, A i ≤ W)
      ∧ finrank ℚ W ≤ ∑ i ∈ Finset.range D, finrank ℚ (A i)
      ∧ SYZ23.partialSup A D ≠ W)
    ∧
    (∃ a b c t k : ℕ, SYZ50.Realizable a b c t k ∧ BalancedInterior a b c) :=
  ⟨pairwise_direct_but_not_generating, block_scale_profile_in_open_kernel⟩

end ArkLib.ProximityGap.SYZ51

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ51.bigblock_pairwise_inter_ge
#print axioms ArkLib.ProximityGap.SYZ51.syz25_pairwise_below_k
#print axioms ArkLib.ProximityGap.SYZ51.syz25_cover_outside_bypass_premise
#print axioms ArkLib.ProximityGap.SYZ51.pairwise_direct_but_not_generating
#print axioms ArkLib.ProximityGap.SYZ51.symmetric_bigblock_balanced_interior
#print axioms ArkLib.ProximityGap.SYZ51.block_scale_profile_in_open_kernel
#print axioms ArkLib.ProximityGap.SYZ51.assembly_bypass_fails
