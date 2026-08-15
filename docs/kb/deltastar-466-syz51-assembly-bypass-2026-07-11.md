# δ* #466 — SYZ51 assembly-bypass audit (2026-07-11)

**Verdict: the spread branch does NOT discharge from landed lemmas. `uniformSylvester` is NOT
removable.** The conjectured bypass fails on two independent, in-tree obstructions.

## The audit question

SYZ40–42 assemble the rate-1/2 proximity strip theorem on a master hypothesis whose sole
substantive open field is `uniformSylvester` (SYZ38/39, BGK type), plus `realizabilityCore`
(SYZ42 existence). The merged branch (`m ≤ 3` blocks) is unconditional (SYZ33
`strip_certified_bad_le_budget` ← SYZ32 routing / the "yield law" `∑_{3 cores}(n−sᵢ) ≤ n−1`
for `3s ≥ 2n+1`). The spread branch (`m ≥ 4`) consumes `uniformSylvester` via
generation ⇒ union-rank ⇒ the SYZ21 knapsack.

**Bypass conjecture.** At spread parameters (`m ≥ 4` blocks, each union `U_j > 2n/3`, rate 1/2),
pairwise block intersections are `≥ 2U−n > n/3`. Since `n/3 < k = n/2`, RS-dual distance `k+1`
forces every *pairwise* anchored-dual overlap `finrank(A_i ⊓ A_j) = 0` (SYZ23
`pairwise_direct_of_inter_zero`). Hope: pairwise directness ⇒ joint directness
(`finrank(⨆A_j) = Σ finrank(A_j)`, SYZ23 `finrank_iSup_eq_sum_of_direct`), closing the union
budget with `uniformSylvester` removed; and the block-scale reduced profile `(a,b,c)` lands in
SYZ47's proven unbalanced region `max ≥ ⌊(a+b+c)/2⌋−1` where `ι ≤ 1` is a theorem.

## Obstruction (1): pairwise directness ⇏ generation (the coplanar crack)

SYZ23's sum lower bound (`finrank_iSup_ge_sum_sub_overlaps`) needs every **incremental** overlap
`finrank(A_i ⊓ ⨆_{j<i}A_j)` to vanish — pairwise-zero does **not** imply this for `≥ 3` subspaces.

Decisive in-tree counterexample: the SYZ25 cover `[[0,1,4,5],[0,2,3,5],[1,2,3,4]]` at `k=3` has
**every pairwise intersection exactly `2 = k−1 < k`** (`SYZ51.syz25_pairwise_below_k`) — so all
three pairs are anchored-dual direct, the *exact* bypass premise — **yet the three minimum-weight
dual lines are coplanar and the family fails to generate** (SYZ25 `overbudget_not_imp_generation`,
re-exported `SYZ51.pairwise_direct_but_not_generating`; over-budget `∑(|Cᵢ|−k)=3=|U|−k` but
`d=1`). The coplanar relation is a nonzero constant syzygy = an `ι=2` witness. Not a
small-support artifact: SYZ50 Question C exhibits **357** fresh constant-syzygy witnesses on the
*band-realizable* big-support config `(4,4,4)`, `t=2`, `μ₁₄`. Killing the incremental overlap is
exactly `SylvesterInjective`; pairwise support-disjointness below `k` cannot see it.

## Obstruction (2): block-scale profiles are the BALANCED INTERIOR (SYZ47-blind)

Big symmetric blocks give a balanced pairwise-overlap profile `(d,d,d)`, `max=d ≪ ⌊3d/2⌋−1`, i.e.
`BalancedInterior` (SYZ48) — the 62.3% sub-region SYZ47 does NOT discharge (yields only
`ι ≤ ⌊d/2⌋`). Proven `SYZ51.symmetric_bigblock_balanced_interior` (`d ≥ 4`). The smallest is
exactly SYZ50's `(4,4,4)`, `t=2`, `n=14` band-realizable balanced-interior witness
(`SYZ51.block_scale_profile_in_open_kernel` = SYZ50 `balanced_interior_meets_realizable`).

Probe `scripts/probes/probe_syz51_assembly_bypass.py` (rate-1/2 band-realizable, `k ≤ 40`):
**65 982** balanced-interior profiles vs **4 389** in the proven region; every symmetric `(d,d,d)`
realizable profile is balanced-interior. The block-scale hope lands in the open kernel, not the
proven strip.

## Upgraded hypothesis list (UNCHANGED)

- `uniformSylvester` — SYZ38/39, BGK type. **NOT removable, not reducible to a proven block-scale
  instance.**
- `realizabilityCore` — SYZ42 syndrome-configuration existence.

No BGK-free strip; no unconditional δ*. CORE remains OPEN / ON-BGK. The bypass is closed with a
concrete in-tree counterexample at the exact configuration it proposed.

## Lean deliverables (`Frontier/_SYZ51AssemblyBypass.lean`, axiom-clean)

- `bigblock_pairwise_inter_ge` — `U > 2n/3 ⇒ 2U−n > n/3` (premise satisfiable).
- `syz25_pairwise_below_k` — the SYZ25 cover is pairwise `= k−1 < k`.
- `pairwise_direct_but_not_generating` — pairwise-direct, over-budget, non-generating (Obstruction 1).
- `symmetric_bigblock_balanced_interior` — `(d,d,d)`, `d≥4`, is balanced-interior.
- `block_scale_profile_in_open_kernel` — realizable ∩ balanced-interior nonempty (Obstruction 2).
- `assembly_bypass_fails` — the two obstructions conjoined (the verdict).
