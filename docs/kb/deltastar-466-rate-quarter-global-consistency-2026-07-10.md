# Rate-quarter predecessor: the global `u₁`-consistency charge — the heavy window is CLOSED, the realized geometry is sterile, and the residual is a swarm recursion

## Status

Successor of the two-cover-window realization.  Answers the population question
("can the realized three-pencil geometry actually CARRY bad scalars?") and, in
doing so, discovers a **new counting surface** that closes the heavy
three-pencil over-budget which `counting_admits_three_heavy_overBudget` had
shown un-excludable by the per-pencil ledger.

Formal kernel (pg-iterate ✅ OK 18s, 8 audited theorems, all on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterGlobalConsistencyCharge.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_global_consistency.py`
(μ_256/F_257 vote-pool lemma checks: 0 violations over 200 instances; n=16
exhaustive bad-counts with the joint-explanation filter).

## 1. The exact obstruction

Fix stack `(u₀,u₁)`, base scalar `γ₀`, base witness `p₀`.  Every pencil through
the base satisfies `w₀ + γ₀·w₁ = p₀`.  Define the **single global function**

```text
D := p₀ − u₀ − γ₀·u₁
```

Two exact facts (`alignedSet_subset_Dzero`, `voteSet_subset_Dsupport`):

* `aligned_j = {D = 0} ∩ {w₁ⱼ = u₁}` — all aligned regions sink into `{D=0}`;
* every rider vote (γ ≠ γ₀, any pencil) lies in `{D ≠ 0}`: the vote equation
  is `D(i) + (γ−γ₀)·(w₁(i)−u₁(i)) = 0`, so `D(i) = 0` forces alignment.

Hence ALL pencils through one base share ONE vote pool
`F = N − |{D=0}|` (`riders_mul_le_Dsupport`: `riders·(T−A) ≤ F` per pencil),
while their aligned regions jointly inflate `|{D=0}|`.  This coupling is the
"riders on different pencils constrain `u₁` on overlapping coordinates" effect,
in closed form: dense alignment and dense rider population compete for the
same coordinates through `D`.

## 2. The heavy window is CLOSED

`three_heavy_riders_budget`: three pairwise-distinct pencils through one base
with aligned regions of the window size `T−1` (pairwise `< k` from the in-tree
`alignedSet_inter_card_lt_k`):

```text
|{D=0}| ≥ 3(T−1) − 3(k−1) = 973078530   ⟹   F ≤ 100663294
riders total ≤ 3F = 301989882   ⟹   #bad ≤ 301989883 ≤ N   (3.55× below budget)
```

So the configuration the layer-cake proved un-excludable by the per-pencil
surface is excluded by the global charge.  The same computation kills J=4
heavies even harder (union forces `F ≤ ~3.0e7`).

## 3. The realized geometry is sterile

`base_row_stack_carries_no_riders`: the two-cover realization used
`u₀ = base codeword` (`γ₀ = 0`, `p₀ = u₀`), giving `D ≡ 0` — the pool is
EMPTY and every sub-threshold pencil carries zero riders.  Probe (n=16
exhaustive with joint-explanation filter): `#bad = 1` (the base scalar alone);
adversarial `D`-stacks over 40 trials reached `#bad = 2` of `n = 16`.
**Geometric realizability ≠ population realizability**, now formally
separated: the gap between them is exactly where the predecessor pin lives.

## 4. The new minimal open statement: sub-Johnson swarm recursion

With the heavy pool `F ≤ 100663294`, every pencil below alignment
`T − F = 492131671` is sterile (a rider needs `T−A ≤ F` votes).  The escaping
families are pencils at alignment in `[T−F, ⌊√(N(k−1))⌋ = 536870910]` —
below Johnson, hence uncounted — with ≤ ~2 riders each and unbounded count.
Their structure is FORCED: a single-rider pencil for rider `γ` must satisfy
`w₁ = u₁ − D/(γ−γ₀)` on ALL of `{D≠0}`, and since `F < k = 2^28` any values on
the pool are interpolable (at n=16 the probe shows the opposite regime,
`f = 7 > k = 4`: 0/16 scalars interpolable).  So the swarm is an **affine
pencil of stacks** `s ↦ u₁ − s·D`: one correlated-agreement instance at
shrunken parameters `N' = N − F`, `T' = T − F`, same `k` — and
`T−F = 492131671 < √((N−F)(k−1)) ≈ 5.11e8`: again just below the Johnson
radius of the shrunken problem.  Named residual:
`GlobalConsistencySwarmResidual`.  The recursion suggests a derecursion
attack (iterate the charge on the shrunken instance) as the natural next
lane; alternatively the structured-floor route stands.

## 5. Honesty

* The closure is per-base-scalar and at the window alignment `= T−1`; the
  general mixed ledger (heavies + swarm) is NOT assembled into `#bad ≤ N` —
  that is exactly the named residual.
* Nothing here changes the operational bracket
  `3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30)`.

## 6. Theorems (all axiom-clean)

`Dsupport_card_add_Dzero_card`, `alignedSet_subset_Dzero`,
`voteSet_subset_Dsupport`, `riders_mul_le_Dsupport`,
`card_add_three_le_union_add_pairs` (subtraction-free 3-set
inclusion–exclusion), `heavy_window_closure_numbers`,
`three_heavy_riders_budget`, `base_row_stack_carries_no_riders`;
honest Prop `GlobalConsistencySwarmResidual`.
