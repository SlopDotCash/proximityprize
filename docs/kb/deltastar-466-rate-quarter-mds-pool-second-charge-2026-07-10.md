# Rate-quarter predecessor: the MDS-pool second charge — literal instantiation, one shrink, permanent double-stall at depth 2

## Status

Executes ranked target 1 of the derecursion round.  **Verdict: the pool-level
second D-charge works exactly as hoped structurally — and then the iteration
dies for a clean, exactly-pinned reason: the running threshold collapses below
`k − 1` after one level, and below `k − 1` no Johnson condition can ever fire
again.**  The charge iteration terminates at depth 2; the surviving
configurations sit in the beyond-Johnson band of MDS agreement families — the
prize wall.

Formal kernel (pg-iterate ✅ OK 26s, 8 audited theorems, all on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterMDSPoolSecondCharge.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` (MDS
section — threshold cap, collapse inequality, full-regime band sweep).

## 1. What works

* **Pool bound**: `F ≤ N − T = 480946858` universally
  (`pool_card_le_N_sub_T`; the base witness sinks into `{D = 0}`) — sharpens
  the previously stated stall range end by one.
* **MDS pool**: distinct codewords collide on `≤ k − 1` pool coordinates
  (`pool_separation`, restriction of `predecessor_sep`); for `F ≥ k` the
  punctured code is genuinely MDS of dimension `k`.
* **Literal iteration**: the sink/source lemmas of the global charge are
  generic in the stack, so the second charge is an instantiation, not a new
  proof: level-2 stack `(u₁, −D)`, pool base `(s₀, q₀)`, second discrepancy
  `D₂ = q₀ − u₁ + s₀·D` (`second_charge_vote_source`,
  `second_pool_closed_form`).  It buys one genuine shrink:
  `|{D₂ = 0}| ≥ t₁` (level-2 threshold).

## 2. Why the iteration dies: the threshold collapse

The pool-level threshold is what a swarm rider is guaranteed to burn on the
pool: `t₁ = T − J_Z(F)`.  Since `|Z| = N − F ≥ T` always,
`J_Z ≥ ⌊√(T(k−1))⌋ = 398907491`, so

```text
t₁ ≤ T − 398907491 = 193887475 < k − 1 = 268435455    (second_level_threshold_cap)
```

**Collapse principle** (`threshold_collapse_stalls`): if the running threshold
`t` is positive and `< k − 1`, then at every later charge level the
sub-Johnson window is nonempty for every pool choice — because each level's
zero-set carries a base witness (`Z ≥ t`) and

```text
(t − F')² ≤ t² < t·(k−1) ≤ Z·(k−1).
```

So after the first charge level the flow can never again reach a Johnson
regime: `double_stall` instantiates this at `t = 193887475`.  The probe sweeps
the whole MDS regime `F ∈ [k, N−T]`: even the COMBINED two-Johnson band
`(T − J_pool(F), J_Z(F)]` is nonempty everywhere (narrowest width `140584336`
at `F = k`; `J_Z + J_pool ≥ 733379302 > T` throughout) — both Johnson radii
together miss the threshold by `≥ 1.4·10⁸`.

## 3. Terminal verdict for the counting/charge cone

Every branch of the P1 predecessor pin through the pencil/charge arc is now:

1. **heavy-window CLOSED** (global consistency charge, `≤ 301989883 ≤ N`);
2. **small-pool CLOSED** (`F ≤ F₀ = 75018133`; greedy optimum
   `882722755 ≤ N`, probe-pinned; Lean layer assembly = flagged engineering);
3. **permanently sub-Johnson** after at most two charge levels — agreement
   families of MDS/RS codes strictly beyond the Johnson radius.

Branch 3 is precisely the beyond-Johnson regime of the proximity-gaps
conjecture: the counting cone bottoms out at the campaign's global wall, which
is consistent with (and explains) every earlier dead end of the arc.
`StallResidual` cannot be discharged by any further Johnson/charge iteration
— new input must be beyond-Johnson list structure (BGK/Paley-type, the prize
wall) or the structured-floor route (`PredecessorStructuredFloorResidual`).

## 4. Honesty

* No delta-star change; bracket `3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30)`
  untouched.
* The small-pool branch's Lean layer-cake assembly (ranked target 3) was
  assessed as not-quick and remains a flagged engineering gap with pinned
  arithmetic.
* The "flow contraction" hypothesis of the round is REFUTED, not confirmed —
  the contraction exists for exactly one step, then the threshold leaves the
  Johnson-visible range permanently.

## 5. Session arc summary (five landed files, 2026-07-10)

`_P1RateQuarterTwoCoverWindow` (window realized) →
`_P1RateQuarterGlobalConsistencyCharge` (heavy window closed; realized
geometry sterile) → `_P1RateQuarterDChargeDerecursion` (exact boundary
`F₀ = 75018133`; small-pool closed, stall taxonomy) →
`_P1RateQuarterMDSPoolSecondCharge` (double-stall; charge iteration terminal).
All axiom-clean; the predecessor pin's open content is now exactly:
`StallResidual` = sub/beyond-Johnson MDS agreement families, plus the flagged
small-pool Lean assembly.
