# SYZ20: joint-rank super-additivity — the merge-corrected channel closes the strip via the integer lift (2026-07-11)

Status: **Lean landed, axiom-clean** (`Frontier/_SYZ20JointRankSuperadditive.lean`), plus an
exact-arithmetic probe. Verdict: **CLOSES the rate-1/2 decisive strip `(Johnson, 1/3)` at the
degenerate/syzygy channel — modulo one honestly-flagged bridge input** (the MDS union-span
dimension + sunflower min-union realizability). This is the structural upgrade SYZ19 named as the
missing theorem. Issue #466 / #507. Tag SYZ20.

## What SYZ19 was missing, and what SYZ20 supplies

SYZ19 diagnosed the leak precisely: the variable-core LP treats per-family rank costs as
**additive** (`∑_f (s_f − k) ≤ n − k`), which lets it buy many rank-cheap overlapping cores that
a single stack cannot host. SYZ20 replaces that with the physical **union-based** budget, in two
proven pieces:

1. **Super-additive plantable cap** (`plantable_span_cap`, fully-proven linear algebra). If a
   nonzero syndrome pair `v` is annihilated by a set of parity functionals whose **span** has
   dimension `ρ`, then `ρ + 1 ≤ finrank V`. The bound is on the joint **span dimension** (= joint
   syndrome rank), NOT a per-core independent count. This is `_G86…plantable_linearIndependent_cap`
   generalised from an independent family to an arbitrary span — overlapping cores contribute
   their union span automatically.

2. **MDS-duality union dimension** (`SuperadditiveUnion`, the packaged bridge input, verified in
   `scripts/probes/probe_syz20_joint_rank_superadditive.py`). For an MDS code, the dual codewords
   supported inside a coordinate set `U` form a space of dimension `max(0, |U| − k)` (MDS
   shortening — **PASS** at `RS[16,8], RS[32,16], RS[64,32]`, exact GF(p) rank). Hence the
   union-anchored parity functionals of degenerate cores `C₁,…,C_D` span exactly `2(|∪Cᵢ| − k)` of
   the `2(n−k)`-dim syndrome-pair space. Mechanism: `sᵢ ∈ span(columns off Cᵢ)` for every `i`
   ⟺ `sᵢ ∈ span(columns off ∪Cᵢ)` (intersection of complement-column-spans = complement of the
   union), a codimension-`2(|U|−k)` condition on the pair.

Chaining (1)∘(2): a non-codeword stack's degenerate cores satisfy `2(|U|−k)+1 ≤ 2(n−k)`, i.e.
`|∪Cᵢ| ≤ n − 1` (`union_card_lt_length`, `union_card_le`). Super-additive **in the union**, not
additive in the sizes.

## The merge correction and the arithmetic (the honest verdict)

Two degenerate cores overlapping in `≥ k` points **merge** (RS distance: two RS[n,k] codewords
agreeing on `≥ k` points are equal). So in a maximal decomposition cores pairwise overlap `≤ k−1`.

**Key regime fact (probe-checked).** In the strip at rate `1/2`, every core has `sⱼ ≤ t < n−1 =
2k−1`, so `2(k−1) ≥ sⱼ`. Then triangle-type packings are **infeasible**: pairwise overlap `q =
k−1` with `2q > s` forces triple overlaps `≥ 2q − s > 0`, so the union cannot fall below the
**sunflower** (common `(k−1)`-core). Randomised packing search (`probe_syz20…`) confirms no
config beats the sunflower `|U| = (k−1) + ∑(sⱼ − k + 1)` in this regime. Hence

  `∑ᵢ (sᵢ − k + 1) ≤ |∪Cᵢ| − (k−1) ≤ (n−1) − (k−1) = n − k.`

This is exactly **SYZ9's rank budget with the per-core cost raised `t−k → t−k+1`** (the merge
cost). The single-resource LP `max ∑ yield(sᵢ)` s.t. `∑(sᵢ−k+1) ≤ n−k`, `yield(s) =
⌊(n−s)/(t−s)⌋` (`s<t`) or `n−s` (`s≥t`):

* **Continuous optimum ties the budget** at the near-degenerate profile `s = t−1`:
  `(n−k)(n−t+1)/(t−k) = B` exactly at the strip top `δ = 1/3 − 1/(3n)` (`merge_near_crossover_eq`,
  `merge_crossover_lt_third`). Strictly safe for every `δ < 1/3 − 1/(3n)`.
* **Integer optimum strictly below budget throughout the strip.** At `n=64, k=32, B=64`:

```
 t   delta    zone       LPcont  arg(s,yield,cost)   LPint   arg(s,y,c,D)   budget  empMax(SYZ7)
 39  0.3906   above-1/3   118.9   (38,26,7)          104    (38,26,7,4)     64      104   KILLED
 40  0.3750   above-1/3   100.0   (39,25,8)          100    (39,25,8,4)     64      100   KILLED
 41  0.3594   above-1/3    85.3   (40,24,9)           72    (40,24,9,3)     64       72   KILLED
 42  0.3438   above-1/3    73.6   (41,23,10)          69    (41,23,10,3)    64       69   KILLED
 43  0.3281   STRIP        64.0   (42,22,11)          48    (33,3,2,16)     64       44   survives
 44  0.3125   STRIP        56.0   (43,21,12)          42    (43,21,12,2)    64       42   survives
 45  0.2969   STRIP        49.2   (44,20,13)          40    (44,20,13,2)    64       40   survives
```

The integer LP (`merge_integer_closes_strip_n64`) is `48, 42, 40 < 64` throughout the strip and
(`merge_integer_kills_above_third_n64`) `104,100,72,69 > 64` above `1/3` — the crossover sits
**exactly** at the strip top. `n=32` agrees (`merge_integer_n32`: strip `t=22` → `24 < 32`,
`δ>1/3` killed). Note `LPint` matches SYZ7's fully-`mcaEvent`-verified `empMax` **exactly** above
`1/3` (`104,100,72,69`) — strong validation of the model.

So the strip closure hangs on the **same integer lift** that promotes SYZ9's rate-`1/4` `3/7` to
`1/2`: the continuous relaxation ties the budget at the single top lattice radius `δ = 1/3 −
1/(3n)`, and the integer `D = ⌊(n−k)/(t−k+1)⌋` strictly closes it.

## Honest scope / residual to a fully in-tree strip theorem

- Part (1) — the super-additive span cap — is **fully proven** linear algebra (axiom-clean).
- The **arithmetic** — continuous crossover `1/3 − 1/(3n)`, integer strip closure, above-`1/3`
  calibration — is **fully proven** pure `ℕ`/`ℚ` (`decide` + `nlinarith`), no `native_decide`.
- Part (2) — the MDS union-span dimension `2(|U|−k)` and the regime-`2(k−1)≥s` sunflower
  min-union — is **probe-verified** and packaged as the structured hypothesis
  `SuperadditiveUnion`. It is a clean MDS-shortening fact plus a regime combinatorial min-union,
  the honest analogue of G87's "abstract-H" bridge simplification. To make the strip theorem
  fully in-tree one must (a) prove the shortening dimension count from in-tree GRS/Vandermonde
  machinery, and (b) prove the sunflower packing is realizable on a single stack with distinct bad
  supports (this is where SYZ18's `no_two_bad_scalars_share_witness` enters — it forbids the
  support collisions that a denser-than-sunflower packing would need).

**Net effect on the bracket.** Conditional on `SuperadditiveUnion`, the degenerate/syzygy channel
**provably starves throughout `(Johnson, 1/3)`** (not just below `(1−ρ)/(2−ρ)` as SYZ9 gave for
the pinned `s=t` channel): SYZ20 extends the wall to ALL variable-core stacks in the strip. With
SYZ6's ceiling `358612991/2^30` and the SYZ9 reach, this is the ceiling-side half of pinning
`δ*(rate 1/2, production) = 1/3` up to the lattice; the floor side still needs `CellPackageSupply`
(SYZ7/SYZ8). δ* bracket unchanged as an unconditional statement: `3/8 ≤ δ* ≤ 43/96+ε`.

## Formal results — `Frontier/_SYZ20JointRankSuperadditive.lean` (axiom-clean)

`propext, Classical.choice, Quot.sound` only. No `sorry`, no `axiom`, no `native_decide`.

- `plantable_span_cap` — super-additive cap: nonzero `v` annihilated by functionals of span-dim
  `ρ` ⟹ `ρ + 1 ≤ finrank V`.
- `SuperadditiveUnion` / `union_card_lt_length` / `union_card_le` — the joint-rank union budget
  `2(|U|−k)+1 ≤ 2(n−k)`, i.e. `|U| ≤ n−1`.
- `merge_near_crossover_eq` / `merge_crossover_lt_third` — continuous crossover `δ = 1/3 − 1/(3n)
  < 1/3`.
- `mergeBound` / `mergeOpt` / `merge_integer_closes_strip_n64` /
  `merge_integer_kills_above_third_n64` / `merge_integer_n32` — the integer LP strip closure +
  above-`1/3` calibration.

## Cross-references
- SYZ19 (the diagnosis SYZ20 answers): `docs/kb/deltastar-466-syz19-lp-dual-certificate-2026-07-11.md`.
- SYZ18 (distinct bad supports, needed for realizability): `Frontier/_SYZ18PairJointSelfExclusion.lean`.
- SYZ9 (pinned-`s=t` wall SYZ20 extends): `Frontier/_SYZ9ChannelRankWall.lean`, `channel_master`.
- Bridge: `Frontier/_G87McaEventSyndromeBridge.lean` (`finrank_syndromePair`, `syndrome_dichotomy`).
- Probe: `scripts/probes/probe_syz20_joint_rank_superadditive.py` (MDS-duality dim + corrected LP
  + triangle-infeasibility packing search); empirics `probe_syz7_strip_scan.py`.
- Issue #466 / #507. Tag SYZ20.
