# SYZ52 — lift test of the SYZ50 band-realizable interior ι=2 witnesses (2026-07-11)

**Issue #466 · rate-1/2 proximity-gap δ\* · CORE OPEN / ON-BGK**

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ52WitnessLift.lean`
Probe: `scripts/probes/probe_syz52_witness_lift.py`
Branch: `codex/syz52-witness-lift` (off `fork/research/proximity-prize` @ 73240c621)
Predecessors: `deltastar-466-syz50-witness-realizability-2026-07-11.md`,
`deltastar-466-syz32-cluster-routing-2026-07-11.md`,
`deltastar-466-syz28-d3-coplanar-crack-2026-07-11.md`

## The question

SYZ50 found that at rate 1/2 the balanced-interior region **meets** the band-realizable polytope;
the smallest realizable balanced `(4,4,4)`, `t=2` config lives on `μ₁₄ ⊂ 𝔽₂₉` and carries **357**
genuine constant-syzygy on-domain `ι=2` witnesses (three disjoint size-4 pairwise regions, a size-4
`R=W_BC/W_AC` level set, 2 points for the triple `T`). SYZ50 relocated the open gate to the
**over-budget-stack lift**: does the `ι=2` syzygy let a stack beat the pencil accounting via extra
scalar coincidences (exactly what the union-rank/generation accounting feared)? SYZ52 runs that
lift test.

## Method (probe, over the *actual* μ₁₄ ⊂ 𝔽₂₉ domain — the syzygy is realized, not abstract)

For each witness build the three band cores `core_A=S_AB∪S_AC∪T`, `core_B=S_AB∪S_BC∪T`,
`core_C=S_AC∪S_BC∪T` (each size `s=a+a+t=10`, `RS[14,7]`). Build stacks `(u₀,u₁)` with all three
cores degenerate (null space of the joint `A_C` constraint with per-core scalars — SYZ32 machinery),
and count the **exact** `mca`-bad scalar set word-level (both `mcaEvent` clauses: line-closeness
`is_close` on `u₀+z·u₁` plus the `inf` point, filtered by mutual correlated agreement `mca_holds`).
Cross-validation and a random-pencil control anchor the numbers.

## Decisive verdicts

**Cross-validation (machinery is sound).** The same code reproduces the SYZ32 crack **exactly**:
SYZ31 near-duplicate cluster (`n=16,k=8,s=11,p=17`) → merge holds `1000/1000`, every stack
`mca`-correlated, max `mca`-bad `= 0`, raw pool `= 18`. Verbatim SYZ32 stack-vacuous verdict.

**A. The μ₁₄ interior witnesses are ANOMALOUS — they DEFEAT the merge/yield accounting.**
Deficiency `d=1` (all 357); the three cores **never merge** on **328/357** witnesses
(`merge_tested=0` — fewer than two cores ever share a local codeword); **no** stack is
`mca`-correlated; and the max `mca`-bad scalar count reaches **`19`** (global, over all 357) —
far above the SYZ22 pencil budget `n−1 = 13`, the pencil-yield ceiling `∑(n−sᵢ)=3·(14−10)=12`, and
`n=14`. Full distribution of per-witness max `mca`-bad:
`{11:2, 12:7, 13:19, 14:120, 15:169, 16:20, 17:5, 18:8, 19:7}` — **329/357 exceed the budget 13**
and **209/357 exceed `n=14`**. The over-budget behaviour is the rule, not an outlier.

**B. Control rules out a small-field artifact.** Random pencil stacks at the same `n=14,k=7,s=10`
have max non-`mca` bad count **`6`** (mean `1.07`, p95 `3`): generic pencils obey the strip's
small-bad-set behaviour, so the witnesses' `≥19` is a genuine effect of the `ι=2` general-position
geometry, not the scale. (A random word is `s`-close only `4%` of the time — the threshold is
meaningful.)

**C. The mechanism — the SYZ32 merge shield is STRUCTURALLY UNAVAILABLE (field-independent).**
Two band cores share exactly one pairwise region + the triple, so their overlap is `|S_ij|+t`. For a
balanced realizable `(d,d,d)` the SYZ50 budget cap `max+1+t ≤ k` forces the pairwise core overlap
`d+t ≤ k−1 < k` — **strictly below** the RS-uniqueness merge threshold `k`. So the merge that
collapsed the SYZ32 cluster to one pencil (overlap `10 ≥ k=8`) **cannot fire** here (μ₁₄:
`d+t=4+2=6 < 7=k`, matching `merge_tested=0`). The cores sit in general position; the yield-degeneracy
that gave SYZ32 its `mca`-bad `= 0` is unavailable, and the pencil accounting is not merge-protected.

**D. Not a strip falsification — the Johnson edge.** The interior band straddles the rate-1/2
Johnson radius `1 − √(1/2) ≈ 0.293 ∈ (1/4, 1/3)`: the `n=14` witness has `δ = 4/14 = 2/7 ≈ 0.286`
(just **below** Johnson), the `n=16` witness has `δ = 5/16 = 0.3125` (just **above**). Near/above
Johnson the proximity-gap bad-set bound is large/divergent, so the high `mca`-bad counts are **not**
per se a BCIKS contradiction. Framed conservatively: under the campaign's SYZ32 `mca` filter these
stacks are non-correlated with bad-counts far above the SYZ22 budget and the random baseline, which
**defeats the merge/yield accounting route**; it is **not** claimed as a strip refutation. Any valid
shield must invoke the genuine near-Johnson proximity-gap list bound, not the pencil-yield/merge
combinatorics.

**E. Scale check (n=16, μ₁₆ ⊂ 𝔽₁₇).** Next realizable balanced config `(4,4,4)`, `t=3`, `s=11`:
overlap `a+t = 7 < 8 = k` (no merge, `8/8`), matroid deficiency `d=0` here, and max `mca`-bad
`= 18 > 16 = n > 15 = budget`. The anomaly **persists** at the next size — and note `d=0`, so the
over-budget lift is driven by the general-position no-merge geometry, **not** by matroid
deficiency. The structural mechanism (overlap `= a+t ≤ k−1 < k`, no merge) holds at every size by
construction (SYZ50 budget cap; proven in Lean). (Larger `n=18..24` scans are combinatorially
expensive; the `n=14` and `n=16` witnesses already bracket the Johnson edge — see D.)

## What was proved (Lean, axiom-clean pure ℕ) — `Frontier/_SYZ52WitnessLift.lean`

- `coreOverlap r t = r + t`, `MergeApplies r t k := k ≤ coreOverlap r t` (RS-uniqueness threshold).
- `overlap_lt_k_of_realizable` : `Realizable d d d t k → coreOverlap d t < k` (budget cap ⇒ sub-`k`).
- `merge_unavailable_of_realizable` : `Realizable d d d t k → ¬ MergeApplies d t k` — **the SYZ32
  merge shield is structurally unavailable on every band-realizable interior witness**.
- `mu14_overlap_lt_k` (`6<7`), `syz32_crack_merges` (`10≥8`), `mu14_realizable_and_nonmerging`,
  `shield_does_not_transport` — the μ₁₄-vs-crack separation as one statement.

Axiom audit: all theorems depend only on `propext`/`Quot.sound` (via imports); the two `decide`
facts (`mu14_overlap_lt_k`, `syz32_crack_merges`) depend on **no axioms**. No `sorry`, no
`native_decide`.

## Honest status

The band-realizable `ι=2` interior witnesses are **NOT stack-harmless via the SYZ22/SYZ32
accounting**: the merge shield is provably unavailable (`overlap = d+t < k`), and the lift blows
past the pencil budget/ceiling and `n` (max `mca`-bad `= 19`, `329/357` over budget, vs a random
baseline of `6`). This is the **first empirical trace of the `ι=2` structure mattering at stack
level** — the general-position (non-merging) geometry defeats the merge/yield route, independent of
matroid deficiency (`d=1` at `n=14`, `d=0` at `n=16`, same anomaly). It is **not** claimed as a
strip falsification (Johnson-edge radius). The residual is now sharp: the shield must come from the
genuine near-Johnson proximity-gap list bound, not pencil-yield/merge combinatorics. CORE remains
OPEN / ON-BGK.

## Reuse hooks

- `overlap_lt_k_of_realizable` / `merge_unavailable_of_realizable` — the budget cap ⇒ every band
  core pair is sub-merge-threshold; kills any attempt to transport a merge/yield argument (SYZ32,
  SYZ29) into the band-realizable interior.
- `probe_syz52_witness_lift.py` `lift_test` — SYZ32-style exact `mca`-bad lift over an **arbitrary**
  domain `alpha` (numpy-vectorized `_agr_masks`); reuse for any on-domain witness lift, and the
  random-pencil control for the strip baseline at a given `(n,k,s)`.
