# δ* #466 — top-spike ancestry in the dyadic tower (2026-07-08)

## Hypothesis

R187 showed that finite moments alone cannot prove the exponential MGF target:
one must forbid isolated far-tail spikes structurally.  R188 tests whether
actual dyadic top spikes have a rigid ancestry in the tower

```text
μ_{n/2} ⊂ μ_n.
```

A large parent period should be assembled from two child periods.  If top
parents require two large same-sign children, then far-tail control can be
attacked through an ancestral branching/counting theorem.

Probe: `scripts/probes/probe_r188_top_spike_ancestry.py`.

## Result

Top 20 parent cosets in representative rows:

```text
n p top maxX sameSign align[min,mean] meanMinChild meanParentOverChildSum
--------------------------------------------------------------------------------------------
32  1048609    20  16.508   1.000    [1.000,1.000] 4.525        0.965
64  16778497   20  27.584   1.000    [1.000,1.000] 7.103        0.974
128 268437889  20  23.688   1.000    [1.000,1.000] 8.190        0.980
256 16777729   20  16.587   1.000    [1.000,1.000] 4.980        0.964
```

The largest individual parent in each row was likewise a same-sign merge of
two already-large children.  Example:

```text
n=64, p=16778497:
  parent maxX = 27.584
  children = 14.516 and 13.087
  parent/(child sum) = 0.9993
```

## Verdict

The dyadic far tail is not made of isolated one-generation accidents.  Top
spikes are ancestral chains of large same-sign child merges.

This suggests a concrete no-far-spike theorem:

```text
High-tail ancestry theorem.
If a parent coset has X_parent ≥ T, then both child cosets have normalized
scores ≥ cT (or one child is exceptionally huge), and their signs agree.
The count of such same-sign high-child pairs decays fast enough to imply
MGF(1/4)≤2.
```

This is stronger and more structural than finite moments.  It targets the
actual obstruction found by R187: isolated far-tail spikes are forbidden
because a spike must have a high-tail ancestry through the dyadic tower.

Honest scope: this is still a conjectural combinatorial/probabilistic theorem.
But it gives a very specific object to prove: count aligned high-child pairs,
not arbitrary period maxima.
