# δ* #466 — R218 Markov moment tail consumer

R218 formalizes the elementary moment-to-survival bridge:

```text
θ^r · #{b ∈ s : θ ≤ t_b} ≤ Σ_{b∈s} t_b^r.
```

Specialized to the nonzero normalized-square period spectrum, this gives a
finite-grid route into R216: choose a moment order `r(θ)` at each threshold,
prove

```text
Σ_{b≠0} X_b^{r(θ)} ≤ B(θ) · θ^{r(θ)},
```

and R216 consumes the resulting grid tail.

## Probe

Artifact:

```text
scripts/probes/probe_r218_markov_tail_from_wick.py
```

The probe asks whether ideal exponential/Wick moments

```text
E[X^r] ≤ A · r! / c^r
```

can certify the target half-rate tail by optimized Markov:

```text
P[X ≥ T] ≤ min_r A · r! / (cT)^r
```

against

```text
0.6 · exp(-T/2) + 2/M.
```

## Readout

Optimistic `A=1,c=1`:

```text
worst_ratio=2.74787 T=1.000 markov=1 target=0.363918 r=1
certifies_all=False
```

Measured/weaker `A=1,c=0.59`:

```text
worst_ratio=4.66628 T=5.000 markov=0.229819 target=0.049251 r=2
certifies_all=False
```

Conclusion: moment Markov is a useful high-threshold bridge, but it does not
prove the live `0.6 exp(-T/2)+2` survival law by itself.  The low and mid
thresholds require genuine distributional input, not only moment ceilings.

## Lean check

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R218MarkovMomentTailConsumer.lean
```

Result:

```text
OK (7s)
```
