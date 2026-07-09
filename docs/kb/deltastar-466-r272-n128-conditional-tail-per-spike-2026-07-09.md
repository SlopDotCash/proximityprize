# #466 R272 n=128 conditional tail per top spike

## Question

R271 suggested a theorem-shaped branch:

```text
top n=64 child + aligned opposite-half tail child.
```

This probe tests the stronger one-piece certificate:

```text
for the top 8 n=64 children, the aligned opposite-half tail above threshold has
uniformly small exponential mass.
```

For each top-8 child it checks its unique opposite-half partner in the n=128
join and records the induced `exp(X128/4)/M128` mass when

```text
tailX >= tau,
fineRatio >= alpha,
phase >= 0.999.
```

## Command

```bash
python3 scripts/probes/probe_r272_n128_conditional_tail_per_spike.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-k 8 --cos-floor 0.999 --top 25
```

## Result

The cached scan has `6864` top-child rows.  Threshold totals:

```text
tau=2 alpha=0.75: hits=278 totalMass=4.157434 worstMass=0.246187
tau=2 alpha=0.90: hits=113 totalMass=2.256530 worstMass=0.246187
tau=2 alpha=0.95: hits=29  totalMass=1.130799 worstMass=0.246187

tau=4 alpha=0.75: hits=74 totalMass=1.975708 worstMass=0.246187
tau=4 alpha=0.90: hits=69 totalMass=1.732409 worstMass=0.246187
tau=4 alpha=0.95: hits=29 totalMass=1.130799 worstMass=0.246187

tau=6 alpha=0.90: hits=11 totalMass=0.821046 worstMass=0.246187
tau=6 alpha=0.95: hits=10 totalMass=0.744267 worstMass=0.246187

tau=8 alpha=0.90: hits=3 totalMass=0.422846 worstMass=0.246187
tau=8 alpha=0.95: hits=3 totalMass=0.422846 worstMass=0.246187
```

The worst certificate is stable across all thresholds:

```text
p=231169, M128=1806
mass=0.246187
top rank=4, topX=10.45
partner rank=1, tailX=14.07
fineRatio=0.988
MGF128=1.753, MGF64=1.403
```

## Conclusion

The one-piece top-8 conditional tail certificate is too broad.  It captures the
near branch, but also enough coherent/inherited mass that its total is not a
small error term.  Even strict thresholds `tailX >= 8` and `fineRatio >= 0.95`
leave total mass `0.422846`.

The surviving theorem shape is a two-stage split:

1. first pay or classify inherited resonance/top-tail rows via the resonance
   tree;
2. only then apply a conditional tail-around-spike bound to the non-inherited
   moderate branch.

In other words, "top child + aligned tail" is the right local mechanism, but it
is not by itself a global budget.  It has to be composed with the cross-level
mode taxonomy from R267/R268.
