# R235 n=128 exception handling

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Question

Can the finite `n=128` failures from R234 be handled by increasing the trim
count, or do they require separate finite certificates?

## Larger trim sweep

Command:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 7 --medium-max-a 7 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --cache-dir /tmp/proximity-r231-n128 \
  --top 30 --trims 5 8 10 12 16 24 32 48 64 \
  --taus 0.5 0.75 1.0 1.5 2.0 --spike-budgets 0 \
  --step 0.03125 --cutoff 0
```

Summary:

```text
cases=565
feasible_rows=0
best_budget=2.740389
trim=8
tau=0.5
K=0
budget witness: n=128 p=65537 M=512
```

Increasing the trim count does not repair the `p=65537` row; it makes the top
payment larger and the total budget worse.

## Excluding the Fermat row

With `M >= 513`, the remaining worst row is still a failure:

```text
n=128 p=231169 M=1806
total=2.075371
topStair=0.362695
maxX=24.388818
fifth=13.953538
```

## Excluding both finite failures

A direct cached check excluding `p in {65537, 231169}` leaves comfortable slack:

```text
cases=563
worst remaining total=1.897375
slack=0.102625
worst remaining row: n=128 p=288257 M=2252
```

## Interpretation

The n=128 lane should be split explicitly:

```text
special finite direct certificates:
  (n,p,M) = (128,65537,512)
  (n,p,M) = (128,231169,1806)

ordinary n=128 lane:
  same top-five residual certificate appears to have >0.10 slack
  in the tested M <= 4096 window.

main asymptotic lane:
  n >= 256, top-five certificate has even larger slack.
```

The two exceptional rows should not be forced through the asymptotic top-five
budget theorem.  They should be discharged by exact finite certificates or by a
structured-prime lemma tailored to their spike profile.
