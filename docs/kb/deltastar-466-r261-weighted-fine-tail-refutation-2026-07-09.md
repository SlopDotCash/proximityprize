# R261 weighted fine-tail refutation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R260 proposed replacing the failed product envelope with a weighted fine-tail
bound:

```text
sum_{R_fine >= theta, after top trim} exp(lift(X32)/4)
  <= C * M * exp(-theta/2).
```

R261 measures this weighted constant directly.

## Probe update

`scripts/probes/probe_r259_n64_joint_fine_budget.py` now reports `CWtail`,
the weighted fine-tail constant, and supports:

```text
--sort c_weighted_tail
```

The summary now separately reports the worst budget and worst weighted-tail
row.

## Command

```bash
python3 -m py_compile scripts/probes/probe_r259_n64_joint_fine_budget.py

python3 scripts/probes/probe_r259_n64_joint_fine_budget.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --trim 1 --tau 0.5 --step 0.03125 \
  --sort c_weighted_tail --top 8

python3 scripts/probes/probe_r259_n64_joint_fine_budget.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --trim 1 --tau 0.5 --step 0.03125 \
  --max-exact-mgf 2.0 --sort c_weighted_tail --top 8
```

## Result

The weighted fine-tail constant is not uniformly small.

Unfiltered:

```text
worst_weighted_tail = 19.86057017
M=1024 p=65537
```

After filtering exact full-MGF failures (`exact MGF <= 2`):

```text
worst_weighted_tail = 1.88363490
M=1030 p=65921
budget=2.27700755
```

Other filtered high weighted-tail rows:

```text
M=2227 p=142529  CWtail=1.5924
M=6255 p=400321  CWtail=1.5238
M=4050 p=259201  CWtail=1.3984
```

Thus the positive weighted-tail theorem is still too crude unless it gains a
larger finite/resonance filtering branch.

## Route update

The next proof surface should not be a positive tail bound.  The data points
toward needing a signed/cancellation statement in the layer-cake composition,
or a more structural resonance decomposition:

```text
not enough:
  positive weighted tail of exp(lift(X32)/4) over R_fine survivors

needed:
  cancellation/anti-correlation between coarse layer and fine residual,
  or exact classification of the high weighted-tail resonance rows.
```

This is a useful failure: it prevents replacing the product envelope by an
equally positive but still overbroad weighted envelope.
