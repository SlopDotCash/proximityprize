# R260 filtered joint fine-budget stress

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R259 showed that the naive joint fine-layer budget is dominated by known
direct-MGF failure rows.  R260 filters those rows out and asks whether the same
budget works on the remaining exact-`MGF <= 2` branch.

## Probe update

`scripts/probes/probe_r259_n64_joint_fine_budget.py` now supports:

```text
--max-exact-mgf <value>
```

which discards rows whose exact full quarter-MGF exceeds that threshold before
ranking the joint envelope budgets.

## Command

```bash
python3 -m py_compile scripts/probes/probe_r259_n64_joint_fine_budget.py
for trim in 1 2 4; do
  python3 scripts/probes/probe_r259_n64_joint_fine_budget.py \
    --min-index 512 --max-index 12000 --chunk 8192 \
    --trim "$trim" --tau 0.5 --step 0.03125 \
    --max-exact-mgf 2.0 --top 12
done

python3 scripts/probes/probe_r259_n64_joint_fine_budget.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --trim 1 --tau 0.5 --step 0.03125 \
  --max-exact-mgf 1.8 --top 12
```

## Result

Filtering exact-MGF failures helps, but the product/envelope method still does
not close.

```text
max_exact_mgf=2.0:
  trim=1 worst budget=2.31345546 at M=522,  p=33409
  trim=2 worst budget=2.35348949 at M=522,  p=33409
  trim=4 worst budget=2.41194145 at M=1030, p=65921

max_exact_mgf=1.8:
  trim=1 worst budget=2.06130211 at M=6583, p=421313
```

So even after removing direct failures, the envelope overpays by `0.31` in the
`MGF <= 2` branch and by `0.061` under a stricter `MGF <= 1.8` margin.

## Interpretation

The right object is not:

```text
mean(exp(lift(X32)/4)) * unweighted_tail_envelope(R_fine).
```

That product loses the anti-correlation/cancellation between coarse weight and
fine residual rank.  The next theorem-shaped target should be a **weighted
fine-tail bound**:

```text
sum_{R_fine >= theta, after top trim}
  exp(lift(X32)/4)
<= C_weighted * M * exp(-theta/2)
```

or its layer-cake/MGF-integrated equivalent.

This is a sharper and more faithful replacement for the failed product
composition.
