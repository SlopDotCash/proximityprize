# R256 n=64 divisor-layer correlation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R255 found no simple top-index geometry classifier for the `n=64` resonance
family.  R256 tests whether the bad `n=64` spikes are inherited from lower
divisor layers `n=8,16,32`, or whether they live in the fine `64/32` residual.

## Probe

New script:

```text
scripts/probes/probe_r256_n64_divisor_layer_correlation.py
```

For each row `p=64M+1`, it computes the quotient spectrum for `n=64` and for
divisors `d=8,16,32`.  Each `n=64` quotient coset maps into a coarser `d`
quotient coset, so the probe reports:

```text
correlation(X_64, lifted X_d)
mean X_64 on top n=64 rows
mean lifted X_d on those rows
mean fine residual X_64 - lifted X_d on those rows
```

## Command

```bash
python3 -m py_compile scripts/probes/probe_r256_n64_divisor_layer_correlation.py
python3 scripts/probes/probe_r256_n64_divisor_layer_correlation.py \
  --top 12 --chunk 8192 --divisors 8 16 32
```

## Findings

There is moderate whole-spectrum correlation with the `n=32` layer, but the
fatal top rows still carry large positive fine residuals after subtracting
the lifted `n=32` component.

For the dominant large-index row:

```text
p=697601 M=10900
corr(X64,X32)=0.5913
top_mean X64=20.826
top_mean X32=9.693
top_mean residual X64-X32=11.134
residual max=18.690
```

For the exact-square row:

```text
p=665857 M=10404
corr(X64,X32)=0.6147
top_mean X64=20.249
top_mean X32=12.072
top_mean residual X64-X32=8.178
residual max=20.213
```

For the older direct-MGF failure:

```text
p=204353 M=3193
corr(X64,X32)=0.6115
top_mean X64=16.876
top_mean X32=8.151
top_mean residual X64-X32=8.725
residual max=13.472
```

The coarser layers `n=8` and `n=16` explain still less of the top mass.

## Interpretation

The `n=64` obstruction is not simply inherited from lower divisor spectra.
The `n=32` layer is visibly correlated with the full spectrum, but the dangerous
top spikes retain a large fine-layer residual.

Next attack surface:

```text
analyze the fine layer X_64 - lifted X_32,
especially its top residual representatives and whether it has a smaller
stationary-phase/cyclotomic description.
```

This is a sharper target than the earlier whole-spectrum rank-sum envelope.
