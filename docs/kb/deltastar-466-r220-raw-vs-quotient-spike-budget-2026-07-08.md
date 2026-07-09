# δ* #466 — R220 raw vs quotient spike budget

R219 works on the raw nonzero frequency carrier.  Most exact probes evaluate
one representative per `μ_n`-coset because `|η_b|` is coset-constant.  Therefore
a quotient-coset tail

```text
N_q(T) <= C * M * exp(-T/2) + K
```

translates to a raw-frequency tail

```text
N_raw(T) <= C * (p - 1) * exp(-T/2) + n * K.
```

R220 tests this distinction.  The probe is:

```text
scripts/probes/probe_r220_raw_vs_quotient_spike_budget.py
```

Compile hygiene:

```text
python3 -m py_compile scripts/probes/probe_r220_raw_vs_quotient_spike_budget.py
```

passed.

Smoke command:

```text
python3 scripts/probes/probe_r220_raw_vs_quotient_spike_budget.py --skip-large --chunk 8192
```

Output:

```text
R220 raw-vs-quotient spike budget C=0.6 K=2.0 step=0.5 rows=4
rawLitEx  rawScaleEx qExcess   T,count_q raw_count maxX    mgf1/4  M       n    p          label
----------------------------------------------------------------------------------------------------------------------------------
   61.832    -64.168   -1.003 20.5,1       64        20.691  2.7523  124     64   7937       r202-medium-mgf-counterexample
   -4.413    -66.413   -2.075 6.0 ,1       32        6.226   1.3864  36      32   1153       r200-worst-spike-ratio
 -188.625   -250.625   -7.832 9.0 ,1       32        9.002   1.3900  1025    32   32801      r202-worst-large-spike
-1794.555  -2304.555   -9.002 17.0,1       256       17.291  1.4101  65548   256  16780289   large-grid-start

summary
max_raw_literal_excess=61.831642
max_raw_scaled_excess=-64.168358
max_quotient_excess=-1.002631
```

Full command:

```text
python3 scripts/probes/probe_r220_raw_vs_quotient_spike_budget.py --chunk 32768
```

Output:

```text
R220 raw-vs-quotient spike budget C=0.6 K=2.0 step=0.5 rows=5
rawLitEx  rawScaleEx qExcess   T,count_q raw_count maxX    mgf1/4  M       n    p          label
----------------------------------------------------------------------------------------------------------------------------------
   61.832    -64.168   -1.003 20.5,1       64        20.691  2.7523  124     64   7937       r202-medium-mgf-counterexample
   -4.413    -66.413   -2.075 6.0 ,1       32        6.226   1.3864  36      32   1153       r200-worst-spike-ratio
  -94.811   -348.811   -2.725 27.0,1       128       27.172  1.4103  2097179 128  268438913  large-anchor
 -188.625   -250.625   -7.832 9.0 ,1       32        9.002   1.3900  1025    32   32801      r202-worst-large-spike
-1794.555  -2304.555   -9.002 17.0,1       256       17.291  1.4101  65548   256  16780289   large-grid-start

summary
max_raw_literal_excess=61.831642
max_raw_scaled_excess=-64.168358
max_quotient_excess=-1.002631
```

Readout: literal `K = 2` on raw nonzero frequencies is refuted by the
`n = 64, p = 7937` medium row.  This is not a failure of the quotient tail:
the quotient excess is negative.  It is exactly the expected coset-multiplicity
effect.  For R219 on raw frequencies, the spike reserve should be scaled as
`Kspike = n * Kquotient` or the carrier should be changed to quotient cosets.
