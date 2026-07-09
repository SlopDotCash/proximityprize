# δ* #466 — near-zero/high-tail compensation law (2026-07-08)

## Hypothesis

R175 showed dyadic spectra are more polarized than random phase sums: extra
near-zero mass and heavier high tail, while the R168 MGF barely changes.  R176
quantifies that compensation by bins.

Probe: `scripts/probes/probe_r176_tail_zero_compensation.py`.

## Result

Across mature dyadic rows:

```text
dyadic low<0.5 ≈ 0.519
dyadic high>=4 ≈ 0.045
dyadic MGF(1/8) ≈ 1.1543
```

Random phase controls:

```text
random low<0.5 ≈ 0.391..0.395
random high>=4 ≈ 0.017..0.019
random MGF(1/8) ≈ 1.1428
```

Representative bin split:

```text
n=128 p=268437889
dyadic:
  [0,0.25): f=0.382, mean-share=0.031, mgf-share=0.334
  [0.25,0.5): f=0.138, mean-share=0.050, mgf-share=0.125
  [0.5,1): f=0.163, mean-share=0.118, mgf-share=0.154
  [1,2): f=0.160, mean-share=0.229, mgf-share=0.166
  [2,4): f=0.112, mean-share=0.313, mgf-share=0.138
  [4,8): f=0.041, mean-share=0.216, mgf-share=0.069
  >=8: f=0.004, mean-share=0.044, mgf-share=0.013

random:
  [0,0.25): f=0.221, mean-share=0.027, mgf-share=0.196
  [0.25,0.5): f=0.173, mean-share=0.064, mgf-share=0.158
  [0.5,1): f=0.239, mean-share=0.174, mgf-share=0.229
  [1,2): f=0.233, mean-share=0.331, mgf-share=0.244
  [2,4): f=0.116, mean-share=0.313, mgf-share=0.143
  [4,8): f=0.018, mean-share=0.089, mgf-share=0.029
```

## Verdict

The dyadic spectrum is polarized:

* much more mass near zero;
* much heavier high tail;
* conserved mean `E[X]=1`;
* small MGF penalty at rate `1/8`.

This suggests a proof route different from generic concentration:

```text
Prove a dyadic polarization/compensation theorem:
  high-tail mass is coupled to near-zero mass strongly enough that
  Σ exp(X/8) remains ≤ 2M.
```

The R168 finite-grid certificate is compatible with this: high bins can be
larger than random as long as low bins are also larger and the weighted
staircase sum stays below budget.
