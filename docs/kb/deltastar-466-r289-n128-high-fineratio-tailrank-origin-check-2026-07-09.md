# #466 R289 n=128 high-fineRatio tail-rank origin check

## Question

R287/R288 showed that in the continuation window `M=12001..20000`, the
n=128 moderate high-fineRatio branch is mostly captured by `tailRank <= 8192`,
with a tiny boundary residual:

```text
tailRank > 8192:
  residualRows=29
  residualMass=0.03155764
  maxTailX=1.596075
  fineRatio < 0.80 for every residual row
```

R289 asks whether the same tail-rank split also explains the original
`M<=12000` scan, where R274 found the finite low-fineRatio exception
`p=231169`.

## Command

```bash
python3 scripts/probes/probe_r288_n128_high_fineratio_tailrank_residual.py \
  --min-index 512 --max-index 12000 \
  --progress-every-primes 150 --progress-every-seconds 30 --top 32
```

## Result

```text
R288 n=128 high-fineRatio tail-rank residual M=[512,12000] tailRank>8192
primes=1727 candidateRows=926 moderateRows=567 highRows=519
highMass=4.05440987
residualRows=0 residualMass=0.00000000 residualShare=0.00000000
```

There are no high-fineRatio rows escaping `tailRank <= 8192` in the original
window.

## Interpretation

The high-fineRatio tail-rank shoulder is stronger than R287 first suggested:

```text
M=512..12000:
  high branch is entirely inside tailRank <= 8192.

M=12001..20000:
  tailRank > 8192 residual exists, but is tiny-tail only:
    tailX < 2,
    fineRatio < 0.80,
    worst mass = 0.00141443.
```

This separates the two moderate obstructions cleanly:

```text
low-fineRatio branch:
  contains the finite heavy row p=231169 and a diffuse deep-tail tax.

high-fineRatio branch:
  main balanced shoulder inside tailRank <= 8192;
  late high-index boundary layer outside the shoulder, with tiny tailX.
```

## Next target

A theorem-shaped n=128 moderate branch certificate can now be stated as:

```text
ModerateBranch128:
  lowRatio (<0.75):
    finite exception p=231169 + rowwise/deep-tail envelope;

  highRatio (>=0.75):
    tailRank <= 8192 shoulder + tiny-tail boundary
    (tailRank > 8192 => tailX < 2 and fineRatio < 0.80 in the scanned range).
```

The next probe should test whether the `tailRank > 8192` boundary remains
`tailX < 2` and `fineRatio < 0.80` beyond `M=20000`, or whether the threshold
must grow slowly with `M`.

