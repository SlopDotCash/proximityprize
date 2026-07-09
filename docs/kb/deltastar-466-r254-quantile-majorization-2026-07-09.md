# #466 R254: quantile majorization probe

Date: 2026-07-09

## Question

R253 identifies the micro-band obstruction with the trim-five residual `q60`.
R254 asks whether this cap can be replaced by a smoother majorization or
partial-sum inequality.

Command:

```bash
python3 scripts/probes/probe_r254_quantile_majorization.py --cache-only
```

## Result

Worst micro-band rows:

```text
micro    q60      lowAvg60 upAvg60  lowSum60 upSum60  n     p          M
0.601134 0.790489 0.24124  1.54958  0.14426  0.92662  512   760321     1485
0.601039 0.783391 0.23537  1.54512  0.14071  0.92376  512   620033     1211
0.600614 0.779684 0.24250  1.53058  0.14473  0.91347  512   417793     816
```

Top correlations with the micro-band score:

```text
q60          +0.937601
lowSum0.7    +0.831196
lowAvg0.7    +0.825667
lowSum0.65   +0.777587
lowAvg0.65   +0.771633
lowSum0.6    +0.679450
lowAvg0.6    +0.673154
```

Upper partial averages are weak predictors. Lower-tail partial averages have
real signal but still underperform `q60`.

## Route update

Majorization is not refuted, but it is not an obvious simplification. A
possible theorem interface is:

```text
lower 65-70% residual mass is large enough
  => q60 cannot exceed 0.79049
  => micro-band cap.
```

This would require a strong lower-tail mass inequality, not merely a mean or
variance bound. The direct quantile envelope remains the sharper target.
