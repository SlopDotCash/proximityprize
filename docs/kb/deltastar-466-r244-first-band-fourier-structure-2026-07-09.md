# #466 R244: first-band Fourier structure

Date: 2026-07-09

## Question

R242/R243 show that the trim-five residual endpoint is a middle-bulk CDF
statement, not a low-moment statement. R244 recomputes the unsorted quotient
spectrum for the worst first-band rows and studies

```text
T = {coset index j : X_j >= 0.75} \ top_five
```

as a subset of the cyclic quotient group `Z/MZ`.

Command:

```bash
python3 scripts/probes/probe_r244_first_band_fourier_structure.py
```

## Output

```text
n     p          M      |T|    dens     half_C   maxFour  energy
512   760321     1485   612    0.412121 0.599633 0.030485 0.41326
512   620033     1211   499    0.412056 0.599538 0.033833 0.41345
512   417793     816    336    0.411765 0.599114 0.037416 0.41362
256   202753     792    323    0.407828 0.593387 0.041610 0.41000
```

Maximum cyclic interval densities:

```text
n,p          win16   win32   win64   win128  win256
512,760321   0.7500  0.6250  0.5781  0.5078  0.4766
512,620033   0.8125  0.6250  0.5625  0.5234  0.4805
512,417793   0.8125  0.7188  0.6094  0.5000  0.4688
256,202753   0.7500  0.6562  0.5469  0.4922  0.4766
```

The threshold set has small nonzero Fourier coefficients (`~0.03-0.04`) and
normalized additive energy essentially equal to its density (`~0.41`). Small
windows can clump, but there is no large interval, subgroup, or low-frequency
quotient structure explaining the worst rows.

## Route update

This refutes the easy structured-bad-set route. The first-band cap appears to
be a vertical distribution theorem for Gauss-period magnitudes:

```text
after deleting the five largest quotient values,
P[X >= 0.75] <= 0.4122
```

The survivor set itself is Fourier-uniform in the quotient index. A proof will
likely need to bound the value distribution of `X_j = |eta_j|^2 / sigma^2`
directly, rather than classify the threshold set by additive or interval
structure.
