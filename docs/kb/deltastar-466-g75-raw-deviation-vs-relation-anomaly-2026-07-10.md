# Issue #466 G75: raw deviation versus centered relation anomaly

Date: 2026-07-10

## Correction

G74's critic probe did not evaluate R366's signed object. It measured:

- complex linear forms in the Gauss periods `eta_b`;
- the sign of the raw full-energy deviation `E_r - Wick_r`;
- phase coherence on the maximum-magnitude multiplicative coset.

R366's `relationAnomaly` is instead the real weighted shadow-pair discrepancy

```text
Anom_r = q * shadowCollisionMass - (n^(2r) - shadowEnergy).
```

A kernel pair has coefficient `q-1`; a non-kernel pair has coefficient `-1`. The cancellation is
between kernel and non-kernel shadow-difference orbits. The identity `eta_(bg)=eta_b` for `g` in the
subgroup makes phase coherence inside one multiplicative coset tautological and does not control
this cross-orbit discrepancy. R378 already proves the analogous useful fact on the relation side:
each negacyclic rotation orbit is mass/sign coherent. That result leaves cancellation across orbits
open, exactly as R366/R367 state.

## Exact calibration

Let

```text
B_r = shadowEnergy,
C_r = shadowCollisionMass,
E_r = B_r + C_r,
W_r = a proposed Wick scale,
K_r = q W_r - (q-1) B_r.
```

G75 proves

```text
Anom_r - K_r = q (E_r - W_r) - n^(2r).
```

Therefore

```text
Anom_r <= K_r  iff  q (E_r - W_r) <= n^(2r).
```

The raw Gaussian inequality `E_r <= W_r` is sufficient, but stronger than necessary by the exact
DC allowance `n^(2r)/q`. G75 also proves that, at the concrete Wick scale and under exact order, the
centered relation budget is equivalent to `DCEnergyBound (powerRootSet g n) r`, not merely sufficient
for it. This cleanly separates the roles of the preceding results:

- FS15--FS18 prove the stronger raw inequality on their good-prime sets.
- G64 proves deep prize rungs cannot remain raw-good because the principal character alone crosses
  the raw Wick ceiling.
- G64 does not imply failure of the centered target. Failure requires the raw excess to exceed the
  entire DC allowance, not merely to become positive.

## Exact probe

The G75 probe computes `B_r` exactly from the signed-coordinate return recurrence and computes the
finite-field spectrum by FFT. It reports

```text
S_r / ((p-1) B_r),  S_r = sum_(b != 0) |eta_b|^(2r),
Anom_r / K_r.
```

Representative outcomes:

- `n=64, p=16777729, v2(p-1)=9, beta=4.000007`: `Anom/K` remains negative through `r=40`.
- `n=64, p=264961, v2(p-1)=8`: also remains negative through the tested range.
- `n=64, p=355009`: fails the centered budget from `r=2` through `r=20`, then passes by `r=24`.
- `n=64, p=4017089`: `Anom/K = 7.98, 9.22, 11.29, 14.52, 19.18, 32.92, 48.99, 59.35`
  at `r=2,3,4,5,6,8,10,12`; it returns below one only near `r=32` when the factorial shadow ceiling
  becomes too large to be useful.

Thus neither maximal 2-adic valuation nor raw-deviation sign decides the centered relation route.
The missing arithmetic is a saddle-depth weighted equidistribution theorem across relation orbits.

## Literature placement

Podesta and Videla, arXiv:1911.08549, identify Gauss periods as the eigenvalues of generalized
Paley Cayley graphs. Standard Fourier analysis of random walks on finite abelian groups identifies
centered return discrepancies with moments of the nontrivial eigenvalues. R366/R367 is this spectral
mixing problem rewritten in characteristic-zero shadow/relation coordinates.

Shkredov and Vyugin's finite-intersection theorem for additive shifts of multiplicative subgroups
(arXiv:1102.1172) is a genuine structural input, but G73 proves its finite-`k` exponent floor remains
above the required half exponent. It does not control the G75 cross-orbit discrepancy at the
`r ~ log p` saddle.

## Status

G75 is an axiom-clean correction and handoff. It prevents a false closure of the only correctly
centered signed target. CORE remains open.
