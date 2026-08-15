# G316: closed formula for the antipodal-pair model

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G314 and G315 identified an antipodal-pair model behind the certified large-field toy tables. G316
turns that model into a compact formula.

Let `n=2h` and pair the roots as `{e_j,-e_j}`. Let `u` mark the size of the `r`-subset `A`, and `v`
mark the size of the `(r-1)`-subset `B`. The local balanced-choice polynomials are:

```text
N = 1 + 2uv + u^2 + v^2 + u^2v^2       neutral pair
U = u + v + u^2v + uv^2                unit-forced pair
D = uv                                  double-forced pair
```

For coefficient 1, every contributing case has even `deg_u-deg_v`, while adjacent ranks require
`deg_u-deg_v = 1`. Hence the coefficient-1 antipodal-model dot is zero for every adjacent rank.

For coefficient 2, define

```text
T_m(r) = [u^r v^(r-1)] U N^m.
```

Then the antipodal-model dot is

```text
D_2(h,r) = 2h*T_{h-1}(r) + 4h(h-1)*T_{h-2}(r-1).
```

The first term is the same-pair case `z=y`; the second term is the different-pair case
`pair(y) != pair(z)`. The opposite same-pair case `z=-y` contributes zero for coefficient 2.

For the live ranks this coefficient extraction simplifies to:

```text
D_2(h,5) = 2h*(11*C(h-1,2) + 161*C(h-1,3) + 406*C(h-1,4))
D_2(h,6) = 2h*(C(h-1,2) + 81*C(h-1,3) + 786*C(h-1,4) + 1722*C(h-1,5))
```

The script checks this formula against the brute antipodal model for `n=16` at every rank and for
`n=32` at ranks `5,6`. It also emits the next closed-form predictions:

```text
n=16:  r=5 dot=321216,      r=6 dot=1064448
n=32:  r=5 dot=20115200,    r=6 dot=200992512
n=64:  r=5 dot=864230400,   r=6 dot=20331698688
n=128: r=5 dot=31776632832, r=6 dot=1609610978304
```

## Scope

This is a formula for the antipodal-pair model, not a proof that every finite-field cell has no
extra modular relations. The certified field computations already matched this model for `n=16` all
ranks and `n=32` ranks `5,6`; G316 isolates the exact combinatorial highway those checks were
following. The next production-facing question is to prove when the finite-field relation count
equals this antipodal model, or to bound the extra relations.

## Artifact

- Probe: `scripts/probes/g316_antipodal_closed_formula.py`
- Output: platform temp directory `arklib-reports/g316_antipodal_closed_formula.out`
