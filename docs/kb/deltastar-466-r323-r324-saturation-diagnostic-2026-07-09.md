# R323--R324 Saturation Diagnostic and 2-Adic Refutation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Complete depth-3 diagnostic

R323 extends the primitive-recurrence census from the selected depth-4 cells
to all 1,158 primes in the complete `n=32`, depth-3 bad-prime table.

For every prime, the dominant relation resultant is divisible by `p`.  The
resultant quotient distribution is:

```text
Q=2: 675, Q=4: 250, Q=8: 111, Q=16: 47, Q=32: 9,
odd cofactor: 66.
```

Thus 1,092 of 1,158 cells are purely dyadically saturated.  Among the 259
high-beta cells, the worst DC-subtracted Wick ratios by quotient are:

```text
Q=2     1.0278933
Q=4     0.9314149
Q=8     0.9302888
Q=16    0.9189466
Q=32    0.9157922
Q=194   0.9147499
Q=386   0.9105526
Q=5186  0.9091705
```

The only high-beta super-Wick cell is again `p=21523361`, the `c=3`
recurrence with `Q=2`.  All 66 odd-cofactor cells are Wick-safe.  Resultant
quotient is therefore strongly diagnostic in this complete census, but pure
dyadic saturation is common rather than exceptional.

## Proposed 2-adic mechanism

The natural explanation was a repeated-root code.  In characteristic two,

```text
x^(2^k) + 1 = (x+1)^(2^k),
```

proved axiom-clean in `_R323RepeatedRootCyclotomic.lean`.  The quotient `2^a`
measures a local repeated-root defect, suggesting an `a`-bit parity code and a
possible Boolean hypercontractive bound.

## R324 refutation

That mechanism is false as a source of uniform mixing.  In
`F_2[t]/(t^a)`, for `a=2^s`, the orbit vectors

```text
(1+t)^j, 0 <= j < a,
```

form the mod-2 Pascal matrix.  It is triangular with diagonal one, hence a
basis.  Additive characters can therefore realize every sign pattern on the
orbit.  Choosing one negative sign gives character bias `a-2`, normalized

```text
1 - 2/a -> 1.
```

The exact probe verifies ranks and biases through `a=32`; the local spectral
gap falls as `2/a`.  Consequently the repeated-root 2-adic quotient has no
uniform spectral gap and cannot prove the centered recurrence mixing bound.

This also means the observed improvement as `Q` grows is not explained by the
local 2-primary factor: its intrinsic worst spectral behavior goes in the
opposite direction.  The improvement must arise from coupling to the odd
`p`-component, which is precisely where the Paley/BGK difficulty lives.

## Revised verdict

Primitive recurrence saturation remains a genuine exact structural discovery:
it compresses the relation lattice and predicts the empirical cells.  But
saturation plus local 2-adic hypercontractivity does not close the prize.  A
winning use of the recurrence presentation must prove a coupled archimedean
bound involving both the short recurrence and its `p`-component; treating the
dyadic quotient independently is refuted.

No prize closure is claimed.
