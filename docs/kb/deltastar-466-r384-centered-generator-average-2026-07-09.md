# Issue #466 R384: centered primitive-generator average

Date: 2026-07-09

R384 keeps the negative mass discarded by the positive R383 incidence bound. For an endpoint `d`,
let `Z(d)` count primitive generators at which its polynomial vanishes. The exact identity is

```text
sum_generators centeredLoad
  = sum_d endpointMass(d) * (q * Z(d) - phi(n)).
```

When every primitive generator describes the same dyadic subgroup, the left side is
`phi(n) * centeredLoad`.

This identifies the live cross-generator target: doubled-walk endpoint mass must equidistribute
against primitive-root incidence with density `phi(n)/q`, at Wick-scale error. A pointwise upper
bound on `Z(d)` cannot provide this centering; both the `Z=0` negative mass and `Z>0` positive mass
must be compared.

`centeredLoad_le_iff_average_le` completes the no-gain audit: for a nonempty primitive-generator
family with common load, an upper bound on the averaged expression is equivalent to the original
upper bound after multiplying by exactly `phi(n)`. Thus the centered generator route is a faithful
new coordinate system, but not a weaker theorem than the original DC-subtracted energy wall. Its
remaining weighted equidistribution statement is the same wall in primitive-root-incidence form.
