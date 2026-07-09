# Issue #466 R355: generator-web Wick consumer

Date: 2026-07-09

## Result

R346 refuted the claim that every bad endpoint is controlled by one dominant binomial.
R355 replaces that failed structural claim by the weaker normalized census

```text
(r-s)! * #R_s <= 3^(r-s) * m^(r-s),
```

for each cancellation-depth stratum `R_s`.  Keeping R322's `s!` endpoint denominator and using

```text
choose(r,s) * s! * (r-s)! = r!
```

gives the axiom-clean headline

```text
r! * shadowCollisionMass <= 4^r * (2r)! * m^r.
```

Equivalently, this is an `8^r` loss over the Gaussian Wick mass
`(2r-1)!! * m^r`.  The loss is exponential only in moment depth, rather than ambient dimension,
and is compatible with the prize-scale moment optimization.

## Remaining target

It now suffices to prove `GeneratorWebCensus`.  R326 proves the required normalized count for
one low-`L1` generator sphere.  The unresolved structural step is a bounded-multiplicity encoding
of every realized relation stratum into a union of such spheres.  Unlike the refuted R325/R346
single-binomial law, this condition permits a multi-generator recurrence web and charges all
non-pairable six-webs rather than excluding them.
