# #466 R358 — the explicit bad endpoint has only ten six-web orbits

Exact enumeration at `p = 16,778,497`, `n = 64` gives:

```text
unordered triples                         41,664
occupied triple-sum values                 39,104
collision groups                              704
genuine non-antipodal collision pairs        640
affine exponent orbits                       10
```

The orbit action is `i ↦ u i + t (mod 64)` with `u` odd, together with
swapping the two sides of the triple equality. Every one of the ten observed
orbits has size 64.

As a control, neighboring primes `16,777,601`, `16,777,729`, and `16,778,561`
each have only 64 baseline collision groups and 29,760 baseline pair
collisions, with no genuine non-antipodal six-webs. The bad prime has 704
groups and 30,400 pairs: exactly 640 additional genuine collisions. The ten
orbits are therefore arithmetic signal, not a generic artifact of triple-sum
counting.

This is a major compression relative to the raw `3+3` template count. The
actual finite-field obstruction is carried by ten affine web types, not by
hundreds of thousands of formal templates. A viable next theorem should bound
the number of affine web types (or their transfer-matrix spectral radii) at
general dyadic order, then charge one resultant/recurrence carrier per type.

This computation also supplies a concrete falsification test: any proposed
uniform orbit-count law must reproduce ten types at this endpoint and must
allow the 640 genuine collisions.
