# #466 R309: c=3 relation-web formula

Date: 2026-07-09

## What landed

`Frontier/_R309C3RelationWebFormula.lean` proves the arithmetic simplification
for the `c = 3` relation-web histogram identified by the R308 probe/anatomy:

```text
c3HistogramMass n = 60 n^2 - 90 n
```

and compares it to the depth-3 exact-Wick headroom:

```text
depth3Headroom n = 45 n^2 - 40 n.
```

Main declarations:

```text
c3HistogramMass_eq
depth3Headroom_lt_c3HistogramMass
c3HistogramMass_sub_headroom
```

For every `n >= 4`, the c=3 histogram mass exceeds the depth-3 headroom.  The
gap is:

```text
c3HistogramMass n - depth3Headroom n = 5 n (3 n - 10).
```

## Meaning

This does not prove the relation-web classification.  It locks the algebraic
consequence of that classification, preventing constant drift: if the three
strata are proved as stated, the c=3 web is too large for the depth-3 headroom.

## Validation

Passed:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R309C3RelationWebFormula.lean
```
