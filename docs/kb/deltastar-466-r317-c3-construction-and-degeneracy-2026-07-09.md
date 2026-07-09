# #466 R317 — constructive `c = 3` fibers, and why `ζ^h = 3` alone is insufficient

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R317C3LargeFiberConstruction.lean`
proves the field-theoretic identities behind two observed `c = 3` web
families.  If

```text
ζ^m = -1,   ζ^h = 3,   k + h = m,
```

then `3ζ^k = -1`, and for every translate `t`:

```text
-ζ^t = 2ζ^t - ζ^(t+h) = 3ζ^(t+k),
1 + ζ^t + ζ^k = ζ^t - 2ζ^k.
```

These are the algebraic collision equalities used by the large and one
small-fiber template families.  The file is axiom-clean and deliberately does
not claim the unproved representation-count or exhaustivity portions of the
R311 signature law.

## Refutation pass

The tempting strengthening

```text
ζ^h = 3  =>  full R310 three-stratum histogram
```

is false without further nondegeneracy assumptions.  The existing exact
classifier reproduces both counterexamples:

```text
python3 scripts/probes/probe_r310_c3_histogram_classifier.py --n 16 --p 17 --c 3
python3 scripts/probes/probe_r310_c3_histogram_classifier.py --n 16 --p 193 --c 3
```

For `p = 17` (`d = 1`) it finds only two huge collision strata; for `p = 193`
(`d = 7`) it finds eight strata, neither equal to the R310 prediction.  In
contrast, the intended high-beta cases still match exactly:

```text
n = 32,  p = 21523361
n = 64,  p = 926510094425921
n = 128, p = 1716841910146256242328924544641
```

## Consequence

The constructive equalities are reusable, but the global relation-web theorem
must explicitly control low-order/overlapping relations; it cannot be inferred
from a single `c = 3` relation.  The remaining work is the finite
classification and multiplicity calculation under a sharp nondegeneracy guard.

## Validation

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R317C3LargeFiberConstruction.lean
```

Result: `OK`, with no `sorryAx` in the printed theorem audits.
