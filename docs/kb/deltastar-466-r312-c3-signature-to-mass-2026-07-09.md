# #466 R312 — Lean bridge from `c=3` signatures to exact-Wick failure

## What landed

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R312C3SignatureToMass.lean
```

R311 reduced the `c=3` relation-web target to three collision-fiber count signatures:

```text
(3n-3, 3, 1)   with multiplicity n
(6, 3, 3)      with multiplicity 2n
(6, 3)         with multiplicity n(n-7)
```

R312 proves the arithmetic bridge:

```text
delta(3n-3,3,1) = 24n - 18
delta(6,3,3)    = 90
delta(6,3)      = 36
```

and therefore:

```text
n * delta(3n-3,3,1) + 2n * delta(6,3,3) + n(n-7) * delta(6,3)
  = 60n² - 90n.
```

It also proves this signature mass beats exact-Wick headroom `45n² - 40n` for every `n >= 4`.

## Validation

Passed:

```bash
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R312C3SignatureToMass.lean
```

No `sorryAx`; axiom audit is within the usual Lean foundations.

## Remaining target

The hard statement is now entirely finite-combinatorial:

```text
C3RelationWebSignature21:
  under the nondegenerate relation g^21 = 3, the only positive collision fibers have
  signatures (3n-3,3,1), (6,3,3), and (6,3), with multiplicities n, 2n, n(n-7).
```

R312 proves that this signature theorem would automatically refute the exact-Wick depth-3
input for all dyadic `n >= 4`.
