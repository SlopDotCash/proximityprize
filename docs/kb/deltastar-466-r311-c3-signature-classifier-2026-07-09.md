# #466 R311 — `c=3` relation-web fibers have only three count signatures

## Purpose

R310 confirmed the full `c=3` delta histogram at `n = 32,64,128`.  R311 refines that
histogram to the actual collision-fiber count signatures, which are closer to a Lean
combinatorial proof than raw deltas.

## Probe

New script:

```text
scripts/probes/probe_r311_c3_signature_classifier.py
```

It groups the R305 char-zero depth-3 shadow vectors modulo `p`, records each positive
collision fiber by the sorted list of representation counts in that fiber, and compares the
result to the predicted signature histogram.

Outputs:

```text
scripts/probes/_out_466_r311_n32_c3_signatures.txt
scripts/probes/_out_466_r311_n64_c3_signatures.txt
scripts/probes/_out_466_r311_n128_c3_signatures.txt
```

## Result

For all three tested dangerous `c=3` primes (`n=32,64,128`), the complete positive collision
fiber signature histogram is exactly:

```text
signature = (3n-3, 3, 1)   delta = 24n - 18   count = n
signature = (6, 3, 3)      delta = 90         count = 2n
signature = (6, 3)         delta = 36         count = n(n-7)
```

Concrete checks:

```text
n=32:
  (93,3,1) count 32; (6,3,3) count 64; (6,3) count 800
n=64:
  (189,3,1) count 64; (6,3,3) count 128; (6,3) count 3648
n=128:
  (381,3,1) count 128; (6,3,3) count 256; (6,3) count 15488
```

## Consequence

The missing proof target is sharper than R310:

```text
C3RelationWebSignature21:
  under the nondegenerate relation g^21 = 3, the only positive collision fibers have
  count signatures (3n-3,3,1), (6,3,3), and (6,3), with multiplicities n, 2n,
  and n(n-7), respectively.
```

R309 already proves this signature theorem would imply the exact-Wick depth-3 failure.  The
remaining problem is finite combinatorics of signed-basis 3-sum vectors, not numerical
estimation.
