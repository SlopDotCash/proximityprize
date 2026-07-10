# Issue #466 R393: primitive/antipodal four-fiber decomposition

Date: 2026-07-09

R393 defines the antipodal cover as all 24 coordinate permutations of

```text
(x,-x,u,v),  x in G,  u+v=c,
```

and defines `primitiveFourFiber` by removing that cover from the full four-fiber. It proves

```text
rep4(c) <= primitive4(c) + 24*|G|*rep2(c).
```

Consequently

```text
primitive4(c) <= A|G|  and  rep2(c) <= B
  => rep4(c) <= (A+24B)|G|.
```

The factor 24 ignores overlaps and is not intended to be sharp. The theorem cleanly separates the
finite-characteristic switching problem into a constant pair-fiber theorem and a linear primitive
torsion-surface theorem.
