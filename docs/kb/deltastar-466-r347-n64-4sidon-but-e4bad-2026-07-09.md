# #466 R347 — the first n=64 K-bad endpoint is 4-Sidon

For `p = 16,778,497` and `H = μ₆₄`, exhaustive pair-sum enumeration finds no
non-antipodal collision

```text
x_i + x_j = x_k + x_l,
```

with unordered pairs distinct. The only repeated pair sums are the trivial
zero/antipodal family. Thus `H` is 4-Sidon in the relevant sense.

Nevertheless the exact four-sum energy is K-bad:

```text
E4^0 = 1,602,260,800
W4  = 13,547,520
A4/E4^0 = 1.0591...
```

This rules out a proof architecture that classifies only support-4
cyclotomic relations. The excess first appears as an 8-variable collision web
(four subgroup elements on each side), compatible with complete absence of
nontrivial 4-term relations. R324’s cancellation-depth stratification is the
correct abstraction: the proof must bound weighted higher-order fibers, not just
the minimal relation support.
