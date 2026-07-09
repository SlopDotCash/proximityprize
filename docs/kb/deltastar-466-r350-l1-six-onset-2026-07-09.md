# #466 R350 — the n=64 bad endpoint begins at L1 six

At `p = 16,778,497`, random exact 8-term collision sampling followed by
antipodal reduction produced the endpoint-L1 distribution

```text
L1 = 0 : 1,221,093   (trivial antipodal collisions)
L1 = 6 :    81,684
L1 = 8 :    65,317
```

No nontrivial L1-2 or L1-4 relation was found. The latter is exhaustive from
the pair-sum census: `μ₆₄` has no non-antipodal 4-term relation. The first
nontrivial web therefore begins at L1 six, even though the depth-four energy is
K-bad.

For `r = 4`, the identity `endpointL1 = 2r - 2s` means L1 six corresponds to
`s = 1`; all higher-weight strata `s ≥ 2` would be empty under the exact
4-Sidon-to-L1-six implication. This is a concrete target for formalization:
prove that 4-Sidonness eliminates the `s ≥ 2` R324 strata, then bound only the
low-weight L1-six web. It does not solve the all-rung wall, but it converts the
observed bad endpoint from an unrestricted `m^3` envelope to a potentially
linear-in-`m` web at the first bad rung.
