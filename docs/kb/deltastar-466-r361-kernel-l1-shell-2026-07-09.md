# #466 R361 — the bad endpoint kernel has a 40-vector L1-six shell

Let

```text
L_p = { d ∈ Z^32 : Σ_{j<32} d_j g^j = 0 (mod p) },
```

where `g` is the folded order-64 subgroup generator at
`p = 16,778,497`. Exact enumeration of reduced signed multisets gives:

```text
nonzero L1-2 vectors : 0
nonzero L1-4 vectors : 0
nonzero L1-6 vectors : 40
```

Thus the first successive minimum of the evaluation kernel in the relevant
L1 geometry is exactly six. The 640 genuine collision pairs from R358 are
weighted realizations of these 40 reduced kernel vectors; collision multiplicity
is not the same thing as lattice-vector count.

This is the cleanest finite target extracted so far for R322: prove a bound on
the number and weighted return mass of the first short-vector shell of the
prime-ideal lattice, then iterate across shells. It avoids both raw template
enumeration and the false assumption that the first shell is absent.
