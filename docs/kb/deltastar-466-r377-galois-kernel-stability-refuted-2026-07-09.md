# #466 R377: Galois kernel stability is refuted

## Hypothesis

R371--R372 proved that rotating exponent vectors preserves the fixed shadow-evaluation
kernel. If odd exponent multipliers also preserved it, a generic sparse relation would
carry an affine orbit of size about `n * phi(n)`, potentially supplying the missing second
factor of `n` in norm-sieve bad-prime counting.

## Refutation

The hypothesis is false in the smallest order-eight cell. In `F_17`, with `g=2`,

```text
g^1 + g^3 = g^0 + g^7,
```

but multiplying all exponents by the unit `3 mod 8` gives

```text
g^3 + g^1 != g^0 + g^5.
```

`_R377GaloisKernelStabilityRefuted.lean` verifies both statements by kernel reduction in
`ZMod 17`, with no axioms.

The conceptual reason is that `zeta -> zeta^a` is a Galois automorphism in characteristic
zero, while reduction at a selected root `g` chooses one prime ideal above `p`. The Galois
action moves that ideal. Translation is different: it merely multiplies a relation by
`g^b`, so it preserves the fixed kernel.

One can average over all prime ideals above `p`, but this relabels the same subgroup and
multiplies both the bad incidence and the ambient relation family by `phi(n)`. It gives no
net sieve saving. Therefore the unconditional orbit quantization available to the wall is
the rotation factor `n`, not `n*phi(n)`. The proposed affine-orbit closure route is dead.

The R369 saddle-only conjecture and its primitive-padding recovery remain unaffected.
