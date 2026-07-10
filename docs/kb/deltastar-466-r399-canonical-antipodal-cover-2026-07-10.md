# Issue #466 R399: canonical antipodal cover and the direct-four-fiber pivot

R393 originally bounded its antipodal cover using all 24 coordinate permutations. Swapping the two
residual coordinates and swapping the ordered residual pair leaves the inserted tuple unchanged.
Choosing the canonical representative with `sigma^{-1}(2)<sigma^{-1}(3)` leaves exactly 12
permutations. Lean now proves

```text
card(antipodalCover G c) <= 12*|G|*rep2(c).
```

Consequently `PrimitiveFourBoundNine` plus `PairMultiplicityEight` implies the exact R390 constant
`rep4(c)<=105|G|`, since `9+12*8=105`. Both the canonical-cover theorem and corrected consumer are
axiom-clean.

The producer hypothesis is nevertheless false: `n=256`, `p=67280421310721` has `rep2(2)=9` above
the quartic threshold. Exact convolution still gives `rep4(1)=rep4(2)=24865<105*256`. Therefore
the canonicalization is a valid strengthening, but the next proof must attack the four-fiber
directly. Pointwise pair multiplicity loses compensating overlap that is visible in the full
four-fold convolution.

The relevant primary literature confirms this distinction: Heath-Brown and Konyagin's shifted
subgroup bound is `O(|G|^(2/3))`, not constant, while the observed direct four-fiber remains linear.
