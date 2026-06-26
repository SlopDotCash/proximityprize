# Issue #464: convolution-squaring bootstrap verdict

Date: 2026-06-26.

Status: **route reduced to the Paley starting estimate**, not a delta-star proof.

External source: arXiv:2606.24471, "Discrepancy for Random Linear Codes"
<https://arxiv.org/abs/2606.24471>.

## Thesis

The latest #464 paper sweep identified arXiv:2606.24471 as the strongest new-looking lead.  The
paper's useful mechanism is real: for a normalized test `f`, the mirrored self-convolution
`F_f = f * f̌` has Fourier coefficients whose magnitudes are squared, so an
`α`-Fourier-concentrated test becomes `α^2`-Fourier-concentrated, and after `d` iterations
becomes `α^(2^d)`-concentrated.  This is powerful for random linear codes because the relevant
test families start with a product-structure concentration parameter `α < 1`.

For the deterministic smooth-subgroup Paley core, however, the starting concentration is exactly the
unknown prize object:

```text
α = M(μ_n) / n,
M(μ_n) = max_{b ≠ 0} |Σ_{x∈μ_n} e_p(bx)|.
```

The desired floor estimate is precisely `α ≤ A`, where `A = Θ(√(log(p/n)/n))`.  Iterating
self-convolution changes this to `α^(2^d) ≤ A^(2^d)`, but on nonnegative reals that inequality is
equivalent to `α ≤ A`.  Thus the D1 bootstrap can amplify a known Paley-strength input; it cannot
produce that input for `1_{μ_n}/n`.

## Lean Surface

New in `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D1ConvolutionSquaringReduction.lean`:

```lean
squaredConcentration
squaredConcentration_le_iff
normalized_house_bound_iff
iterated_squared_bound_iff_house_bound
not_iterated_squared_bound_of_not_house_bound
```

The main theorem is:

```lean
iterated_squared_bound_iff_house_bound
```

It states that, for nonnegative `M` and target `A` and positive subgroup size `n`, the iterated
convolution-squared inequality

```text
(M / n)^(2^d) ≤ A^(2^d)
```

is equivalent to the original house bound:

```text
M ≤ n * A.
```

The contrapositive form records that if the Paley house bound fails, then every finite convolution
squaring depth fails at the correspondingly squared target.

## Why This Does Not Cross the Wall

The random-code paper's variance step is designed for a random construction sequence: smoothness for
`F_f` controls the next generator step for `f`.  The prize object is not a random code sampled by
adding random generators; it is a fixed explicit multiplicative subgroup in `F_p`.  The only way to
import the paper's squaring mechanism is to identify a base Fourier-concentration parameter for the
fixed test `1_{μ_n}/n`.  That parameter is `M(μ_n)/n`, so the base hypothesis is already the
Paley/BGK estimate in normalized form.

This is not a defect in arXiv:2606.24471.  It is a mismatch of primitives: the paper improves
discrepancy once pseudorandomness of the test family is known, while the RS floor needs a proof that
the smooth subgroup test is pseudorandom in the first place.

## Verdict

The convolution-squaring Fourier bootstrap is a valid consumer of a Paley-strength starting
estimate and a useful conceptual template for random-linear-code discrepancy.  For plain
smooth-domain RS, it does not bypass the wall: the starting `α` is exactly the normalized
Gauss-period house.  Any winning D1 variant must add an independent proof that
`1_{μ_n}/n` is already `O(√(log(p/n)/n))`-Fourier-concentrated, which is the original open core.
