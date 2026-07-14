# G297: dilation anchors form a coset-constant zero-sum family

Date: 2026-07-13 MDT / 2026-07-14 UTC. Issue #466 CORE. Branch `research/proximity-prize` only.

## Mechanism tested

For an order-`n` subgroup `G <= F_p^*`, put

```text
W_a(t) = #{(y,z) in G^2 : a*y-z=t},
A_a(R) = p * sum_t W_a(t) R(t) - n^2 * sum_t R(t).
```

For `a != 0`, `W_a(t)=|aG intersect (G+t)|`. The target CORE coefficient is `a=2`. The only
canonical comparison anchor with stronger internal structure is `a=1`, where `W_1` is the subgroup
difference autocorrelation. A transport from this anchor would have to control

```text
A_2(R)-A_1(R) = p * sum_t (W_2(t)-W_1(t)) R(t).
```

The question is not whether each intersection profile is small. It is whether two distinguished
coefficient cosets have a signed relative placement against the rank-labelled row.

## Unconditional structure

The new formal payload proves three identities over every finite field and every finite
multiplicative subgroup `H <= F^*`.

### 1. Coset constancy

For every `u in H`, multiplication by `u` reindexes the `y` variable:

```text
W_{a*u}(t) = W_a(t),
A_{a*u}(R) = A_a(R).
```

Thus the nonzero coefficient family factors exactly through `F^*/H`. Anchor selection is quotient
coset selection.

### 2. Pointwise coefficient conservation

For fixed `t`, every pair `(y,z) in H^2` determines the unique coefficient
`a=(t+z)/y`. Therefore

```text
sum_{a in F} W_a(t) = |H|^2.
```

This is an exact double count. It uses no character estimate, moment bound, or census assumption.

### 3. Zero-sum centered family

Substituting the preceding identity into the centered alignment gives

```text
sum_{a in F} A_a(R) = 0
```

for every integer row `R`. Consequently, if the full coefficient family is not identically zero,
some coefficient has positive alignment and another has negative alignment. This includes the
separate coefficient `a=0`, which may carry one of the signs. The formal payload therefore also
proves the precise nonzero-family identity

```text
sum_{a != 0} A_a(R) = -A_0(R).
```

The nonzero values factor through `F^*/H`, but they are not claimed to have zero sum by themselves.
These identities sharpen the binding obstruction without that overclaim. A theorem transporting
`A_1` to `A_2` must identify where the two distinguished nonzero coefficient cosets sit inside the
signed family. That is the missing row-placement information itself.

## Exact distinguished-coset refutation

The self-contained pure-integer probe `scripts/probes/g297_dilation_anchor_nogo.py` computes the
proper subgroup `G=mu_16 <= F_113^*`, every coefficient profile `W_a`, and the adjacent-rank rows
without FFT or floating point. It verifies the structural identities pointwise and obtains

```text
r=5: A_1=-2,977,296, A_2=+1,727,120, A_2-A_1=+4,704,416;
r=6: A_1=  +152,176, A_2=   -77,440, A_2-A_1=  -229,616.
```

For the complete coefficient family:

```text
r=5: sum_a A_a=0, range [-2,977,296, +6,657,536], seven nonzero coefficient cosets;
r=6: sum_a A_a=0, range [  -265,472,   +152,176], seven nonzero coefficient cosets.
```

Thus one field and one subgroup refute both possible rank-uniform sign transports. The deformation
changes sign between adjacent ranks and exceeds the anchor margin in the sign-changing direction
each time. The committed probe reproduces this two-way reversal directly from integer subset-sum
histograms and all coefficient profiles, without FFT or floating point.

## Literature and asymptotics

Shkredov and Vyugin, *On additive shifts of multiplicative subgroups* (arXiv:1102.1172), and related
Stepanov intersection estimates control nonnegative intersections of multiplicative cosets with
additive shifts. Such bounds act on individual `W_a(t)` values or their marginal energies. The
coset-constant zero-sum theorem shows why this does not transport the CORE sign: the coefficient
family is forced to be sign-balanced after pairing with `R`, and selecting the sign of the `a=2`
coset requires the fine labelled placement discarded by uniform intersection bounds.

At sponsor scale, improving a pointwise exponent leaves the exact deformation identity unchanged.
Even perfect separate control of `W_1` and `W_2` does not bound
`sum_t (W_2-W_1)R_r`. A successful comparison needs a signed theorem for that row-labelled pairing,
which is the BGK/Paley covariance in difference form.

FS15-FS18 are fully consumed:

- FS15 proves fixed-depth Wick magnitude at FS-good primes.
- FS16 gives the sharp per-configuration resultant envelope `(2r)^(n/2)`.
- FS17 unions finitely many depth bad sets.
- FS18 classifies odd vanishing and even Wick behavior on the same good set.
- G64 forces the sponsor exceptional by depth six.

These results do not choose the sign-bearing coefficient coset at the explicit sponsor prime, and
they do not estimate the in-window production row `r*=89` established by G299.

## Formal payload and scope

`Frontier/_G297DilationAnchorNoGo.lean` proves:

- `weightedKernel_mul_right` and `anchorAlignment_mul_right`, the unconditional coset laws;
- `sum_weightedKernel`, the pointwise coefficient conservation identity;
- `sum_anchorAlignment`, the exact full-family zero sum;
- `sum_nonzero_anchorAlignment`, the exact nonzero-family sum `-A_0`;
- `zero_sum_nonzero_has_both_signs` and `anchor_family_has_both_signs`, explicitly including `a=0`;
- the exact `F_113`, ranks 5 and 6, two-way transport reversal.

All audited declarations use only `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`,
custom axiom, or native-decision axiom.

This closes coefficient-anchor transport as a shortcut. It does not estimate either production
sponsor covariance. The live object remains the direct row-labelled full-family covariance at the
actual in-window production depth. CORE remains OPEN / ON-BGK.
