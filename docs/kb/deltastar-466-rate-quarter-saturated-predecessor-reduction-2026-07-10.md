# Rate-quarter saturated predecessor reduction (2026-07-10)

## Status

Two axiom-clean counting results reduce the prospective matching lower bound
for the saturated P1 construction to one structural extraction problem.

The construction is bad at agreement threshold

```text
t = 592,794,965,
```

so the immediately smaller radius asks for agreement `t+1`.  A saturated
source core has size

```text
z = t-1 = 592,794,964,
6z = 53m-8,
n = 16m.
```

If every predecessor event can be assigned to a common-core polynomial source
pencil, the terminal count is now closed:

1. there are at most four saturated primitive source pencils;
2. every event needs at least two fresh coordinates beyond its core;
3. fresh petals for distinct scalars in one pencil are disjoint;
4. four such pencils carry at most `n` labels in total.

This does **not** yet prove the lower bound.  The remaining residual is to
extract those saturated common-core pencils from an arbitrary bad stack (or
to handle events whose maximal source core is smaller than `z`).

## 1. Integral five-core barrier

For five subsets `S_i` of an `n`-point universe, let `s_x` be the number of
sets containing coordinate `x`.  The integer inequality

```text
5 s_x <= s_x^2 + 6
```

is exact at multiplicities two and three.  Summing it and using the exact
first/second-moment identities gives

```text
4 sum_i |S_i| <= 6n + 20 lambda
```

when every distinct pair intersects in at most `lambda`.  Therefore five
cores of size at least `z` satisfy

```text
20z <= 6n + 20lambda.
```

At the saturated endpoint, `lambda=4m-2`; substituting `n=16m` and
`6z=53m-8` contradicts this inequality for `m>10`.  In a primitive collapsed
polynomial cluster, the factor root bound supplies exactly the pair cap.

The kernel theorems are

```text
fiveCore_integral_johnson
exists_pair_inter_card_ge_four_mul_sub_one_of_five
not_five_saturated_cores_in_primitive_cluster
```

in

```text
Frontier/_RateQuarterSaturatedFiveCoreBarrier.lean.
```

This improves the earlier quadratic Plotkin conclusion from at most five
source lines to at most four.  It is independent of the `mu_16` locator
pattern.

## 2. Four-cluster two-fresh capacity

For one source pencil with common core `D`, the existing line-core packing
theorem gives

```text
|Gamma| * max(1, T-|D|) + |D| <= n.
```

At the predecessor `T=t+1` and a saturated core `|D|=t-1`, so every label
uses at least two fresh coordinates:

```text
2|Gamma| + |D| <= n.
```

Also `z>n/2`.  Summing over four clusters yields

```text
2 sum_i |Gamma_i| + sum_i |D_i| <= 4n,
sum_i |D_i| >= 2n,
sum_i |Gamma_i| <= n.
```

This is formalized by

```text
fourCluster_label_card_le_universe
saturated_core_ge_half
fourSaturatedCluster_label_card_le
```

in

```text
Frontier/_RateQuarterPredecessorFourClusterCapacity.lean.
```

## 3. Exact remaining structural target

For a bad scalar `gamma` with decoded polynomial `q_gamma`, view

```text
z_gamma = (1, gamma, coefficients(q_gamma))
```

as the normal of a hyperplane containing the lifted coordinate rows

```text
ell_x = (-u0(x), -u1(x), 1, x, ..., x^(k-1)).
```

Nonjointness and a witness of size at least `k` make this normal unique.
Two events sharing at least `k` coordinates determine a polynomial source
line.  The live task is a rich-hyperplane/source-pencil decomposition showing
that more than `n` predecessor events force at most four pencils with common
cores of size at least `z`, or else that the nonsaturated remainder already
has at most `n` labels.  The two terminal counting lemmas above can then be
applied without further asymptotic or field arithmetic.
