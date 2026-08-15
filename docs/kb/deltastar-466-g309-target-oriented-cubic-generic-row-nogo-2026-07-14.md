# G309: the target-oriented odd cubic normal needs genuine rank-row structure

Date: 2026-07-14
Issue: #466
Branch: `research/proximity-prize` only

## Verdict

The target-oriented odd cubic normal found by the Core lane is not a generic consequence of row
nonnegativity. On the exact proper dyadic cell `mu_8 <= F_73^*`, the nonnegative delta row
`R=1_{4}` has coefficient-two alignment `A_2(R)=-64` but odd cubic normal `L3odd(R)=73`.
Therefore

```text
L3odd(R) > 0  =>  A_2(R) > 0
```

is false for arbitrary nonnegative rows. The exact rank-five/rank-six census survivor is not
refuted: any proof for actual adjacent-rank subset-sum rows must use their extra arithmetic
structure. G309 is a depth-independent scope fence, not a production sign theorem and not prize
closure.

## 1. The target-oriented cubic normal

At sponsor two, `[2]` generates the odd quotient and the quotient order is divisible by three. This
orients the inversion-odd cubic weight before the rank row is observed:

```text
s3(j) = 0, +1, -1 according as j = 0, 1, 2 mod 3,
L3odd(R) = sum_j s3(j) A_[2]^j(R).
```

Unlike the generator-invariant real order-three trace closed by G306/G307, this normal uses the
actual target orientation. The fresh Core census found no cell with `A_2<0<L3odd` among 288 exact
rank-five/rank-six cells and no such violation among 110 negative-target rows in an all-rank stress.
That is evidence for a one-sided theorem on the specific subset-sum row class, not a theorem yet.

## 2. Exact generic-row countermodel

The Lean file defines

```text
H = {1,10,22,27,46,51,63,72} subset F_73,
W_a(t) = #{(y,z) in H^2 : a*y-z=t},
A_a(R) = 73*sum_t W_a(t)R(t) - 64*sum_t R(t).
```

The quotient classes are labelled by the powers

```text
[2]^j = (1,2,4,8,16,32,64,55,37),  j in Z/9Z.
```

For the pointwise nonnegative row `R=1_{4}`, kernel evaluation gives multiplicities

```text
(W_[2]^j(4))_j = (0,0,0,1,2,1,0,2,2),
```

hence exact centered alignments

```text
(A_[2]^j(R))_j = (-64,-64,-64,9,82,9,-64,82,82).
```

Thus `A_2(R)=-64`, while the odd cubic sum is

```text
(-64)-(-64) + 82-9 + 82-82 = 73.
```

Lean proves the actual finite-field sums, not merely a hard-coded sign record. The reproducibility
probe scans every delta row and finds eight counterexamples; residue four is the first.

## 3. Scope and surviving obligation

G309 closes only the implication from **generic row nonnegativity** to target sign. It does not close
the one-sided survivor on actual adjacent-rank rows. The remaining sponsor-two route now has two
honest obligations:

1. prove `L3odd(R_89)>0` from target-oriented cubic/Jacobi arithmetic at the production sponsor;
2. prove `L3odd(R_r)>0 => A_2(R_r)>0` using structure special to the subset-sum row.

A proof that treats `R` as an arbitrary nonnegative function is impossible by G309. A finite census
or a theorem restating either obligation as a hypothesis would not advance the frontier. CORE
remains open / on-BGK.

## Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G309TargetOrientedCubicGenericRowNoGo.lean`
- Probe: `scripts/probes/g309_target_oriented_cubic_generic_row_nogo.py`
- Ledger: `[466-G309-target-oriented-cubic-generic-row-nogo]`
