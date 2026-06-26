# Issue #464: Tsang/Soundararajan high-moment range gate

Date: 2026-06-26.

Status: **range-gated**, not a delta-star proof.

External source: arXiv:2606.10242, "A Tsang-range high-moment bound for
`Im log L(1/2+it, chi)` under GRH" <https://arxiv.org/abs/2606.10242>.

## Thesis

arXiv:2606.10242 is a useful stress test because it is exactly the kind of recent
high-moment theorem that can look relevant to the #464 Paley wall.  Its abstract-level output is a
GRH-conditional Selberg-Tsang high-moment bound for fixed conductor and moments only in a
Tsang range:

```text
1 <= k <= K log log(qT).
```

The plain-RS prize needs a different object: worst-case dyadic Gauss periods over the finite-field
subgroup `mu_n`, with field size `q = n^beta` for fixed `beta` around 4 to 5, and moment/log-tail
control at the Paley saddle.  In the finite-field diagonal analogy, the range restriction is
schematically:

```text
n^(2r) <= q.
```

For `q = n^beta`, this forces `2r <= beta`.  That is constant depth at fixed polynomial exponent.
The prize saddle is growing-depth: `r` is on the order of `log q` or `log(q/n)`, not bounded by
`beta / 2`.

## Lean Surface

New in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D3TsangHighMomentRangeGate.lean`:

```lean
DiagonalRange
not_diagonalRange_at_poly_field_of_beta_lt_twice_depth
twice_depth_le_beta_of_diagonalRange_at_poly_field
diagonalRange_fails_at_depth_beta_plus
range_bound_does_not_control_next_depth
```

The key arithmetic statement is:

```text
q = n^beta and n^(2r) <= q  =>  2r <= beta.
```

So any theorem whose usable content is confined to the diagonal/Tsang range cannot by itself
reach the log-depth wraparound moment needed by the prize.  The countermodel theorem records the
logical gap: a statistic can be bounded on every admissible depth `r <= R` and still fail at
`R + 1`.

## Verdict

The Tsang/Soundararajan mean-value mechanism does not close the plain-RS floor as stated.  It is
valuable as a template for what a high-moment tail theorem should look like, but the load-bearing
upgrade would have to be a finite-field, subgroup-specific, beyond-diagonal wraparound estimate.

In other words: a winning variant cannot merely import a Tsang-range high-moment lemma.  It must
remove the constant-depth obstruction for `q = n^beta` and provide phase-sensitive control at the
Paley saddle.
