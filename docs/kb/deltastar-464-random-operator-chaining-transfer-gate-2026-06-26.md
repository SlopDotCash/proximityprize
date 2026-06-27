# Issue #464: random-operator / chaining transfer gate

Date: 2026-06-26.

Status: **transfer-gated**, not a delta-star proof.

External source: arXiv:2606.19075, "Random Schrödinger operators on manifolds and abstract bounds
for multiplier-type operators" <https://arxiv.org/abs/2606.19075>.

## Thesis

The random-operator / generic-chaining lead is attractive because its native output is an operator
norm or supremum, not a second moment.  The cited paper proves that randomization can improve
deterministic multiplier-type operator norm bounds and yield square-root cancellation gains in
random Schrödinger settings.

For #464, the target is not a randomized coefficient vector.  It is the fixed deterministic
process

```text
eta_b = sum_{x in mu_n} psi(bx)
```

over the quotient index set `F_p^*/mu_n`.  The issue's latest experiments say this process looks
independent-Gaussian-like, not log-correlated.  That is exactly the right shape for the floor, but
the proof still has to certify the deterministic tail/increment input.

The transfer gate is therefore:

```text
random model norm bound
  -> fixed smooth-domain period bound
```

only if one proves either

```text
detStat(d) <= modelStat(pull(d))       for every deterministic instance d
```

or a bad-event cover saying every deterministic spike is represented by a model spike.

Without one of these, the random model can be uniformly bounded while the designated smooth
instance carries a spike.

## Lean Surface

New in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_D5RandomOperatorChainingTransferGate.lean`:

```lean
deterministic_bound_of_pointwise_domination
no_deterministic_bad_of_bad_event_cover
bounded_random_model_does_not_bound_fixed_instance
no_model_bad_does_not_exclude_uncovered_deterministic_bad
```

The positive lemmas record the two legitimate transfers: pointwise domination and covered bad
events.  The countermodels record the trap: a bounded random/operator model, or even an empty model
bad set, says nothing about an uncovered deterministic smooth-domain instance.

## Relation To Existing Chaining Notes

This complements the existing I031/dilation quotient lesson.  The quotient index set has the right
entropy scale `log(p/n)`, but the metric is empirically flat, so Dudley/Talagrand reproduces the
union-bound-sized floor once a sub-Gaussian marginal/increment theorem is available.  The entropy
calculus is not the missing mathematics.  The missing mathematics is the deterministic
sub-Gaussian tail for the actual Gauss-period field at depth `r ~ log q`.

## Verdict

Random multiplier and chaining technology remains a good language for the desired proof, but it
does not close the plain-RS floor by itself.  A winning variant must prove the deterministic
coupling/sub-Gaussian input for `eta_b`; otherwise the random theorem is only an adjacent model
with the right heuristic shape.
