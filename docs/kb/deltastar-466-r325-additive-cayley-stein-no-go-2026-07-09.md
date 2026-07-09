# R325 additive-Cayley Stein route: exact regression, exact obstruction

## Candidate

For a multiplicative subgroup `G <= F_p^*`, let

`X(b) = sum_{x in G} exp(2 pi i b x / p)`.

Choose `B` uniformly in `F_p`, choose `T` uniformly in a symmetric coset
`aG`, and put `B' = B + T`.  The pair is exchangeable and has exact linear
regression

`E[X(B') | B=b] = c X(b)`, where `c = X(a)/n`.

This is a genuinely additive coupling, distinct from the previously tested
multiplicative permutation coupling.

## Pointwise proxy identity

Writing `P` for averaging over `aG`, the conditional squared jump is

`J(b) = P(X^2)(b) + (1 - 2c) X(b)^2`.

There is always a coset with `X(a) <= 0` because the nonzero periods have
negative total sum. For that choice, `-1 <= c <= 0`, hence

`V(b) := J(b)/(2(1-c)) >= X(b)^2/2`.

Consequently, a pointwise Chatterjee/Stein hypothesis `V <= C n` implies the
strictly stronger square-root bound `|X| <= sqrt(2Cn)`.  A hypothesis
`V <= C n log p` already contains the desired prize-scale estimate. The
conditional variance cannot be bounded independently of the period maximum.

The abstract implication is machine checked in
`_R325AdditiveCayleySteinNoGo.lean` with no axioms or placeholders.

## Numerical falsification pressure

`probe_r325_additive_cayley_stein.py` verifies exact regression to floating
error and computes the proxy at every state. Representative maxima of `V/n`
were:

| `(n,p)` | `max V/n` | `max |X|` |
|---|---:|---:|
| `(16,65537)` | 1.606 | 13.838 |
| `(32,1048609)` | 9.190 | 22.983 |
| `(32,1439393)` | 8.634 | 25.472 |
| `(64,100609)` | 9.184 | 35.218 |
| `(128,103553)` | 6.290 | 38.244 |

The worst nonzero state is generally an extremal period, not a transition
that hits the excluded DC point. This matches the exact lower bound above.

## Verdict

**Refuted as an independent route.** The additive coupling supplies exact
regression for free, but its pointwise variance certificate algebraically
contains the target maximum. Any successful use would need a new cancellation
principle for `P(X^2)` that simultaneously defeats the explicit `X^2` term;
that is another encoding of the original archimedean cancellation wall.
