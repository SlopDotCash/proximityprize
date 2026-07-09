# R344: High-level carré-du-champ hypothesis

## Nonlinear Markov form

Let `f` be the real period vector on `F_p^*/H`, and let `P` average over the
quotient classes `(r-1)H`, `r in H\{1}`.  The pointwise autocorrelation identity
is

```
f^2 = n + (n-1) P f
```

(up to the harmless `n-1` versus `n` normalization).  Define

```
Gamma(f) = P(f^2) - (P f)^2.
```

If `Gamma(f)=O(n)` on high superlevel sets and the walk has a sufficiently
strong one-sided entropy expansion, a self-bounding concentration argument
could control the maximum without estimating every raw moment separately.

## Exact spectral probe

`probe_r344_quotient_carre_du_champ.py` computes the complete period spectrum
by FFT and maps `H-1` to quotient indices using baby-step/giant-step.

| `(p,n)` | `max Gamma/n` | `Gamma(max |f|)/n` | max on `f >= 4 sqrt(n)` |
|---|---:|---:|---:|
| `(521,8)` | 4.624 | 0.120 | empty |
| `(100049,8)` | 7.545 | 0.001 | empty |
| `(1048609,16)` | 12.422 | 0.047 | empty |
| `(16777601,32)` | 10.781 | 0.328 | 0.454 |

The global `O(n)` carré-du-champ conjecture with a small absolute constant is
false.  The high-level version is strongly supported: conditional variance
falls rapidly with the period level, and is tiny at the actual maximizer.

## Remaining obstruction

At a maximum `M`, the fixed-point equation gives

```
P f approximately M^2/n.
```

For the desired extreme scale `M approximately sqrt(n log m)`, this neighbor
mean is only `log m`, far below `M`.  Thus an isolated extreme is compatible
with `Gamma(f)=O(n)`: its neighbors may remain ordinary `sqrt(n)`-scale values.
An ordinary spectral gap or local variance estimate cannot exclude that
configuration.

The live hypothesis must therefore combine high-level carré-du-champ with a
**one-sided no-isolated-spike expansion theorem** for the arithmetic walk.  A
usable form would show that whenever `f(i) >= t sqrt(n)`, a quantitatively large
set reached in a bounded number of reverse steps also has positive excess;
the exact global second moment would then cap `t` by `O(sqrt(log m))`.  Proving
that propagation, rather than the local variance estimate itself, is the new
mathematical target.
