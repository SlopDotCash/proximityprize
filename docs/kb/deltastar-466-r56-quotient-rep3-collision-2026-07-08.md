# δ* #466 — quotient-rep3 collision probe (2026-07-08)

## Hypothesis

Round 55 rewrote the depth-3 DC-subtracted energy as the variance of the representation
function

```text
rep3_G(c) = #{(x,y,z) in G^3 : x+y+z=c}.
```

Round 56 proved `rep3_G` is constant on multiplicative cosets when `G = μ_n`.  The bold
hypothesis tested here was:

> Maybe quotienting by `G` creates a genuinely low-collision object: the coset values of `rep3`
> might satisfy a stronger flatness law than the Gauss-period wall, giving a new route to the
> depth-3 Wick bound.

Probe: `scripts/probes/probe_r56_quotient_rep3_collision.py`.

## Result

Exact computations at Burgess-shape primes `p ≈ n^4`:

| n | p | max rep3 | collision surplus / n² | nonzero quotient cosets | R3 | n(1-R3) |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 4129 | 21 | 36.000 | 12 | 0.661921 | 2.705 |
| 16 | 65537 | 45 | 90.750 | 44 | 0.819325 | 2.891 |
| 32 | 1048609 | 93 | 202.125 | 172 | 0.906852 | 2.981 |

The R56 coset constancy check passed in every row.

## Verdict

The strong quotient-low-collision hypothesis is **refuted**.  The quotient lens is a correct
normalization, but the coset representation values are not low-collision enough to give a free
depth-3 proof: `max rep3` grows roughly linearly with `n`, and the collision surplus is large.

The positive information is that the same probe independently reconfirms the pair-collision law:

```text
R3 = 1 - 3/n + o(1/n).
```

So R55/R56 do not bypass the wall; they sharpen the right object.  The live hypothesis remains the
uniform sub-Wick / pair-collision law at growing depth, not a quotient combinatorial collapse.
