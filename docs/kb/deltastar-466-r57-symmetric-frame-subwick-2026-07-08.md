# δ* #466 — symmetric-frame sub-Wick bypass refuted (2026-07-08)

## Hypothesis

The R25/R55 picture says the prize moment route needs a uniform sub-Wick bound for the nonzero
Fourier spectrum

```text
η_b(S) = sum_{x in S} e_p(bx),    b != 0.
```

Since `μ_n` is symmetric (`S = -S`), `η_b` is a sum of bounded real cosine variables.  A tempting
bypass was:

> Maybe every symmetric set `S = -S` has sub-Wick nonzero Fourier moments:
>
> `R_r(S) := Σ_{b≠0}|η_b|^(2r) / ((p-1)(2r-1)!!σ^(2r)) ≤ 1`.

If true, this would remove the special Paley/BGK input and replace it with a general
bounded-cosine/negative-dependence theorem.

Probe: `scripts/probes/probe_r57_symmetric_frame_subwick.py`.

## Result

The broad symmetric-frame theorem is **false**.

Exact full-spectrum computations:

| n | p | multiplicative subgroup R2/R3/R4 | best random symmetric R2/R3/R4 |
|---:|---:|---|---|
| 8 | 2017 | 0.8709 / 0.6569 / 0.4289 | 0.9968 / 0.8859 / 0.6794 |
| 12 | 2017 | 0.9031 / 0.8507 / 0.7669 | **1.5775 / 2.1549 / 2.4480** |
| 16 | 4129 | 0.9238 / 0.7653 / 0.5595 | **1.2386 / 1.6521 / 2.0556** |

Random symmetric super-Wick samples appeared already at `n=12` and `n=16`, and hill-climbing made
the violation large.

## Verdict

The sub-Wick law is **not** a generic consequence of symmetry, bounded cosine summands, or the
`S=-S` pairing.  The multiplicative subgroup's sub-Wick behavior uses real arithmetic structure:
cyclotomic/equidistribution constraints on the chosen symmetric set, not just negative dependence
of a cosine frame.

This refines the target:

* Dead route: prove sub-Wick for all symmetric sets.
* Live route: prove sub-Wick for multiplicative subgroups, or for a sharply characterized
  cyclotomic class excluding the random symmetric counterexamples.

So the R25 arcsine mechanism is the correct local model, but the global proof must still supply
the Paley/BGK-type uniformity that makes `μ_n` behave like that model at logarithmic depth.
