# #466 R369: fourth-power saddle recovery

## Prize-closing hypothesis under test

Let `H = mu_n` be a dyadic multiplicative subgroup of `F_p`, with `p >= n^4`, and put
`r_p = ceil(log p)`.  The surviving conjecture is the single-rung statement

```text
p E_rp(H) - n^(2 rp) <= p (2 rp - 1)!! n^rp.
```

This is exactly `DCEnergyBound H r_p`.  The in-tree theorem
`DCOptimized.eta_sq_le_dcOptimized` then gives

```text
max_(b != 0) |eta_b|^2 <= 2 e n ceil(log p).
```

Thus this is not a shallow energy target: it is the optimized square-root-cancellation rung
consumed by the proximity-prize analytic route.  At production scale `p ~ n * 2^128`,
`n <= 2^32` implies `p >> n^4`.

## Prove/refute loop

The initially stronger hypothesis, `DCEnergyBound H r` for every `r`, is false even above the
fourth-power frontier.  The complete R305 census gives

```text
n=32, p=21523361 > n^4: depth-3 excess = 58560,
centered depth-3 ratio = 1.027893... > 1.
```

The failure is shallow and then reverses.  Running

```text
python3 scripts/probes/probe_r369_fourth_power_saddle.py 32 21523361
```

gives ratios increasing through `r=7` (`1.0950`), crossing below one at `r=11`, and reaching
`0.2421` at the saddle `r=ceil(log p)=17`.  So the known fourth-power counterexample to the
full tower supports, rather than refutes, the one-rung saddle conjecture.

Additional falsification:

- exhaustive `n=4`, all 21 split primes in `[n^4,2n^4]`, through depth 30: no failure;
- exhaustive `n=8`, all 115 split primes in `[n^4,2n^4]`, through depth 30: no failure;
- exhaustive `n=16`, all 691 split primes in `[n^4,2n^4]`, through depth 17: no failure;
- twelve sampled `n=32` primes near `n^4`, through depth 25: no failure;
- `n=64, p=16777601`, the first split prime above `n^4`, through the saddle depth 17:
  ratios decrease from `0.98429` at `r=2` to `0.11947` at `r=17`.

The `n=64` exact grouped-shadow check also gives zero depth-3 excess at that prime.  Floating
FFT values are discovery evidence, not formal certificates.

## What a proof must exploit

The conjecture is weaker than the Paley-style full tower and survives sporadic low-weight
cyclotomic relations.  A proof may charge a relation web of multiplicity `M` against the
factorial growth of `(2r-1)!!` only at `r=ceil(log p)`.  This is the feature missed by every
fixed-depth resultant census: a web can violate shallow Wick while becoming harmless at the
saddle.  The next attack should bound the weighted generating function of relation modules
directly at this saddle, not coefficientwise at every depth.

No current published subgroup exponential-sum theorem proves this estimate.  It remains open
and is not claimed as prize closure.
