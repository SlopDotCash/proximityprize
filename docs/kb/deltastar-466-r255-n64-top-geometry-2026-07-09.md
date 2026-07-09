# R255 n=64 top-representative geometry

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R254 refuted simple scalar classifiers of the `n=64` resonance family.  R255
checks the actual top quotient representatives for a low-dimensional geometry
signature: normalized quotient coordinate, signed representative size, cyclic
clustering, and inverse-near-pairing.

## Probe

New script:

```text
scripts/probes/probe_r255_n64_top_geometry.py
```

For selected `n=64` rows it reports:

```text
idx/M, normalized representative rep/p, signed rep/p,
inverse-index gap to the top set,
nearest top-index gap,
cyclic gap summary among top indices.
```

## Command

```bash
python3 -m py_compile scripts/probes/probe_r255_n64_top_geometry.py
python3 scripts/probes/probe_r255_n64_top_geometry.py --top 16 --chunk 8192
```

## Findings

No simple geometry classifier emerged.

The fatal large-index row `(p,M)=(697601,10900)` has visible arithmetic
spacing:

```text
top_idx_sorted:
886 905 930 1808 1827 2213 2666 2774 3696 4618 5540 5680 6602 8602 8666 10864

cycle_gaps:
19 25 878 19 386 453 108 922 922 922 140 922 2000 64 2198 922
```

The repeated `922` gaps look tempting.  But nearby bad/control rows show
different patterns:

```text
p=665857, M=10404:
  gaps include 1880, 852, 1028, 947, 224, 605, ...

p=421313, M=6583:
  gaps include 170, 737, 444, 786, 59, 1703, ...

p=355009, M=5547 control-ish:
  gaps include 41, 542, 101, 98, 1286, 147, ...
```

Inverse pairing is also inconclusive.  Some rows have near inverse misses, but
the top set is not closed under inversion and the inverse gaps do not isolate
bad rows from moderate controls.

## Route update

The `n=64` large-index obstruction is not explained by:

```text
simple M factorization/residue/square distance (R254),
or simple top-index clustering/inverse-near-pairing (R255).
```

The next realistic attack needs a richer decomposition of the `n=64` spectrum:

```text
character/factor decomposition by divisors of 64,
stationary-phase analysis of the top representatives,
or exact decomposition of the top spikes into lower-order period components.
```

In particular, the repeated-gap pattern in `(697601,10900)` may still be a clue,
but it is not a robust classifier by itself.
