# Issue #466: anchor-failure regime scan — the crossover bump

Date: 2026-07-11 (UTC). Probe: `scripts/probes/probe_466_anchor_regime_scan.py`
(exact iterated-convolution energies; anchor ratio ρ(t) = q·E_t/(q·(2t−1)!!·n^t + n^{2t})).

## Data (all exact)

- n=16, e=3/4/5: ρ decreases monotonically in t (0.94 → 0.37); anchors comfortable.
- n=32, e=3 (crossover t≈5): dip then RISE — 0.751 (t4), 0.752 (t5), 0.833 (t6).
- n=64, e=2 (n ≈ √p, crossover t≈3): monotone rise to 0.9969 (t5), 0.9994 (t6) — grazing 1.
- n=64, e=3 (crossover t≈5): 0.882 (t4), 0.935 (t5), 0.980 (t6) — the bump again.
- n=64, e=4: the known FAILURE at t=5 (ratio 1.0124, prior falsification sweep).

## Findings

1. **The crossover bump is real**: ρ(t) rises toward (and past) 1 around each regime's
   crossover rung n^t ≈ q·(2t−1)!!, then the n^{2t} term rescues deeper rungs. All observed
   or near failures sit at the bump.
2. **At fixed regime exponent, ρ grows with n**: e=4, t=5: 0.51 (n=16) → 1.01 (n=64).
   This n-growth at the bump is the danger signal.
3. **Production sits at e ≈ 5.27 with its bump at t ≈ 5–6.** The small-n analogue rows
   (n=16, e=5: ρ₅ = 0.52) are comfortable, but the observed n-growth means the decisive
   empirical unknown for the whole campaign is: **does ρ₅(n, e ≈ 5.3) cross 1 as n grows
   toward 2^30?** A scan at n = 128/256 (e ≈ 5 downsampled primes, rungs 4–6, needs a
   compiled or numpy convolution) would give the trend's exponent; three data points
   (16, 64, 256) at matched regime would settle the direction.

## Reading for the campaign

Combined with the counterexample autopsy (disjoint census healthy, failure = crossover
descent): the census tower's deep family (t ≥ 11) has no evidence against it and sits far
from any bump; the production anchors at the bump (t = 5, 6) are where δ* will be won or
lost on this face. The HBK-regime tools (n = q^{0.19} ≪ q^{1/3}) apply exactly there.

## Honest scope

No failures found in this sample; small n; not a proof either way. CORE remains OPEN.
