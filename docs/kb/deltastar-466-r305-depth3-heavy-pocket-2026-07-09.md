# #466 R305 — depth-3 exact-Wick failure localizes to a low-beta heavy pocket at n=32

## Question

R304 refuted the r53 exact-Wick depth-3 headroom atom at `n = 32`: several primes
`p ≡ 1 (mod 32)`, `p ≥ n^3`, have

```text
excess(p,n) = E_3(p,n) - (15n^3 - 45n^2 + 40n) > 45n^2 - 40n,
```

so `E_3(p,n) ≤ 15n^3` is false as a universal `β ≥ 3` input. The next question is whether the
failure is a persistent high-beta obstruction or a low-beta heavy pocket.

## Exact scanner used

`scripts/probes/probe_r305_fast_excess_scanner.py` computes the same depth-3 excess exactly by
grouping the char-0 3-sum vectors:

```text
excess(p,n) = sum_c rep3_p(c)^2 - sum_w N3(w)^2.
```

For `n = 32`, the char-0 histogram has `K = 5504` exact vectors and
`E_3^char0 = 446720`; the exact-Wick headroom is `44800`.

## New scan

Commands:

```bash
python3 scripts/probes/probe_r305_fast_excess_scanner.py \
  --n 32 --min-p 2000001 --max-p 5000000 --progress-every 2000

python3 scripts/probes/probe_r305_fast_excess_scanner.py \
  --n 32 --min-p 5000001 --max-p 20000000 --progress-every 10000
```

Results:

```text
[2,000,001, 5,000,000]:
  primes scanned:       12452
  nonzero-excess:          65
  exact-Wick violations:    0
  observed excess quanta: mostly 3840, 5760, 11520

[5,000,001, 20,000,000]:
  primes scanned:       57645
  nonzero-excess:          54
  exact-Wick violations:    0
  observed excess quanta: 960, 1920, 3840, 5760
```

Combined with R304:

```text
[32^3, 2,000,000]:
  primes scanned:        9088
  exact-Wick violations:   19
  largest violation: p=32993, excess=391680 = 8.74 * headroom
  last violation seen: p=194977, beta=3.515

[2,000,001, 20,000,000]:
  primes scanned:       70097
  exact-Wick violations:    0
  nonzero excess persists but stays <= 11520 = 0.257 * headroom
```

## Interpretation

The naive repair "all wraparound excess disappears above the first pocket" is false:
nonzero excess persists at least through `p = 19,894,753` (`β = 4.849`).

The weaker and more useful repair survives this stress:

```text
Depth3HeavyPocket32:
  for n = 32, all exact-Wick headroom violations are confined to a low-beta pocket
  near beta <= 3.52, while high-beta wraparound is light and quantized.
```

This does not close the moment route. It says the r53 atom failed for a reason more structured
than "depth 3 is globally too large": heavy collision classes appear only at small primes; later
bad primes carry small class mass. A plausible next theorem shape is therefore not
`excess = 0`, but a **mass-filtered norm-divisor classification**:

```text
HeavyDepth3ClassBound(n):
  if a depth-3 difference class carries mass > 45n^2 - 40n, then every prime
  p ≡ 1 (mod n) killing that class lies below an explicit low-beta norm frontier.
```

At prize scale this would still be far from enough by itself, because the real wall needs
log-depth DC-subtracted control, not one fixed rung. But it is a sharper local obstruction map:
exact Wick is false, persistent wraparound is real, and the dangerous part seems carried by a
finite heavy-class pocket rather than by the high-beta dust.

## Status

No closure claimed. This is exact empirical evidence for the depth-3 subproblem and a new
candidate classification target. The slow full norm-spectrum script
`probe_r305_depth3_excess_classification.py` was started for `n = 32` but stopped because its
Python difference-class loop is too slow (`5504^2` tuple updates). A vectorized/heavy-class-only
norm census is the natural next probe.
