# #466 R309 — census badness vs the moment tower: two different scales (clarification round)

## Question

Does the depth-3 census badness (r304/r305: exact-Wick violations, ζ-relation webs) infect
the DC-subtracted moment TOWER (the WallHolds object) at higher depths?

## Probe (n=16, exact FFT moments, DC-dropped, r = 1..6)

A_r/(q·(2r−1)‼·n^r) for census-BAD primes (8929, 7873, 14401, 41521) vs clean primes of
similar size (8081, 12689, 40961):

```text
BAD   primes: r=6 ratio 0.385–0.408   (persistently ELEVATED at every depth)
clean primes: r=6 ratio 0.260–0.335
ALL sub-Wick through r=6; ratios monotonically decreasing in r.
```

Mechanism: the census badness is exactly a mildly elevated max frequency —

```text
B²/(n·ln p):  BAD 1.12–1.15   clean 0.91–1.03      (B = max_b |η_b|)
```

and a single frequency can NEVER cross the DC-subtracted Wick reference at any depth for
these primes: crossing needs B² ≳ (2r/e)·n growing with r, while observed B²/n ≈ 10–12 is
flat (log-space search to r=400: no crossing, all seven primes).

## Conclusions

1. **The r304 refutation and WallHolds are on different scales.** r304 killed the
   EXACT-CONSTANT depth-3 rung (C = 15 sharp); the tower needs only bounded-constant
   sub-Wick, which even census-bad primes satisfy comfortably at computable scales — the
   (2r−1)‼ headroom absorbs the O(1)-factor census effect.
2. **Census badness is a persistent per-prime spectral property**, visible at every depth
   as a uniform moment lift, with the clean discriminant `B² / (n·ln p)` (≈1.13 bad vs
   ≤1.03 clean at n=16). The depth-3 relation webs and the max-frequency elevation are the
   same phenomenon in two coordinates.
3. **Observed strength**: B² ≈ (0.9–1.15)·n·ln p across all tested primes — numerically the
   Paley-conjecture-strength bound B = O(√(n log p)), which is exactly the open prize-scale
   statement. The wall stays where it was: proving any such bound uniformly at n = 2³⁰,
   r ≈ ln q.

No wall contact; this round PREVENTS a wrong turn (trying to feed the census exclusion into
the tower, where it is not needed) and pins the correct discriminant for the good-prime
lane: the census governs exact-constant rungs; the tower's enemy is only the global
max-frequency scale. CORE OPEN, ON-BGK.
