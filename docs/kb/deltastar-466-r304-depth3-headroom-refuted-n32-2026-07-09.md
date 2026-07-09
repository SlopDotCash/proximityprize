# #466 R304 — the r53 depth-3 headroom atom is REFUTED at n=32 (exact-Wick r=3 rung fails near β=3–3.5)

## The claim under test

r53 reduced the r=3 rung to the headroom atom: for all primes `p ≡ 1 (mod n)`, `p ≥ n³`,

```text
excess(p,n) = E₃(p,n) − (15n³ − 45n² + 40n)  ≤  45n² − 40n      (⇔ E₃ ≤ 15n³, exact Wick)
```

r52 had found bad primes with positive excess but reported them all "O(n²)-scale", leaving
the atom standing. R304 scanned EVERY prime `p ≡ 1 (mod n)` with `β ≥ 3` up to large bounds
(FFT computation of `q·E₃ = Σ_b |η_b|⁶`, validated bit-exact against the r52 integer probe
at n=16).

## Result: REFUTED at n=32

`scripts/probes/probe_r304_depth3_excess_exhaustive.py`. At `n = 32` (headroom
`45n²−40n = 44800`, Wick `15n³ = 491520`) there are MANY violating primes, starting at the
very bottom of the β ≥ 3 window and persisting past β = 3.5 — all re-verified with the exact
integer (bincount) method:

```text
                                                             raw          DC-subtracted
p=32993   β=3.002  E₃=838400  excess=391680 = 11.95·n³   E₃/Wick=1.706   (E₃−n⁶/q)/Wick=1.640
p=65537   β=3.200  E₃=703520  excess=256800              E₃/Wick=1.431   1.398   (Fermat prime!)
p=194977  β=3.515  E₃=636800  excess=190080              E₃/Wick=1.296   1.284
p=35393   β=3.022  E₃=492800  excess=46080 = 45n²        E₃/Wick=1.003   0.941   (DC artifact)
(19 raw violations total in p ≤ ~6.3·10⁵; none new after β≈3.52 so far)
```

**The r54 DC-caveat does NOT rescue the atom**: subtracting the DC floor `n⁶/q` leaves the
strong violations intact (1.64× / 1.40× / 1.28× Wick). Only the weak `45n²`-level raw
violations (e.g. p=35393) are DC artifacts in the sense of r54.

Two corrections to the r52 record:

1. **The excess is NOT O(n²)-scale at bad primes**: `excess = 11.95·n³` at p=32993 — the
   n³-scale is reached, so `E₃ ≤ C·n³` survives only with C ≈ 26 at n=32, not C=15.
   The EXACT-Wick rung (the input the r53→r54 chain feeds on) is false as a universal
   statement over `β ≥ 3`.
2. **The failure is n-INVERTED**: at n=8 the full window `β ∈ [3, 6.64]` has excess
   IDENTICALLY 0 (all ~19.5k primes); at n=16 the worst excess is 1920 = 17.6% of headroom
   (all β ≥ 3, no violation); at n=32 the atom fails by 8.7×. Growing n makes it WORSE —
   the wrong direction for prize uniformity (n = 2³⁰).

## Surviving structure (kept for the next round)

- **Quantization law (observed)**: every nonzero excess at BOTH n=16 and n=32 is an exact
  multiple of **480** (n=16: 480·{1,2,4}; n=32: 480·{96,104,396,404,535,816}) and the most
  common violating level is exactly `45n²` (= 46080 = headroom + 40n at n=32). The excess
  appears to count exceptional wraparound solution orbits at a fixed quantum.
- **Norm-bound mechanism (theory, matches data)**: a wraparound solution forces a nonzero
  6-term ±sum `z` of n-th roots of unity with `p | Norm(z)`, and `|Norm(z)| ≤ 6^φ(n)`. Hence
  excess ≡ 0 for `p > 6^φ(n)` — at n=8 that is p > 1296 ≈ immediate (observed: zero
  everywhere), at n=16 p > 6⁸ ≈ 1.7·10⁶ (observed: zero above 45k already), at n=32 the
  bound allows bad primes to 6¹⁶ ≈ 2.8·10¹² (β ≈ 8.26) — whether violations of exact Wick
  persist to prize-relevant β ≈ 5.3 is the R305 question (norm-divisor census).

## Consequence for the moment route

The depth-3 rung of the tower CANNOT be closed as `E₃ ≤ 15n³` uniformly over `β ≥ 3`; it
needs either (a) a β-floor above the norm frontier (fixed n: true but useless at n = 2³⁰
where 6^φ(n) is astronomically ≫ q), (b) constant inflation `C > 15` (compounds fatally as
C^r up the tower), or (c) bad-prime EXCLUSION — which re-routes the lane into the
floor-bad/good-prime-selection surface (Tier-1 item 4). The variance/orbit machinery
(r55–r303) is unaffected: it bounds level-sets GIVEN an energy bound; the refutation is of
the specific exact-Wick energy input. CORE OPEN — this round SHARPENS the wall's location.

Probe outputs: `scripts/probes/_out_466_r304_n{8,16,32}.txt`.
