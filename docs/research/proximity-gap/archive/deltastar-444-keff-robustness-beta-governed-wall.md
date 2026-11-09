# #444 K_eff robustness at fixed beta — the energy-transfer floor REDUCES TO THE BGK WALL

**Date:** 2026-06-17
**Probe:** `scripts/probes/probe_keff_robust_scale.py` (machine-checked, EXACT energy over
proper `mu_n`, self-test = methods match exact integer enumeration to <1e-9 and char-0 anchor
matches `3n^2-3n`, `15n^3-45n^2+40n`).
**Verdict:** the "K_eff = (E_r/Wick)^{1/r} bounded, antitone, structured-prime-robust at
beta=4" hope is **REFUTED as the basis for the prize**. K_eff is bounded only in a *shallow*
window `r <~ r*(beta)`; the prize needs `r ~ ln p ~ 89-110`, and `r* << r_prize` with the gap
*widening* as `n -> 2^30`. The energy-transfer floor reduces to exactly the BGK / deep-moment
defect wall, not a free K=O(1).

## What was claimed (the hopeful pivot)

`K_eff = (E_r / Wick)^{1/r}` (Wick = `(2r-1)!! n^r`) is `~0.6` vs Wick / `<=1.10` vs exact
char-0, **bounded, antitone in r, structured-prime-robust** (hi-v2 / rough <= generic) for
`n=16..256` at the TRUE `beta=4`; the Fermat `K=2.28` inflation was a sub-prize (`beta~3`)
artifact gone once `p>n^4`. If true uniformly to `r ~ ln q`, the transfer
`E_r <= K^r * Wick` holds and the prize floor is TRUE.

## What the exact energy actually shows (proper mu_n, beta held at 4)

`E_r` computed EXACTLY two ways (full length-p FFT for n<=64; Gauss-period coset sum
`E_r=(n^{2r}+n*sum eta_c^{2r})/p` for n>=128). `K_eff(0)=(E_r/E_r^char0)^{1/r}` is the
faithfulness ratio (>1 = char-p energy EXCEEDS char-0 = defect).

| n   | p (generic, beta=4) | r*(E/E0>1.1) | r*(E/E0>1.5) | K_eff(0)@r=8 | E_r/E0 @ r=8 |
|-----|---------------------|--------------|--------------|-------------|--------------|
| 16  | 65537               | 8            | none(<=9)    | 1.012       | 1.10         |
| 32  | 1048609             | 6            | 8            | 1.107       | 2.18         |
| 64  | 16777601            | 6            | 6            | 1.391       | 14.0         |
| 128 | 268437889           | 5            | 6            | 1.895       | 166.0        |

Two facts kill the hope:

1. **NOT antitone past the onset.** K_eff(W) turns around and grows once `r > r*`; at n=128
   it reaches `1.84` by r=8 (E_r/Wick = 133x). The antitone claim holds only for `r <= r*`.
2. **The deep-r defect CREEPS UP with n at FIXED beta** (K0@r=8: 1.012 -> 1.107 -> 1.391 ->
   1.895). It does NOT saturate near 1.1; it diverges. Reason: phi(n)=n/2 grows, the config
   variety V_r gains components, char-p sparse-relation count mod p grows.

## The onset is beta-governed; the gap to the prize WIDENS

- **Fixed beta=4, grow n:** onset `r*` *shrinks* (8->6->6->5) while needed depth `ln p` grows.
- **Fixed n, grow beta:** onset `r*` *grows* (n=16: beta3->r*=5, beta4->r*=8, beta>=5->no
  defect within r<=14). So larger p clears more short relations (consistent with the
  Mahler/norm threshold `defect=0 for p>(2r)^{phi(n)/2}`).
- **Prize-consistent (index ~ 2^16 fixed, n grows so beta -> 1+):** `r*/ln p` shrinks
  monotonically `0.481 -> 0.328 -> 0.251` (n=32,64,128). Because the prize index `2^128`
  dominates, `beta = 1 + 128/log2(n) -> 1` as `n -> 2^30`, which CRUSHES `r*` toward O(1)
  while the moment depth `r_prize ~ ln p ~ 89-110` stays large. The faithful window covers a
  *vanishing fraction* of the required range.

## Structured-prime axis: robust, but irrelevant

high-v2, rough-index, smooth-index, near-Fermat primes at beta=4 give K_eff(0) curves
*identical to generic* (n=128: all four within 1e-3 of generic at every r). So "structured
<= generic" is CONFIRMED in the weak sense (structure doesn't inflate). But this is not the
hoped relief: the defect is **depth-vs-beta driven, universal across prime arithmetic**, not a
bad-prime artifact one can argue away. The Fermat K=2.28 really was a low-beta artifact — but
the wall it pointed at (deep-r defect) is real and reappears at any beta once r exceeds r*.

## Bottom line

`E_r <= K^r * Wick` with absolute `K=O(1)` holds empirically ONLY for `r <~ r*(beta) ~ O(beta)`
= the SHALLOW band. The prize moment method needs it to `r ~ ln p`. At the genuine regime
(`p ~ n*2^128`, beta -> 1+, n -> 2^30), `r* / r_prize -> 0`. The energy-transfer reduction is
therefore NOT a free win: it is *exactly* the deep-moment / BGK char-p defect wall
(= #{sparse signed mu_n relations vanishing mod p but not in char 0}), re-expressed in K_eff
language. This independently re-confirms [[deltastar-444-evenodd-descent]] and the
`WF407_DeepMomentDefectWall` / `MomentMethodPrizeDepthNoGo` no-go from the energy-ratio angle,
and adds the precise scaling `r* ~ O(beta)`, `r*/r_prize -> 0`.

No closure, no refutation of the prize — an honest **reduces-to-wall** localization with the
machine-checked scaling law that makes the wall quantitative.
