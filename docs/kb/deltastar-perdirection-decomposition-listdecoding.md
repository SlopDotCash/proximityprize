# Structural advance: per-direction I_dir(s) is a clean step function; δ* = max far-line agreement (list-decoding radius) — #407

> **Scope correction (2026-10-28 audit, T48; see the banner in
> `deltastar-RESOLUTION-tracks-floor-not-half.md`).** The displayed identity
> `δ* = 1 − s*/n` with `s*` "the max agreement of a far monomial line" conflates two quantities. A
> budget crossing counts how many scalars attain each agreement threshold. That is not in general
> the deepest agreement attained by at least one scalar. The formula also covers only the monomial
> far-line family: an incidence upper-bound witness for that family does not prove extremality
> among all stacks, so it does not give the MCA `δ*`. The step profiles are finite exact data at
> `n = 24`, `k = 2`. As the later far-line guard says, `δ*` remains an interval, not a value.

The irregular envelope `I(s)` (361,71,40,24,18,15,15,5 …) that blocked the closed-form derivation is RESOLVED:
it is the **max over directions** of clean **per-direction** curves. Engine single-direction mode (`pg n k a b`).

## Per-direction I_dir(a,b;s) is a clean step function (n=24, k=2, exact)

```
dir (13,2): 361, 1,1,1,1,1,1,1,1, 0...   (sharp peak at s=k+2)
dir (10,3):  72, 71, 0...                (peak 72,71)
dir ( 9,4): HEAVY, 48, 40, 1,1, 0...     (HEAVY=saturated at s=k+2, excluded)
dir (21,4): HEAVY, 24,24,24, 0...        (plateau at 24 = n, then drops)
```

Each direction has a clean profile: a peak near s=k+2, then a constant plateau (often = n, one cyclic orbit,
since n | #bad), then 0. The irregular envelope `I(s) = max_{dir} I_dir(s)` switches which direction realizes the
max at each s.

## The binding = max far-line agreement (a list-decoding radius)

The binding direction (21,4) gives `I_dir = n` (exactly one γ-orbit) on a plateau s=5,6,7, then drops to 0 at
s=8. So **s\* = 7 = the largest agreement size at which ≤ n far-line scalars agree** — and:

> **δ\* = 1 − s\*/n,  s\* = max over far monomial lines `x^a+γx^b` of (max agreement with RS[μ_n,k])**
> = the **far-line list-decoding radius** (largest agreement achievable by a far line with ≤ budget scalars).

This is a much cleaner object than the raw envelope: δ\* is `1 − (far-line LD radius)/n`. The plateau value being
exactly `n` is the cyclic-orbit quantization (`n | #bad`, the dossier's E5 divisibility).

## Why this matters

- It **decomposes** the open decay law into per-direction step functions (clean) + a max envelope (the
  combinatorics is now "which direction's plateau extends furthest").
- It **reframes** δ\* as a far-line list-decoding radius — connecting directly to the GG25 curve-decodability /
  list-size program (the "MCA = line-decoding" framing a concurrent agent also reached).
- The remaining piece is sharp: **the max agreement s\*(n,k) of a far monomial line** = the longest n-plateau,
  = a Reed–Solomon list-decoding quantity for the specific 2-sparse-spectrum words `x^a+γx^b` over μ_n.

## Status

Real structural advance (per-direction decomposition + list-decoding reframing), engine single-direction mode
added. NOT a closure: `s*(n,k)` (the far-line LD radius) is still the open quantity — but it is now a clean
list-decoding question over roots of unity, not an irregular envelope. Engine generates exact per-direction data.
