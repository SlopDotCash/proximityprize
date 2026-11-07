# The remaining open piece, isolated precisely: the decay law I(s,n,k) — partial structure (#407)

> **Scope correction (2026-10-28 audit, T48).** Read the claims below as finite evidence, with
> these qualifications:
> - The polynomial "laws" are fits. "EXACT cubic" for `k = 2` fits four values (`n = 16, 20, 24, 32`),
>   `~n⁴` for `k = 4` fits three, and "degree ≈ k+1" is a pattern, not a derivation. None of them is
>   a proved formula; "(all p-INDEPENDENT, proven)" is withdrawn.
> - The values are computed for `n`-th roots of unity in characteristic zero. Transferring them to
>   `F_q` needs a characteristic-transfer hypothesis. Newton's identities convert power sums into
>   elementary symmetric functions only when the relevant indices are invertible in the field, and
>   symmetric-function vanishing constraints can acquire extra solutions modulo `p`.
> - The far-line incidence object is not the MCA `δ*`. See the later correction
>   `farline-incidence-is-plotkin-proxy-not-mca-deltastar.md`, which also keeps `δ*` as an
>   interval. Three increasing rows at fixed `k = 2` and growing `n` also vary the rate, so they
>   do not settle a fixed-rate "floor direction".

The prize δ* (via the validated far-line incidence object) is now reduced to ONE clean combinatorial object:
the over-determined incidence decay law `I(s,n,k)`. Pinning it pins δ* exactly (and the Θ(1/log n) floor
correction). Partial structure established by the engine (all p-INDEPENDENT, proven):

## Top of the decay (s = k+2) — clean polynomial in n

- **k=2:** `I(s=k+2) = n³/32 + …` (EXACT cubic; fits 97,201,361,897 at n=16,20,24,32 perfectly).
- **k=4:** `I(s=k+2) ~ n⁴` (89,457,1441 at n=16,24,32).
- Degree of the polynomial in n grows with k (≈ k+1).

## The full decay (engine "curve" mode)

`I(s)` decays from this polynomial top (`~n^{k+1}` at s=k+2) through a gradual curve to a plateau `~2k+1` near
s~n/2. Examples (exact):
- n=16,k=2: 97 → 16 → 5 → 5 …  (s=4..)
- n=24,k=2: 361 → 71 → 40 → 24 → 18 → 15 → 15 → 5 …
- n=32,k=2: 897 → 90 → 25 → … (crosses budget=32 at s*=6)

## Why this pins δ*

`δ* = (n − s*)/n`, `s* = min{s : I(s,n,k) ≤ budget}`, budget = q·ε* = n. With the closed-form `I(s,n,k)` one
reads off `s*(n,k)` analytically (no enumeration) and hence δ*(n,k) exactly — including whether `s*−k ~
Θ(n/log n)` (⟹ δ* = floor `1−ρ−Θ(1/log n)`). The engine data shows δ* INCREASING toward `1−ρ` (k=2:
0.6875,0.7083,0.8125 at n=16,24,32), so the qualitative floor-direction is settled; the exact correction needs
the closed form.

## Status

**Isolated, not closed.** The remaining work is a single, well-defined combinatorial derivation: the general
`I(s,n,k)` (the top `I(k+2)` is a clean ~n^{k+1} polynomial; the decay-through-s and the budget-crossing s* are
the open parts). This is pure extremal combinatorics over n-th roots of unity — NO char-p, NO BGK, NO analysis.
The engine generates arbitrary exact `I(s,n,k)` data to fit and verify any conjectured closed form. NOT a
closure; the precise object that closes it is named and partially solved.
