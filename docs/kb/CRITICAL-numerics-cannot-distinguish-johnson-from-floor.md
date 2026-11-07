# CRITICAL meta-finding: far-line δ* numerics CANNOT distinguish Johnson from the floor at any feasible n — #407

> **Scope note (2026-10-28 audit, T48).** The retraction of universal asymptotic claims from tiny
> data is correct. The note's own impossibility claim is too strong, though.
> - "Cannot distinguish … at any computationally feasible n" is an estimate of the cost of
>   brute-force enumeration. It does not prove that no feasible computation, using other methods
>   or certificates, can ever separate the models.
> - The table compares `√(kn)` with a single arbitrary coefficient choice `k + n/ln n`, whereas the
>   floor is a `Θ(n/log n)` family with unspecified constants. The crossover near `n = 64` is
>   therefore specific to that coefficient.
>
> Treat the table as a useful finite comparison, not a computational impossibility theorem.

The honest, definitive correction to all the far-line δ* conclusions this session ("it's Johnson", "→½",
"tracks the floor"). They were **over-readings of fundamentally underdetermined data**.

## The scale-confounding (the reason)

The two candidate behaviors for the binding far-line list-decoding radius s*:
- **Johnson:** s* = √(kn)  (⟹ δ* = 1−√ρ, lower window edge)
- **Floor:** s* = k + Θ(n/log n)  (⟹ δ* = 1−ρ−Θ(1/log n), the prize, upper window edge)

These two scales are **numerically within O(1) of each other at every accessible n**, and separate only at huge n:

| n | k | √(kn) (Johnson) | k+n/ln n (floor) | separation |
|---|---|---|---|---|
| 16 | 4 | 8.0 | 9.8 | 1.8 |
| 24 | 6 | 12.0 | 13.6 | 1.6 |
| 32 | 8 | 16.0 | 17.2 | 1.2 |
| 64 | 16 | 32.0 | 31.4 | 0.6 |
| **256** | **64** | **128.0** | **110.2** | **17.8** |
| 1024 | 256 | 512 | 404 | 108 |

The scales **cross** around n=64 and only separate meaningfully at n≥256 — where the binding `C(256,128) ~ 10⁷⁵`
is utterly infeasible (and n=2^32 prize scale is `C(2^32, 2^31)`, astronomically beyond any computer).

## Consequence (honest)

**The far-line δ* computation CANNOT distinguish Johnson from the prize floor at any computationally feasible n.**
My session conclusions were all over-readings of data that fits BOTH:
- "δ* = Johnson + O(1)/n" — fits, but indistinguishable from the floor (the +O(1)/n IS the floor's −Θ(1/log n)
  at small n, since √(kn) ≈ k+n/log n there).
- "δ* → ½ / refutes the floor" — was a small-n-formula artifact, already retracted.
- "δ* tracks the floor" — fits equally, also not established.

**Every numerical claim distinguishing Johnson from the floor at n≤32 is unsupported.** The data is genuinely
underdetermined for the one question that matters.

## Why this matters (and why the prize is hard)

This is the precise reason the **computational** approach (my engine, and the campaign's far-line probes) cannot
settle the prize: the distinguishing regime (n≥256, ideally n=2^32) is unreachable by enumeration. The prize
**requires the asymptotic/analytic argument** — exactly the BGK / curve-decodability wall — because the
finite-n numerics are scale-confounded by construction. The far-line incidence object, the per-direction
decomposition, the p-independence proof — all real and durable — but they **cannot** resolve Johnson-vs-floor
numerically. That resolution is the analytic open core, unchanged.

## Status

A definitive, honest meta-result: the numerics are fundamentally underdetermined for the prize question, with a
rigorous reason (scale coincidence √(kn) ≈ k+n/log n until n≥256). This RETRACTS the session's
Johnson/½/floor distinctions as unsupported, and re-confirms the prize needs analysis, not computation. The
durable contributions stand (engine, p-independence, decomposition); the conclusions distinguishing the window
edges do not. NOT a closure; an honest boundary on what computation can establish here.
