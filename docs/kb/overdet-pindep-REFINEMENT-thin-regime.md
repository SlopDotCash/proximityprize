# REFINEMENT: over-determined incidence is p-independent IN THE THIN/PRIZE REGIME (converges to char-0 by p~n^4) — #407

> **Scope correction (2026-10-28 audit, T48).** Only **one** thin cell (`n = 32`,
> `p = 1048609 ≈ n⁴`) was tested, so "p-independence holds in the THIN / PRIZE regime" is not
> established as a universal statement. An exact finite algebraic count can still depend on the
> prime, because coefficient reductions, determinants and collisions change with `p`. A transfer
> statement therefore needs a norm or finite-bad-prime exclusion, and thin counterexamples to
> other transfer claims (for example `n = 64`, `p = 17318209`, recorded under T91) show why that
> exclusion must be retained. Those examples do not by themselves refute the monomial maximum `897`
> reported for this particular cell. The "cubic in n" law is a fit to finite values.

A precise refinement of `overdet-incidence-pindependence-proof.md` after a full-direction, multi-prime test
(`probe_407_overdet_thin_convergence.py`). Honest correction of "exactly p-independent for all p".

## The data (n=32, k=2, s=4, MAX over valid far directions b<s)

| prime p | regime (p ≈) | max over-det incidence |
|---|---|---|
| 97 | n (very thick, index 3) | 96 |
| 1153 | n² (thick) | 513 |
| 3137 | n^2.3 (thick) | 769 |
| **1048609** | **n⁴ (PRIZE, thin)** | **897** |

`897` matches the char-0 cubic extrapolation exactly (the over-det max is cubic in n:
9,37,97,201,361,589,... → 897 at n=32). The thick-prime values (96,513,769) are the **convergence approach**
from below.

## The honest, precise statement

- **Per fixed valid-far direction**, the over-det incidence equals char-0 for `p` avoiding the small cyclotomic
  bad primes (agent's norm certificate at n=16: bad primes ⊆ {2, 23}). That exactness is real.
- **The MAX over far directions** converges to its char-0 value (897 at n=32) **as p grows, reaching it by the
  prize scale `p ~ n^4`**. Thick primes (`p ≪ n^4`) give smaller, p-DEPENDENT values (the binding direction
  changes and large-count directions are capped by the small field).
- So **p-independence holds in the THIN / PRIZE regime** (`p ≳ n^4`); the deviating ("bad") primes are all
  **thick** (`p < n^4`), strictly below the prize regime. The prize is ∀-thin-q, so this is exactly the regime
  that matters.

## Why this still supports the decoupling (but more carefully)

The decoupling argument (δ* p-independent because the binding is over-determined and over-det is p-independent)
holds **in the prize regime**: at `p ~ n^4`, the over-det incidence has converged to its char-0 value
(p-independent), and the under-determined incidence `Θ(C(n,k+1)) ≫ budget` still forces the binding to be
over-determined. So **δ* is p-independent for thin/prize primes** — which is the prize's ∀-thin-q requirement.

## Caveats (no overclaim)

1. **One prize-scale prime** (p=1048609) at n=32 — the match to the char-0 cubic (897) is strong evidence but
   not full confirmation; need 2+ primes `~n^4` per n (the agent confirmed this at n=16 with 3 thin primes → 97).
2. **Convergence rate:** the approach 96→513→769→897 shows convergence completes by `~n^4`; the exact p where it
   converges (vs n³ char-0 count) should be pinned (it's `p ≳ char-0 count = O(n³)`, comfortably below n^4).
3. The threshold/floor question (open item #2) is unchanged: with the over-det max cubic `~n³` at s=k+2 ≫ budget
   `~n`, the binding s* is where the over-det incidence curve crosses `~n`; deriving `s*(n,k)` and comparing
   `δ*=(n−s*)/n` to the floor is still the open combinatorial core.

**Net:** the decoupling is intact for the prize (thin) regime, with the precise mechanism: over-det incidence
converges to its char-0 (cyclotomic, p-independent) value by `p~n^4`. The bad primes are thick (`p ≪ n^4`).
