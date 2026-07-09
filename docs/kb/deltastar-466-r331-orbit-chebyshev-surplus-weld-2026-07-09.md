# #466 R331 — orbit Chebyshev × shadow surplus weld: the level-set count pays only the collision mass

## What landed

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R331OrbitChebyshevSurplusWeld.lean`
(axiom-clean; three theorems).

The weld of the session's two arcs:

- **`orbit_count_le_shadow_plus_surplus`** (abstract): if the depth-`r` energy is bounded by
  `char-0 shadowEnergy(n,m,r) + S`, then for any pairwise `G`-inequivalent family of
  `T`-large depth-`r` deviations,
  `|R|·|G|·T² ≤ q·(q·(shadowEnergy + S) − |G|^{2r})`.
- **`orbit_count_le_shadow_plus_surplus_of_repIdentifies`** (concrete): with `g` of order
  `n = 2m`, `g^m = −1`, and the R310 rep-identification, the hypothesis becomes a direct
  bound `E_r − shadowEnergy ≤ S` on the collision mass.
- **`orbit_count_le_shadow_of_injective`**: on shadow-injective primes (the r305/r307
  good-prime criterion) `S = 0` and the count is bounded by the char-0 constant alone.

## Why it matters

`shadowEnergy(n, m, r)` is an exact, prime-independent, computable char-0 quantity. This
weld therefore isolates EVERY prime-dependent unknown of the depth-`r` large-period
level-set count into the single scalar `S` = mod-`p` collision mass — precisely the object
the kernel-relation arc (r312–r321) decomposes into sparse small-height relations and the
census (r305) computes exactly at small `n`. Any future bound on `S` (per-prime, almost-all
primes, or structured-family) now converts into an orbit count by one theorem application,
with no further plumbing.

Does not touch the wall: bounding `S` uniformly to `r ≈ ln q` at `n = 2³⁰` IS the wall.
CORE OPEN, ON-BGK.

Arc completed: r300/r303 (orbit Chebyshev) × r306–r310 (shadow floor/decomposition) →
**r331 (consumer weld)**.
