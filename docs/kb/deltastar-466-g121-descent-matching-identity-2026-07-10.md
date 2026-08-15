# Issue #466/#505 G121: the descent matching identity — exact cross-rung transfer

Date: 2026-07-10

The same-day counterexamples (`DCEnergyBound` false at `(n,p,r) = (64, 16778497, 5)`; G106's
positive depth-five anomaly at order 32) killed every uniform per-depth sign law. What
survives arbitrary counterexamples is an exact identity. G121 supplies the first cross-RUNG
one on the depth-census objects.

## Results (`Frontier/_G121DescentMatchingIdentity.lean`, 7 declarations, axiom-clean, 0 sorryAx)

For `matchCount (v, w) = #{(i, j) : v i = w j}` on rung-`(k+1)` pairs:

- `card_matchSlice` / `card_matchSlice_cube`: fixing a matching position pair `(i, j)`,
  removal/insertion (`Fin.removeNth` / `Fin.insertNth`) bijects the slice onto
  (free common value) × (rung-`k` equal-sum pairs), resp. the population analogue.
- `sum_matchCount_energySet`: `Σ_{eq-sum} matchCount = (k+1)² · #A · E_k(A)`.
- `sum_matchCount_cube`: `Σ_{all pairs} matchCount = (k+1)² · #A^(2k+1)`.
- `descent_anomaly_transfer` (ℤ): `q·Σ_eq matchCount − Σ_all matchCount
  = (k+1)²·#A·(q·E_k − #A^(2k))`.
- `descent_moment_nonneg`: that quantity is `≥ 0` **unconditionally** — at every prime, every
  set, every rung — by the G95 pigeonhole floor at rung `k`. No sign law assumed; immune to
  the new counterexamples.
- `matchCount_eq_zero_iff`: `matchCount y = 0 ↔ cancelDepth y = r` — the matching moment
  vanishes exactly on the fully-disjoint (maximal-depth) sector.

## Structural reading

The invisibility theorem + the identities pin WHERE new information lives at each rung: the
matching moment of the rung-`(k+1)` signed depth measure is exactly determined by the
rung-`k` global anomaly, and the only sector it cannot see is the fully-disjoint one. So all
rung-`(k+1)` content beyond descent is the full-depth sector — the precise object the
depth-five lanes (G111–G120) are attacking. Any future bound (or counterexample) at rung `k`
transfers exactly to a weighted statement at rung `k+1` through this identity, which is the
right replacement for uniform laws in the post-counterexample regime.

Natural continuation (documented, not claimed): higher matching moments (`m` marked
positions) biject onto `([r]_m)²/m!`-weighted rung-`(r−m)` pairs, giving a full triangular
moment ladder; the `m`-th moment vanishes exactly below depth threshold, so the ladder
triangularizes the depth census against the rung hierarchy.

## Honest scope

Exact identities and one unconditional inequality; no bound on the fully-disjoint sector
(that is the wall). CORE remains OPEN.
