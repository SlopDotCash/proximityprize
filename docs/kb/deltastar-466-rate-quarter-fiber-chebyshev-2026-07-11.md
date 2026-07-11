# δ* #466 — Fiber-Chebyshev refinement: the `(k−1)` foreign-vote cap is REAL and kernel-landed; the boundary-moving hope (u-relative) is REFUTED — `F₀` does not move (2026-07-11)

**Lane:** P1 rate-quarter — tenth round of the 2026-07-11 session, executing the
cross-cone round's bonus finding.
**Probe:** `scripts/probes/probe_rate_quarter_p1_fiber_chebyshev.py` (exact).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterFiberChebyshevRefinement.lean`
(pg-iterate OK 10s; 8 theorems; full axiom lists read manually via `lake env lean`:
all exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx, no warnings).

## The mechanism audit (the round's honest core)

The `(k−1)` fiber cap needs the fiber to be the zero set of a NONZERO deg `< k`
polynomial — i.e. BOTH components of the ratio map must be codewords.

* **Codeword-pair case — REAL (kernel-landed).**  A rider `γ` of pencil `a`
  voting at `i ∈ alignedSet(b)` satisfies `(wb₀−wa₀)(i) + γ(wb₁−wa₁)(i) = 0` —
  the zero set of the CODEWORD `r₀ + γ·r₁`.  Probe: 200 random pairs max fiber 5;
  adversarial pair achieves fiber `= k−1 = 63` exactly (cap TIGHT).
* **U-relative case — REFUTED (counterexample).**  The derecursion stall
  ledger's map `ρ = (u₁−w)/D` has neither component a codeword; adversarial
  `u₁ = w + s₀·D` on 200 coordinates gives fiber `200 ≫ 63` at μ_256.
  **Consequence: the stall boundary `F₀ = 75018133` does NOT move; the stall
  band `[75018134, 480946858]` is unchanged; the coordinator's step-(1)
  ledger-recomputation and step-(2) residual-shrink do not exist as stated.**
  No fake recomputation was attempted.

## Kernel-checked (prize shape)

* `codeword_zero_set_le` — nonzero codewords have `≤ k−1` zeros (via
  `predecessor_sep` vs the zero codeword).
* `foreign_vote_fiber_le` — non-exceptional riders collect `≤ k−1` votes inside
  a foreign aligned region.
* `exceptional_scalar_subsingleton` — at most one exceptional (proportionality)
  scalar per distinct pencil pair.
* `foreign_region_rider_energy` — **the fiber-Chebyshev second moment**:
  `S.card · m² ≤ (k−1)·|R|` for non-exceptional scalars with `≥ m` foreign
  votes each — refines the disjointness bound `S.card · m ≤ |R|` exactly when
  `m > k−1`.
* `no_fully_foreign_rider` — `k−1 = 268435455 < N−T = 480946858`: no
  non-exceptional rider collects `(N−T)`-scale votes inside one foreign region.
* Rungs: `refinement_crossover` (effective iff foreign-region alignment
  `A < T−k+1 = 324359511`; the pair-pencil floor `2T−N = 111848108` is deep
  inside — the ENTIRE cloud-floor regime is refined, factor
  `(N−T)/(k−1) ≈ 1.79`), `refinement_factor_floor`, `no_fully_foreign_ledger`
  (`(k−1)(T−1) < (N−T)²`).

## What changed / what did not

* NEW: the per-(pencil-pair, region) vote structure of the cloud is now
  second-moment-capped — every rider spreads its votes over ≥ 2 foreign regions
  or junk (`no_fully_foreign_rider`), and heavy-vote concentration in covered
  regions is quadratically expensive.  This constrains the EXTREMAL geometry of
  swarm families (the dual-construction's riders take exactly 1 vote per
  region — consistent).
* UNCHANGED (honesty): `F₀`, the stall band, `SwarmResidual` (junk/uncovered
  votes are not constrained — the residual is NOT redefined), δ*, the bracket
  `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)`.

## Next targets

1. Compose `foreign_region_rider_energy` with the cluster-confinement master:
   in a `FiveCoverForm` family the three margined pencils' riders vote in the
   two capacity pencils' regions or junk — the second moment may shrink the
   margined caps `36995913` further (exact recomputation needed; the junk slice
   again decides).
2. The u-relative refutation sharpens the swarm's profile: adversarial `u₁`
   concentrating fibers is exactly the swarm's freedom — any future ledger
   refinement must go through codeword-pair structures (pair-pencils), not
   u-relative maps.
