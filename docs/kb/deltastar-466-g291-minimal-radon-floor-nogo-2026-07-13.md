---
id: deltastar-466-g291-minimal-radon-floor-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, weighted-kernel, Farkas, Radon, minimal-circuit, pigeonhole-floor, r-uniform, route-no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G291: the canonical-feature CORE no-go is a minimal, r-uniform positive Radon circuit at the pigeonhole floor

## One-line

G289 exhibits a five-cell positive Farkas circuit that kills every fixed linear functional of the
canonical Ramanujan features `(T2,T4,T8,T16)` on the CORE gate, and shows it is gate-independent, but
never proves the circuit is *minimal*. G291 proves it is: the circuit is a minimal positive Radon
partition sitting exactly at the pigeonhole floor `N = d + 1 = 5` for the canonical linear feature
dimension `d = log2 n = 4`, and its support is r-uniform (spans both ranks `r in {5,6}`). CORE remains
open / on-BGK.

## Why this is new (beyond G289)

G289's kernel-checked payload is: (i) one exact positive dependence among five signed feature vectors,
and (ii) the abstract gate-flip transfer showing the same weights annihilate the negated gate. That
proves a no-go *exists* and is *gate-independent*. It does NOT establish that the census cannot be
compressed: a priori a sub-family of four cells might already carry a positive dependence, which would
make the five-cell certificate non-minimal and the "floor" language unjustified. G291 closes that gap
with a theorem-level minimality proof.

## Abstract layer (general Radon floor)

Over a general family `v : Fin n -> Fin m -> Q`:

- `DeleteOneIndependent v`: every one-deleted subfamily is linearly independent, i.e. the only
  coefficient vector supported off any single index `k` (`c k = 0`) annihilating all `m` coordinates
  is zero.
- `minimal_support_of_deleteOne_independent`: under `DeleteOneIndependent`, any dependence omitting at
  least one index is the zero dependence.
- `full_support_of_nonzero_dependence`: contrapositive packaging: any dependence with a nonzero
  coefficient has full support, so no proper sub-support is dependent.

In the Radon-floor case `n = m + 1` this says a nonzero dependence among `m + 1` vectors in `Q^m`,
each `m`-subset independent, is supported on all `m + 1` of them: a minimal positive circuit is a
positive Radon partition of size exactly `m + 1`.

## Concrete consumer (exact G289 census)

The five sponsor-faithful census cells (`p in {113,337,401,433}`, ranks `{5,6}`, avoiding the
degenerate `p=17` cell), their CORE gate signs, canonical linear features `(T2,T4,T8,T16)`, and the
exact positive Farkas weights are taken verbatim from `_G289CountingMirageNoGo.lean` (`d = 4`, support
`d + 1 = 5`).

- `census_deleteOne_independent`: every `4`-subset of the five signed feature vectors is linearly
  independent. Proved by explicit exact integer Cramer certificates: for each deleted index `k` and
  each target coordinate `t != k`, an integer linear combination of the four coordinate identities
  equals `det_k * c_t`, where `det_k != 0` is the corresponding `4x4` minor determinant (verified
  symbolically in sympy before formalizing; discharged in Lean by `linear_combination` + `norm_num`).
- `census_circuit_full_support`: the positive Farkas circuit uses every one of the five cells (it is
  positive on cell `0`), hence is minimal.
- `circuit_r_uniform`: the support contains a positively-weighted rank-`5` cell and a
  positively-weighted rank-`6` cell, so the no-go is not a per-rank artifact.
- `census_minimal_r_uniform_no_go`: bundles the three facts: no fixed linear functional of
  `(T2,T4,T8,T16)` signs the CORE gate on all five cells; the circuit is full-support (minimal);
  and it is r-uniform.

## Meaning for the frontier

This is the deep-floor / primitive-census certificate. With only `d = 4` canonical Ramanujan
coordinates on the thin 2-power tower `<2> <= (Z/n)^*`, `d + 1 = 5` sponsor-faithful cells already
force a positive circuit and not one cell fewer. The no-go is pinned at the Radon pigeonhole floor and
carries no arithmetic gate content (consistent with and sharpening G289's gate-independence). It does
not bound the covariance at production primes and does not exclude unbounded-dimension or
non-polynomial certificates. The surviving object is unchanged: a real certificate needs unbounded
feature dimension, non-polynomial structure, or genuinely new row-labelled arithmetic beyond the
2-power Ramanujan tower.

## Validation

- `lake env lean` and `scripts/lake-locked.sh build ..._G291MinimalRadonFloorNoGo`: PASS, 1241 jobs,
  zero warnings.
- Axiom audit: all nine theorems `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom
  axioms.
- Forbidden-token precheck (scoped): clean, 0 residual axioms. Sorry census `--fail-on-holes`: 0
  holes.
- Exact probe `scripts/probes/g291_minimal_radon_floor_nogo.py`: PASS (positive circuit support = d+1;
  every 4-subset full-rank; support r-uniform over ranks {5,6}).

CORE remains open / on-BGK.
