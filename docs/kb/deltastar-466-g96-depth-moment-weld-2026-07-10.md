# Issue #466/#505 G96: the depth–moment weld

Date: 2026-07-10

The corrected-padding sector machinery (G83M/G86/G87/G88, assembled by G89/G90, semantically
pinned by G95) lived on an abstract mass/envelope interface. G96 welds it to the production
analytic object: the moment carrier inside `DCEnergyBound`, which feeds
`eta_pow_le_of_dcEnergyBound` and the prize sup-norm chain `M ≤ √(2n·ln q)`.

## Results (`Frontier/_G96DepthMomentWeld.lean`, all 7 declarations axiom-clean, 60 s)

- `rEnergy_eq_addREnergy`: `SubgroupGaussSumMoment.rEnergy G r = Finset.addREnergy r G`.
- `rEnergy_eq_sum_depthFiber` (**the weld**): `rEnergy G r = Σ_{s=0}^{r} depthFiber G r s` —
  the 2r-th-moment object decomposes exactly by G83M maximal-cancellation depth.
- `dcEnergyBound_iff_nat`: `DCEnergyBound G r ↔ q·rEnergy G r ≤ q·(2r-1)!!·#G^r + #G^(2r)`
  (ℕ-clean, real subtraction cleared).
- `dcEnergyBound_of_depth_allowances`: per-depth caps + per-depth DC allowances
  (`Σ cap ≤ Wick`, `Σ D ≤ #G^(2r)`, `q·fiber_s ≤ q·cap_s + D_s`) imply `DCEnergyBound G r`.
- `sum_allPairsDepthFiber`: the population (all-pairs) depth fibers sum EXACTLY to `#G^(2r)` —
  the canonical allowances spend the DC mass with zero slack.
- `dcEnergyBound_of_centered_depth_bounds` (**headline, zero free parameters**): if for every
  depth `q·(equal-sum pairs at depth s) ≤ q·cap_s + (all pairs at depth s)` — i.e. the
  depth-`s` collision count exceeds its uniform expectation by at most `cap_s` — and
  `Σ cap ≤ (2r-1)!!·#G^r`, then `DCEnergyBound G r`.
- `rEnergy_le_wick_of_zero_allowances`: sanity — zero allowances demand `rEnergy ≤ Wick`
  outright, which G95's pigeonhole floor refutes at prize scale; the allowances are
  load-bearing.

## What this changes

The open wall is now stated as a finite family of centered per-depth inequalities about ONE
concrete finite object (`ZMod P`, `#G = 2^30`, `r = 110`), consumable with no further plumbing:
prove `q·depthFiber_s − allPairsDepthFiber_s ≤ q·cap_s` for a cap family totalling the Wick
budget, and `DCEnergyBound` at production scale follows, feeding the existing prize chain. The
per-depth centered object is the `relationAnomaly` shape from R366/G75, now at the production
interface.

## Honest scope

No claim the centered bounds hold (that IS the square-root-cancellation/BGK wall). CORE remains
OPEN / ON-BGK.
