# Issue #466/#505 G95: raw cardinality cannot satisfy the deep budget caps

Date: 2026-07-10

G89 reduced the all-depth production absorption to per-depth budget caps. G95 proves the
unconditional **no-go**: at the production point, NO core-count function `J` can satisfy the
caps when the per-depth masses are the *raw cardinalities* of the equal-sum depth fibers. The
`1/p`-scale relation weighting used by the DC-subtracted moment is therefore mathematically
mandatory for every future consumer of the G89 gate — not a modelling choice.

## Results (`Frontier/_G95CardinalityDeepCapNoGo.lean`, all axiom-clean, pg-iterate 45 s)

- `card_pow_le_card_mul_addREnergy` (**new, upstreamable**): the Cauchy–Schwarz pigeonhole
  floor `#A^(2r) ≤ card α * addREnergy r A` for any finset `A` in a finite ambient additive
  monoid — the missing dual to the in-tree `Finset.addREnergy_le` upper bound. Proof: partition
  the `r`-tuple cube by sum value, expand the energy as `Σ_t fiber(t)^2`, apply
  `sq_sum_le_card_mul_sum_sq` (Chebyshev/Cauchy–Schwarz, valid directly over ℕ).
- `cancelDepth`, `depthFiber`, `addREnergy_eq_sum_depthFiber`: the equal-sum pair set
  partitions exactly by G83M maximal-cancellation depth `s = 0, …, r`.
- `cardinality_caps_force_energy_ceiling`: envelopes + caps for the raw depth fibers force
  `#A^(2r) ≤ card α * (2r-1)!! * #A^r` — generic in the ambient group.
- `production_cardinality_caps_impossible` (**headline**): at the prize shape (`#A = 2^30`
  inside `ZMod P`, `P = 2^30*(2^128+192)+1`, `r = 110`), for every `J`: if the raw depth-fiber
  cardinalities fit the factorial-corrected envelopes, the G89 caps CANNOT all hold. Kernel
  arithmetic: the pigeonhole floor is `2^6600` equal-sum pairs versus a Wick ceiling below
  `2^4157`.

## Reading

The combinatorial padding/decoder route (G81C/G83M/G86/G87/G88 → G89) is NOT refuted — what is
refuted is instantiating its masses by counting. The raw equal-sum pair population genuinely
exceeds the total Gaussian moment budget by `≈ 2^2443`; only after the relation-probability
weighting (each collision carrying `p^{-1}`-scale mass, as in the DC-subtracted moment) can the
budget be met. This pins the semantic interface of the caps: `J`/`W` are weighted masses, and
the open deep-cap wall is a statement about weighted (energy-normalized) quantities, exactly
the square-root-cancellation face already identified as CORE.

## Honest scope

No claim about the weighted deep caps (open analytic wall). No production bound on M. CORE
remains OPEN / ON-BGK.
