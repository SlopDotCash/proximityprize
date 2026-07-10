# #466 R392 — the capstone: ONE named Prop is the arc's only open input

## What landed (axiom-clean, real locked build, first-try compile)

`Frontier/_R392RelationCountCapstone.lean`:

- **`RealizedRelationCountBound g n m r K`**: THE named open Prop — at most `K` realized
  vanishing relations over all sectors;
- **`rEnergy_le_of_relationCountBound`**: it implies `E_r ≤ (1+K)·shadowEnergy`
  (r312 identity + r388 union bound);
- **`orbit_count_of_relationCountBound`**: it implies the depth-`r` orbit Chebyshev
  `|R|·|G|·T² ≤ q·(q·(1+K)·shadowEnergy − |G|^{2r})` — the moment-side control the prize
  pipeline consumes, with `shadowEnergy` an exact char-0 constant.

## The arc, complete

r300–r392 now form one machine-checked conditional: **sub-Wick moment control at depth r
follows from a sub-Wick-scale count K of realized vanishing relations** — where those
relations are exactly characterized (census identity r389), orbit-quantized (r371/r372),
sector-partitioned (r387), and individually certified by nonzero annihilators of height
≤ (2m)!(2r)^{2m} divisible by the prime (r390/r391). Wick-scale `K` means
`K·shadowEnergy ≲ Wick headroom`; at census-good primes `K = 0` and the control is
unconditional char-0.

The open core of the Proximity Prize, per this arc: discharge
`RealizedRelationCountBound` at the prize parameters (n = 2³⁰, r ≈ ln q, p ≈ n·2¹²⁸)
with `K` of Wick scale. Not proven; not refuted; now a single named Prop with its entire
consumer chain verified. CORE OPEN, ON-BGK.
