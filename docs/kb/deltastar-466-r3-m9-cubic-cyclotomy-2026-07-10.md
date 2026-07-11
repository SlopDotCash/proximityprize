# #466 r=3, m = 9: rung discharged unconditionally; cubic-cyclotomy closed forms refuted (2026-07-10)

Fifth and final brick of the route-(ii) session (R297 → R301). Target: the smallest DIST
instance m = 9 left open by `deltastar-466-r3-dist-stratum-accounting-2026-07-10.md`, via
classical cubic/nonic cyclotomy (4p = L²+27M², primary Jacobi sums in ℤ[ω], HD lifting).

## Discharge (formalized): support collapse + counting

At m = 9 (u = 3) there are exactly three H-cosets, so a DIST triple carries the full label
multiset {0,1,2}, whose sum is ≡ 0 mod 3:

- `distStratum(d) = 0` off `d ∈ {0,3,6}` (`m9_dist_support`, kernel-checked, 729 cases);
- per-(d,j) DIST index count ≤ 6 (`m9_inner_card_le`, kernel-checked, 81 cases);
- hence `‖DIST(d)‖ ≤ 48·q^{3/2}` and **`DistStratumEnergyBound J 3 q 10` for every J with
  `‖J‖² ≤ q`** (`distStratumEnergyBound_rung_m9`) — unconditional, no cancellation.

Probe (32 primes p ≡ 1 mod 9 up to 1171): measured sharp constant `C_D(9) = 1.87` — the
counting constant 10 has 5× headroom. **Rung ladder now: m = 3, 6 (C = 0), m = 9 (C = 10);
first genuinely open m = 12** (u = 4: four cosets, no support collapse, Θ(m²) counts per
output — the analytic regime begins there).

## Refutations (with mechanism)

1. **Generator dependence**: per-character `E_DIST` changes by ~25% at p = 109 when the
   primitive root changes. `χ = λ` fixes one Galois conjugate among the six order-9
   characters and `E_DIST` is not Galois-invariant ⇒ no closed form in (p, L, M) for fixed χ.
2. **Galois-averaged integrality (structure, probe-only)**: the average of `E_DIST` over the
   six order-9 characters is an exact integer at every probed prime (distance to ℤ < 10⁻⁴ at
   magnitude 10¹¹) — Galois invariance + algebraic integrality. Deliberately NOT formalized:
   a faithful proof needs algebraic-number-theory machinery (ring of integers, Galois action
   on cyclotomic sums) with no in-tree counterpart; naming a surrogate Prop would launder it.
3. **(L,M)-basis refutation**: even the integer-valued averaged energy has NO exact linear
   form on `{p³, p², p²L, pL², pM², p, 1}` (LSQ residual 4×10²). Mechanism: the DIST energy
   is nonic-cyclotomic — it lives in ℚ(ζ₉) (degree 6) and is not a function of the cubic
   subfield invariants (L, M). Any exact evaluation must use the ℤ[ζ₉] prime splitting of p
   (six primary nonic Jacobi sums), not Gauss's cubic data. That refines rather than closes:
   a ℤ[ζ₉]-basis regression is the natural successor probe if the lane reopens.

## Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R301CubicCyclotomyM9.lean` — axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no sorryAx), pg-iterate 43s. No new named Props:
everything landed is proven outright (the finite parts by `decide`).

## Session arc (R297 → R301), final state of the r=3 rung

1. R297: HD coset triple collapse (I3) — new exact identity; off-coset extension refuted.
2. R298: rung localized two-sidedly to the off-coset remainder; stratum orthogonality refuted.
3. R299: pattern census; (I2) pair-twist stratum r=2-reducible; HD structure exhausted.
4. R300: rung ⟺ `DistStratumEnergyBound` alone (non-distinct strata priced by counting,
   constant 288); rungs m = 3, 6 at C = 0.
5. R301 (this note): rung m = 9 discharged at C = 10; cyclotomy closed forms refuted.

**Dependency graph of the calibrated r=3 open core:** `TripleConvEnergyBound` ⟺ (absolute
constants, unconditional) `DistStratumEnergyBound`, open only for m ≥ 12, with the Katz
vertical-equidistribution statement (see the R300 kb note) as the literature path.
The lane rests. CORE OPEN, ON-BGK. No fabricated closure.
