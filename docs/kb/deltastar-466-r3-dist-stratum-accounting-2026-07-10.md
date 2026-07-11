# #466 r=3 capstone: the rung's dependency graph is ONE Prop — DistStratumEnergyBound (2026-07-10)

Fourth and final brick of the route-(ii) session (after the HD coset collapse, the mixed-depth
localization, and the pattern stratification; see the three sibling kb notes of this date).

## The accounting theorem (unconditional, stronger than the HD pricing)

Split `tripleConv J d` by the decidable predicate "the ordered triple `(i, d−j−i, j)` has all
three H-coset labels distinct" (`H = {0,u,2u}`, `u = m/3`). Then:

1. **Exact split** `tripleConv = distStratum + nonDistStratum` (pure algebra).
2. **Count-thinness of nonDist** (the key observation): for fixed `(d,j)` the bad `i`-set is
   contained in two explicit translate-triples `{j, j−u, j−2u}`, `{d−2j, d−2j+u, d−2j+2u}`
   plus three doubling-fibers `{i : 2i ∈ d−j−H}` — at most `6 + 3k₂` elements,
   `k₂ = #{i : 2i=0} = gcd(2,m) ≤ 2`. Hence with ONLY `‖J‖² ≤ q`:
   `∑_d ‖nonDist(d)‖² ≤ 144·m³·q³` **unconditionally** — no Hasse–Davenport, no cancellation.
3. **Two-sided accounting** (absolute constants):
   `DistStratumEnergyBound C_D ⟹ TripleConvEnergyBound (2C_D + 288)` and conversely
   (`2C + 288`).

**Final dependency graph of the r=3 rung:** the §33 calibrated open core
`TripleConvEnergyBound` ⟺ (up to absolute constants) `DistStratumEnergyBound` alone, given
the classical coefficient envelope. The HD named inputs (`HDCosetTripleCollapse`,
`HDPairCollapse` — classical mathematics, a Mathlib Gauss-sum-product gap) and the r=2-class
`MixedConvEnergyBound` supply the finer exact structure of the non-distinct strata (R297–R299)
but are NOT needed for the scale accounting. The R23 triangle-inequality baseline's `m²` loss
is provably confined to the all-distinct-coset triples.

## Instantiability and ladder rungs (discharged)

- `distStratumEnergyBound_trivial`: `C = m²` always (baseline, now localized to DIST).
- **Rung m = 3** (`u = 1`, one coset) and **rung m = 6** (`u = 2`, two cosets): the DIST
  pattern is EMPTY by pigeonhole, kernel-checked by `decide`; `DistStratumEnergyBound` holds
  with `C = 0` for every coefficient sequence and every `q` — matching the probe
  (`E_DIST ≡ 0` at m = 6 in `probe_466_r3_pattern_stratification.py`). First open m-values:
  `u = m/3 ≥ 3`, i.e. m = 9, 12, 15, …; probe calibration there: `C ≈ 2–3` (E_DIST/Wick
  0.1–0.5, flat in q).

## Route (i): the literature path for the general form (NOT a Lean Prop yet)

The open content is square-root cancellation among **all-distinct-coset Jacobi angle
triples**. The precise monodromy statement needed, in Katz's framework (N. Katz, *Gauss Sums,
Kloosterman Sums, and Monodromy Groups*, Ann. of Math. Studies 116, and *Twisted L-Functions
and Monodromy*, Studies 150): for fixed `m` and `q → ∞` with `m ∣ q−1`, the normalized Jacobi
angles `θ_j = J_j/√q` (J_j = J(λ^j, χ), λ of order m) should, in the vertical direction,
equidistribute as a tuple: for each linear condition `j₁+j₂+j₃ = d` with the three indices in
pairwise-distinct H-cosets, the triple `(θ_{j₁}, θ_{j₂}, θ_{j₃})` equidistributes w.r.t. Haar
measure on `(S¹)³` — equivalently, the geometric monodromy of the associated Kummer-sheaf
family is large enough that the only multiplicative relations among the angles are the forced
ones (the HD relations, which live exactly on the NON-distinct patterns — consistent with our
refutation that no constant-ratio relation exists off them). Under such joint
equidistribution, second-moment bookkeeping gives `DistStratumEnergyBound` with `C = O(1)`.
We do NOT name this as a Lean Prop: a faithful statement requires the sheaf-theoretic
framework (perverse sheaves / monodromy groups) that has no in-tree counterpart; naming a
weakened surrogate would launder the gap. The honest Lean-side open object stays
`DistStratumEnergyBound`.

## Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R300DistStratumAccounting.lean` — axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no sorryAx), pg-iterate 45s. Theorems:
`tripleConv_eq_dist_add_nonDist`, `nonDist_inner_subset`, `card_double_fiber_le_card_kernel`,
`card_nonDist_inner_le`, `norm_nonDistStratum_le`, `nonDistStratum_energy_le`
(+`_of_sq_bound`), `tripleConvEnergyBound_of_distStratum`,
`distStratumEnergyBound_of_tripleConvEnergyBound`, `distStratumEnergyBound_trivial`,
`distStratum_eq_zero_m3`/`_m6`, `distStratumEnergyBound_rung_m3`/`_m6`.

## Session arc summary (R297 → R300)

1. R297: HD coset triple collapse (I3) — new exact identity on the ladder object; off-coset
   extension refuted.
2. R298: (I3) as change of variables — orthogonality refuted; rung localized two-sidedly to
   the off-coset remainder.
3. R299: pattern census — TWO∪DIST carries the mass; (I2) pair-twist stratum r=2-reducible;
   no within-pattern HD collapse (HD structure exhausted).
4. R300 (this note): the rung ⟺ `DistStratumEnergyBound` alone; non-distinct strata priced by
   counting, constant 288; rungs m = 3, 6 discharged at `C = 0`.

DISPROOF tag: `466-r3-dist-stratum-accounting-final`. CORE OPEN, ON-BGK.
No fabricated closure.
