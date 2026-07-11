# #466 r=3: (I3) as a change of variables in the sextic energy — orthogonality refuted, two-sided localization landed (2026-07-10)

Successor to `deltastar-466-r3-hasse-davenport-coset-collapse-2026-07-10.md` (same session,
coordinator-directed move #1). Target: substitute the HD coset collapse INSIDE
`∑_{s≠0}‖T(s)‖⁶ = (q−1)·∑_c‖(J^{∗3})(c)‖²` rather than per-term bounding.

## The exact stratum split (probe-verified, 0 failures / 18 instances)

Inside the Lean `tripleConv` (nonzero-index convention of `_R21/_R22/_R23`), the ordered
triples that are permutations of a FULL coset `{j, j+u, j+2u}` (u = m/3) have index sum 3j,
and the tripling fiber `{j : 3j = d}` is exactly that one coset. Hence:

- **(P1)** `A(d) = 2·∑_{j:3j=d, d≠0} J_j J_{j+u} J_{j+2u}` is the coset-diagonal stratum of
  `tripleConv` (6 orderings = 2 × the 3-element fiber; `A(0) = 0` because the unique
  candidate coset is `H ∋ 0`, killed by the nonzero-index convention);
- **(M1)** under (I3): `A(d) = 6·κ·J₃(d)` on `3ℤ/m∖{0}`, 0 elsewhere — depth-1 exactly;
- `tripleConv = A + R` definitionally, `R` = off-coset remainder.

Probe `scripts/probes/probe_466_r3_mixed_depth_correlation.py`: (P1), (M1), energy-split
sanity all EXACT in 18 nondegenerate (q,m,χ) cells (q ≤ 73, m ≤ 36, χ in/out of family).

## Refutation: no mixed-depth orthogonality

Candidate (M3) `X := ∑_d A(d)·conj(R(d)) = 0` is **FALSE in 18/18 instances**: normalized
correlation |X|/√(E_A·E_R) ∈ [0.08, 0.63], |X| ≈ m²·q³. The HD stratum and the remainder are
genuinely correlated — any route through an exact Pythagoras/orthogonality of strata is dead.

## The calibrated corrected form (landed, axiom-clean)

ℓ²-triangle instead of Pythagoras gives the **two-sided localization** with explicit absolute
constants. Under `HDCosetTripleCollapse` with the classical envelopes (‖κ‖ ≤ q, ‖J₃‖² ≤ q,
k₀ = card{j : 3j = 0} ≤ 3):

- `OffCosetRemainderEnergyBound J u q C_R  ⟹  TripleConvEnergyBound J q (2·C_R + 72)`
- `TripleConvEnergyBound J q C  ⟹  OffCosetRemainderEnergyBound J u q (2·C + 72)`

So **given HD, the calibrated r=3 open core and the off-coset stratum energy bound are the
same open problem up to absolute constants.** The diagonal stratum costs ≤ 36·m·q³ = (36/m²)
of the Wick budget. Honest calibration: the remainder carries essentially all of the energy
(probe: E_R/(6m³q³) ≈ 0.1–0.6), so this is a structural localization (removes an exact
stratum and gives the rung a strictly smaller normal form), not a mass reduction.

## Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R298MixedDepthCorrelation.lean` —
axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx), pg-iterate 48s:
- `tripleFiber`, `cosetDiag`, `offCosetRemainder` + definitional split
  `tripleConv_eq_cosetDiag_add_offCosetRemainder`;
- `cosetDiag_collapse` (A = 2·fiber-card·κ·J₃ under HD);
- `card_fiber_le_card_kernel` — PROVEN (fiber injects into the 3-torsion kernel; the `≤ 3`
  cap `hk₀` is an explicit hypothesis = gcd(3,m), decidable per instance);
- `cosetDiag_energy_le`;
- `tripleConvEnergyBound_of_offCosetRemainder` /
  `offCosetRemainderEnergyBound_of_tripleConvEnergyBound` — the two-sided localization.

Named open inputs: `HDCosetTripleCollapse` (classical HD, as in R297) and the NEW corrected
core `OffCosetRemainderEnergyBound` (strict sub-object of the R23 input).

## Corrected next target

The r=3 rung is now: **bound the off-coset remainder energy** `∑_d‖R(d)‖² ≤ C·m³·q³`.
Since (a) the coset-diagonal is exactly depth-1 and (b) strata are non-orthogonal with O(1)
correlation, the two live moves are:
1. iterate the stratification — split R itself by the coset PATTERN of (j₁,j₂,j₃) (3 cosets
   distinct / two equal / all equal-but-not-full-coset) and hunt HD-type exact structure on
   the pattern-restricted sub-sums (the k=2 identity (I2) constrains the two-equal patterns);
2. route (i) Katz equidistribution now needs only square-root cancellation on off-coset
   angle triples — reformulable per pattern class as a finite checkable statement.

DISPROOF tag: `466-r3-mixed-depth-orthogonality-refuted-localization-landed`.
CORE OPEN, ON-BGK. No fabricated closure.
