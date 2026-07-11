# #466 r=3: pattern stratification of the off-coset remainder — HD structure exhausted, TWO/DIST is the irreducible carrier (2026-07-10)

Third brick of the route-(ii) session (after
`deltastar-466-r3-hasse-davenport-coset-collapse-2026-07-10.md` and
`deltastar-466-r3-mixed-depth-localization-2026-07-10.md`). Coordinator-directed move:
split the off-coset remainder R by the full coset-pattern of (j₁,j₂,j₃) and hunt HD-type
structure per pattern.

## Mass census (probe, exact, 0 structural failures)

`scripts/probes/probe_466_r3_pattern_stratification.py` — 14 nondegenerate (q,m,χ) cells plus
a fixed-m=12 growth ladder to p=181. Patterns by multiset of H-cosets (H = {0,u,2u}, u = m/3):

| pattern | content | energy/Wick |
|---|---|---|
| FULL | full-coset covering (= R298 diagonal, HD-extracted) | ≤ 0.03 |
| SAME3 | one coset, repeated offsets | ≤ 0.05 |
| TWO | exactly two indices share a coset | 0.06–0.32 |
| DIST | all three cosets distinct | 0–0.49 (0 iff u ≤ 2) |

TWO ∪ DIST carries essentially all the remainder energy, and both classes are FLAT in p along
fixed m — square-root cancellation is numerically present in the generic patterns (consistent
with R23's O(1) total). No pattern class shows growth: the rung's difficulty is phase
bookkeeping, not a hidden divergent stratum.

## Exact structure found (HP1): the (I2) pair-twist stratum is r=2-reducible

With `v = m/2` (the FULL order-2-subgroup offset; 2∣m, χ² nontrivial):

- `S(d) = ∑_j J_j·J_{j+v}·J_{d−2j−v} = κ₂·M(d)` EXACTLY, `κ₂ = χ(2)²·J(χ,χ)` (‖κ₂‖ = √q),
  `M = J₂ ⋆ J` a mixed depth-(1,1) convolution, `J₂ = jacobiCoeff χ² lam`;
- measured `∑_d‖M(d)‖²/(m²q²) ≈ 1.0–1.9` — Wick-flat at the r=2-type scale;
- hence stratum energy ≤ C·m²·q³ = (C/6m)·Wick, supplied by r=2-class inputs (the rung that is
  closed mod textbook Weil). Every triple carrying an m/2-pair is removable at r=2 cost.

## Refutation: no within-pattern HD collapse

The offset internal to the TWO class is `u = m/3`, which is NOT a full order-2-subgroup coset.
The candidate constant-ratio collapse `J_j·J_{j+u} = c·J₂(2j+u)` fails with ratio spread O(q)
in every tested cell (p = 13, 19, 31, 37). HD pair rigidity exists at offset m/2 and nowhere
else. **With (I3) (order-3 full coset) and (I2) (order-2 offset) both spent, every HD-type
exact collapse available on the ladder object is exhausted.**

## Calibrated conclusion

The minimal open Prop for the r=3 rung remains `OffCosetRemainderEnergyBound` (R298), with
sharpened content: its mass is the generic-pattern (TWO ∪ DIST) triples, which admit no
constant-ratio exact collapse and are already numerically Wick-flat. Closing the rung from
here requires genuinely analytic input — Katz vertical equidistribution (route i) for the
generic-pattern angle triples, now a sharply delimited target — not further exact HD structure.

## Formal kernel

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R299PatternStratification.lean` — axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no sorryAx), pg-iterate 33s:
- `HDPairCollapse` — named (I2) input (classical HD, probe-verified);
- `pairTwistStratum`, `mixedConv` — the stratum and its depth-(1,1) shadow;
- `pairTwistStratum_collapse` — exact collapse S = κ₂·M;
- `pairTwistStratum_energy_eq` — exact energy transfer ∑‖S‖² = ‖κ₂‖²∑‖M‖²;
- `MixedConvEnergyBound` — the r=2-type named input at scale C·m²·q² (probe: C = 4 comfortable);
- `pairTwistStratum_energy_le` — the consumer (≤ K²·C·m²·q²; K² = q classically).

DISPROOF tag: `466-r3-pattern-stratification-hd-exhausted`. CORE OPEN, ON-BGK.
No fabricated closure.
