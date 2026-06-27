# Issue #464: floor level-depth prime-scale gate

Date: 2026-06-25.

Status: **off-BGK arithmetic guardrail**, not a delta-star proof.

## Inputs Checked

- Live issue #464, especially the off-BGK least-prime floor-localization lane.
- `FloorFiniteRungUniformityBarrier.lean`, which separates finite rung evidence from all-rung
  uniformity.
- `_FloorLinnikExponentGate.lean`, `_FloorLinnikThornerZamanArrow.lean`, and
  `_FloorLinnikTZClosure.lean`, which package prime-supply assumptions for the floor route.

## Lean Result

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorLevelDepthPrimeScaleGate.lean
```

formalizes the scale condition for using least-prime-in-AP input at deeper 2-power levels.

If the base domain is `n = 2^a` but the obstruction can occur at a deeper modulus `2^k`, then an
exponent-`e` prime supply at that deeper level fits below the original prize scale only when

```text
k * e <= 4 * a.
```

The file proves the scale gate and its exact iff forms:

- `dyadic_level_power_le_prize_iff_mul_le`: a level-`k`, exponent-`e` supply fits below
  `(2^a)^4` iff `k * e <= 4 * a`.
- `dyadic_prize_lt_level_power_iff_mul_lt`: it overshoots iff `4 * a < k * e`.
- `level_witness_le_prize_of_mul_le`: any prime witness below the level/exponent scale is below
  prize scale once the exponent-product gate holds.
- `mul_lt_of_prize_lt_level_witness`: any supplied witness that is still above prize scale proves
  the exponent-product gate failed.
- `not_prize_lt_level_witness_of_mul_le`: contrapositively, the exponent-product gate forbids
  above-prize supplied witnesses.
- `fifth_power_deeper_level_above_prize`: classical exponent-5 Linnik scale overshoots the
  `(2^a)^4` prize scale for every deeper level `k >= a`.
- `cubic_deeper_level_le_prize_of_depth`: cubic supply at level `a + d` fits while `3d <= a`.
- `cubic_deeper_level_le_prize_iff_depth`: the cubic fit is exact; it holds iff `3d <= a`.
- `prize_lt_cubic_deeper_level_of_depth_too_large`: cubic supply overshoots when `a < 3d`.
- `prize_lt_cubic_deeper_level_iff_depth_too_large`: the strict cubic overshoot is exact.
- `depth_too_large_of_prize_lt_cubic_level_witness`: an above-prize cubic supplied witness forces
  `a < 3d`.
- `not_prize_lt_cubic_level_witness_of_depth`: the allowed cubic-depth range forbids above-prize
  witnesses.
- `level_depth_prime_scale_summary`: the bundled depth/exponent verdict.

## Consequence for #464

So the multi-level floor-bad story needs both:

```text
1. a structural theorem bounding the level depth d;
2. a prime-supply exponent that fits k * e <= 4a.
```

## Critical Verdict

This corrects a tempting overclaim in the older off-BGK narrative.  “Floor-bad primes are least
primes in AP at bounded 2-power depth” is not enough by itself unless the depth and exponent fit the
base prize scale.

For the current in-tree TZ-style cubic bridge, bounded depth is quantitatively generous:

```text
d <= a / 3.
```

For exponent-5 Linnik scale, there is no room even at the base level.  Thus generic Linnik cannot
rescue a deeper-level floor selector inside the quartic prize window.

## What New Math Would Look Like

A viable deeper-level off-BGK route must prove a structural theorem of the form:

```text
any floor-bad obstruction visible from level a lives at level a + d with 3d <= a,
```

if it relies on cubic prime supply.  If the only available prime theorem has exponent `e`, the
structural theorem must instead force

```text
(a + d) * e <= 4a.
```

This does not prove floor localization or family domination.  It prevents the prime-supply part of
the argument from being invoked outside the scale where it can actually interact with the prize
prime range.
