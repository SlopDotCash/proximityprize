# SYZ1: the 31/64-predecessor all-stack scalar cap is REFUTED at analogue scale by the degenerate-subset channel — the exact-pin hypothesis is unsatisfiable (2026-07-10)

Status: constructive refutation-at-analogue, exact and fully verified; scale-free algebra that
transfers to production parameters. The conditional exact pin's hypothesis is dead; the
unconditional bracket (δ* ≤ 31/64 and the ladder floor) is untouched.

## The refuted object

`_PrizeShapeRateHalfBracket.lean`'s
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` consumes
`hcount`: for EVERY stack (u₀,u₁), the number of `mcaEvent`-bad scalars at
`predecessorRadius (2^30) (31·2^24)` is ≤ 2^30. No stack guard, literal `mcaEvent`
(witness set carries the codeword agreement AND the ¬pairJoint clause).

## The channel

A t-subset S is *degenerate* for a stack when both u₀|S and u₁|S are restrictions of
codewords v₀, v₁. Then for every x ∉ S with d₁(x) ≠ 0 (dᵢ = uᵢ − vᵢ), the scalar
γₓ = −d₀(x)/d₁(x) is genuinely mcaEvent-bad: the line u₀+γₓu₁ agrees with the codeword
v₀+γₓv₁ on S ∪ {x} (size t+1), and pairJoint fails on that same witness set because the
unique S-interpolants miss uᵢ at x. One degenerate subset donates up to n−t distinct bad
scalars; D subsets cost 2(t−k)D syndrome rank out of 2(n−k) and stack additively.

## Verified results (probe `scripts/probes/probe_syzygy_configuration_bad_counts.py`)

Every certified scalar fully verified against the literal mcaEvent (agreement set + pairJoint,
two independent interpolation paths); over-budget witnesses printed with full reproduction data.

| n | k | t | p | family | certified bad | budget n | verdict |
|---|---|---|---|---|---|---|---|
| 32 | 16 | 18 | 2^30-ish, 2^40-ish | D3 subsets | 42 | 32 | OVER-BUDGET |
| 32 | 16 | 18 | same | D7 | 98 | 32 | OVER-BUDGET |
| 64 | 32 | 34 | ~2^60 | D7 | 210 | 64 | OVER-BUDGET |
| 64 | 32 | 34 | ~2^60 | D15 | 450 | 64 | OVER-BUDGET |

Counts are exactly D·(n−t) — no collisions observed; the channel is additive. Subset overlap is
NOT an obstruction (t > n/2 cells work: n=64 used 15 mutually overlapping 34-subsets). The
channel is p-free: identical counts at every field size (this is exact algebra, unlike the
G84/G85 small-field combinatorial channel which collapses at large p).

## Production transfer

At n=2^30, k=2^29, t = 553648129 (G87's wall threshold): n−t = 31·2^24 − 1 ≈ 5.2·10^8 per
degenerate subset; rank budget admits D ≤ 30; already **D = 3 yields ≈ 1.56·10^9 > 2^30
budget** (margin ≈ 1.5×; collisions would have to eat 31% of the yield to save the cap, against
exact additivity at both probed scales). The construction is explicit linear algebra
(solve 2(t−k)D homogeneous conditions in a 2^31-dim stack space; kernel is astronomically
larger than the codeword-pair subspace).

## Consequences (honest scope)

- The exact-pin route `hcount ⟹ δ* = 31/64` keeps its (vacuously conditional) validity but its
  hypothesis is unsatisfiable: **the all-stack scalar cap at the 31/64 predecessor is false.**
  This parallels the file's own half-predecessor refutation, one rung down.
- NOT affected: the unconditional bracket `178956971/2^30 ≤ δ* ≤ 31/64`, the packing ceilings,
  and everything on the floor side.
- The exact-pin program must move to a guarded count (stacks without degenerate subsets — but
  G86/G87 show the syzygy/degenerate channel is precisely what the rank dichotomy isolates), a
  radius where the channel starves (n−t < budget/D_max has no solution at this shape:
  the channel dies only when n−t ≤ 2^30/30, i.e. t ≥ n − 2^25ish — far below Johnson), or a
  different count altogether (e.g. distinct witness codewords instead of scalars).
- Recommended next Lean artifact: formalize ¬hcount via the explicit construction (existence of
  a degenerate-D3 stack + the γₓ pencil; the only nontrivial ingredient is distinctness of
  enough γₓ values, which can be forced constructively rather than generically).

Probe: deterministic, exact arithmetic; run `python3 scripts/probes/probe_syzygy_configuration_bad_counts.py`.
Issue #466 / #507 / #505. Tag SYZ1 (G88/G89 tags were already taken by concurrent lanes).
