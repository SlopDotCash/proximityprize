# δ* sweep A16 — exact w=4 orbit count `#orbits = n/4 − 1` (cyclotomic brick)

**Date:** 2026-06-14 · **Actionable:** A16 (`400-T04`) · **Type:** lean-brick + probe
**Status:** PARTIAL (lower bound + exact mechanism PROVEN axiom-clean; upper bound = named-open Lam–Leung)

## The claim (from #400 data)

For the dyadic domain `μ_n`, `n = 2^μ`, the number of `μ_n`-orbits of size-4 subsets
`S ⊆ μ_n` with `e₂(S) = 0` (vanishing second elementary symmetric function) and `e₁(S) ≠ 0`
(nonvanishing first power sum) is exactly

  `#orbits = n/4 − 1`.

Data (exhaustive **exact** enumeration over `ℤ[ζ_n]/(X^{n/2}+1)`, no floating point):
`n = 8,16,32,64,128 ↦ 1,3,7,15,31 = n/4 − 1`. (`scripts/probes/sweep_A16_orbitcount_w4.py`)

## The structure (machine-discovered)

Every orbit has a canonical representative whose four roots, with `w = ζ^j` (and `ζ^{n/2} = −1`,
so `ζ^{n/2+j} = −w`), are

  `S_j = { 1, w, w², −w }`,   `j = 1, …, n/4 − 1`.

In exponent coordinates (`ZMod n`, multiplication by `ζ^t` ≙ translation by `t`):
`S_j = {0, j, 2j, n/2 + j}`. The verified facts:

* `e₂(1, w, w², −w) = w + w² − w + w³ − w² − w³ = 0` — a **pure ring identity**, identically zero;
  the `e₂=0` certificate is NOT a cyclotomic coincidence (no reduction mod `Φ_n` needed).
* `e₁(1, w, w², −w) = 1 + w²`, so `e₁ = 0 ⟺ w² = −1 ⟺ ζ^{2j} = ζ^{n/2} ⟺ j = n/4`.
  The excluded `j = n/4` is precisely the `μ_4`-coset `{1, i, −1, −i}` (`e₁ = 0`), explaining the
  `−1` in `n/4 − 1`.
* The `n/4 − 1` representatives are pairwise distinct (separating witness: the element `2M + j`,
  `M = n/4`, lies in `S_j` but in no other `S_i` for `1 ≤ i,j ≤ M−1`).

The antipodal pairing of the six pairwise-sum exponents into three `n/2`-difference pairs holds
for *all* `e₂=0` quartets (verified: `e2zero == antipodal-paired` count at every `n ≤ 64`),
which is the combinatorial shadow of the Lam–Leung classification.

## What is PROVEN (axiom-clean Lean) vs OPEN

Artifact: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A16_OrbitCountW4.lean`
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

PROVEN, fully general in `M = n/4`:
* `e2_quartet_eq_zero`, `e1_quartet_eq`, `e1_quartet_ne_zero_iff` — the exact ring identities.
* `exponentRep`, `exponentRep_card = 4` — the canonical reps as 4-element `ZMod (4M)` subsets.
* `exponentRep_injective`, `repFamily_card = M − 1` — the `n/4 − 1` distinct representatives
  (the lower-bound content `#orbits ≥ n/4 − 1`).
* `orbit_count_eq_of_surjective` — the honest conditional assembly `#orbits = n/4 − 1`.

OPEN (named `Prop`, NOT discharged — no fabrication):
* `OrbitCountW4Surjective` — that every `e₂=0,e₁≠0` quartet is `μ_n`-equivalent to some `S_j`
  (equivalently: every vanishing sum of six `2^μ`-th roots is a `ℤ≥0`-combination of rotated
  antipodal pairs = **Lam–Leung**). Mathlib lacks Lam–Leung. Numerically true for all `n ≤ 64`.

## Honest verdict

A real landable cyclotomic brick: the `Θ(n²)`-style empirical refutation data (400-T04) is now a
**theorem** for its exact-mechanism + lower-bound content, with the upper bound isolated as the
single named Lam–Leung input. The `e₂=0` identity being *formal* (true in any commutative ring)
is the cleanest takeaway and likely generalizes the `w`-dependence to higher even window weights
(the `quartet` pattern `{1, w, w², −w}` is the `w=4` instance of a `{±w^a}`-balanced family).
This is δ*-relevant only as census bookkeeping (relevance 5); the prize wall is unchanged.

Probes: `scripts/probes/sweep_A16_orbitcount_w4.py` (orbit count + antipodal check),
`scripts/probes/sweep_A16_structure.py` (the `S_j = {0,j,2j,n/2+j}` characterization).
