# Issue #464 loop note: Door-IV potential gauges and why they do not thin the wall

Date: 2026-06-25.

Status: **negative structural progress**, not a prize proof.  This note records one more
propose -> attack -> refute loop against the current #464 frontier.

## Evidence read this pass

- Issue #464 body and all 24 comments through 2026-06-22, especially the AssaultV2/V3/V4
  corrections and the late Door-IV comments.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`, including the §16 correction that the
  off-BGK floor is necessary but not sufficient.
- `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md` and
  `ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`.
- The local Paley/BGK reference map:
  `docs/references/proximity-gap-paley-spectrum/README.md` and
  `docs/references/proximity-gap-paley-spectrum/BRIDGE-house-and-randomwalk.md`.
- Targeted PDF text slices from the local library:
  `~/papers/arklib/eprint-2026-680-ABF26.pdf`,
  `~/papers/arklib/proximity-paley/BGK-gausssum-crma.pdf`,
  `~/papers/arklib/proximity-paley/arxiv-1809.09829.pdf`.
- PDF inventory: `~/papers/arklib` currently contains 327 PDFs; this loop did not re-read every
  page of every PDF, but it did use the canonical dossier plus the targeted primary PDFs for the
  definitions and wall statements.

## Current frontier after the issue comments

The latest comments close a large part of Door-IV Lane 1.  The observed worst frequency `b*`
has coherent dyadic pieces, but the coherence is a lower-bound obstruction, not an upper-bound
tool.  The half-mass split is real-collinear; the balance ratio is stationary in an `O(1)` band;
the `k`-piece split is partition-depth invariant; gap value, curvature, spectrum, and local-run
statistics are either dilation-invariant, generic, full-rank, or wrong-direction.  The remaining
live phrase in the issue is therefore not "gap geometry" but finer **multiplicative phase
arithmetic**.

The workbench also matters: the bare `M(μ_n) <= C sqrt(n log(p/n))` sup-bound is necessary but is
not by itself the operative incidence input.  The prize-facing input is a worst-case incidence /
`sqrt(q) * B` hyperplane-cancellation statement in the BCHKS 1.12 direction.  A local Door-IV
descent can still be interesting, but only if it produces a real worst-case incidence bound or a
strictly stronger phase-correlation theorem, not another average or local magnitude restatement.

## New attempted tool: potential-gauged dyadic descent

The failed Door-IV descents all try to control the true magnitude

```text
M_top = |A + B|
```

by passing to a child magnitude such as `M_child = |A|` or the max over the thinner subgroup.  The
natural next idea is to change variables: define a potential `Phi` on periods, not equal to `M`, and
prove a contraction

```text
Phi_top <= K * Phi_child
```

even when the raw magnitude has a lower floor

```text
c * M_child <= M_top.
```

If `K` can be `sqrt(2)` while `c` is measured above `sqrt(2)`, this would look like a way around the
coherence obstruction.  This is the same kind of maneuver that sometimes works in analysis: entropy,
energy, curvature, or a gauge norm contracts while the literal norm does not.

The key question is whether such a potential is actually new math or just a disguised rescaling of
the same wall.

## Lean result: the gauge must pay for the floor in distortion

I added a self-contained frontier lemma:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DoorIVPotentialGaugeBarrier.lean
```

Main theorem:

```lean
gauge_contraction_forces_distortion
```

Abstract statement: if the true magnitudes satisfy

```text
c * M_child <= M_top,
```

and the potential is comparable to the true magnitudes by

```text
lo * M_top <= Phi_top
Phi_child <= hi * M_child,
```

then any contraction

```text
Phi_top <= K * Phi_child
```

forces

```text
lo * c <= K * hi.
```

In normalized form (`lo = hi = 1`), every `K`-contraction forces `c <= K`.  So if the real per-level
floor is above `sqrt(2)`, a normalized potential cannot prove a `sqrt(2)` descent.  More generally,
the potential must have distortion

```text
hi / lo >= c / K.
```

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DoorIVPotentialGaugeBarrier.lean
```

passed in 16 seconds; the file is axiom-clean under the usual frontier audit and has no `sorry`.

## Critique of the attempted tool

This does not close the prize.  It refutes a proof architecture.

A potential method is only useful if the potential is still faithful enough to return a bound on the
actual period magnitude or incidence.  The lemma says: any faithful one-step potential inherits the
same per-level lower floor, up to its distortion.  Therefore a claimed `sqrt(2)` recursive proof has
to hide the excess in `hi / lo`.  If `hi / lo` grows down the dyadic tower, the proof has merely moved
the wall into a distortion product.  If `hi / lo` is uniformly bounded but bigger than `c/sqrt(2)`,
the final constant worsens by exactly the missing factor.  If `Phi` is not comparable to `M`, it no
longer proves the needed worst-case magnitude or incidence statement.

This is the same pattern as the Jacobi/Toda and half-mass stories: the reparameterization can be
honest and illuminating, but the final conversion back to the prize object is where the BGK/Paley
wall reappears.

## What survives

The only potential-style escape that survives this lemma is a **nonlocal, non-comparable** phase
functional that proves incidence directly without first proving a pointwise period magnitude bound.
That would have to exploit cancellation across the annihilator hyperplane in the workbench's
`WorstCaseIncidenceBounded` input.  It cannot be a scalar gauge sandwiched between constant multiples
of `M`.

That suggests the next real attack should be phrased as one of:

1. A vector-valued hyperplane-cancellation operator whose output is the incidence deviation, not the
   period sup.  It must prove a `sqrt(q) * B` cancellation and avoid the known `q * B` naive route.
2. A sparse-dominance theorem in the Chai-Fan Conj 7.1 surface: show that the unrestricted
   `>=3`-monomial worst case is dominated by the 3-position sparse family.  This bypasses scalar
   gauges and attacks the actual stack supremum.
3. A symmetric-function coset-rigidity theorem for the non-correlated monomial directions: prove the
   bad-scalar value set occupies `O(1)` `mu_n`-cosets at the binding radius.  This is finite
   cyclotomic algebra, not an average period bound, but it must control all directions, not just the
   binder floor family.
4. A genuinely new phase-correlation theorem on the quotient sequence `j -> eta(g^j)`, with an
   output that is an incidence bound.  Any local half-split, local gap statistic, scalar sign, or
   bounded-distortion gauge is now mapped and dead.

## Bottom line for the loop

The potential-gauge route fails cleanly: a faithful scalar potential cannot thin the coherent
per-level floor.  The result is useful because it prevents the next loop from hiding Door-IV under
renamed norms.  The next attack should leave scalar magnitudes entirely and target the workbench's
incidence input or the sparse/symmetric-function stack supremum directly.

No theorem here asserts `delta*`, `mcaConjecture`, BCHKS 1.12, or the Paley/BGK core.  The core remains
open.
