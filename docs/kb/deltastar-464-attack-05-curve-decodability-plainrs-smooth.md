# Attack #05 — GG25 curve decodability: closing the curve list-size for plain smooth RS

Issue #464/#444/#407. Angle: the GG25 (ePrint 2025/2054) curve-decodability engine is proven
axiom-clean; δ* is pinned the instant a single `CurveListSizeLe` instance lands (m = poly(n) for
plain RS at the prize point). Levers probed: (a) a smooth-domain-specific curve list-size bound;
(b) whether the plain-RS curve list-size equals the Paley wall or a different/easier object.

## Target theorem

> For explicit plain smooth-domain RS at the prize point (n = 2^30, ε* = 2^-128, δ in the window
> interior (1-√ρ, 1-ρ-Θ(1/log n)) strictly above Johnson), establish
> `CurveListSizeLe (RS-code) ℓ δ m` with `m = poly(n)`. By `curveDecodable_of_curveListSize`
> (proven) + `GG25SpreadBound`/`GG25MCAFromCurveDecodability` (proven), this pins δ* and closes
> the prize.

## What was established (axiom-clean, new)

File `Frontier/_Attack05CurveListSizeReducesToRSList.lean` (verified `[propext, Classical.choice,
Quot.sound]`, no sorryAx):

1. `curveListSize_le_prod_rowList` — the distinct-curve count in any `CurveAssignment` image is
   `≤ ∏_{j≤ℓ} (rowList j).card`, where `rowList j` is the set of distinct codewords appearing in
   row `j` over the close set. Proof: the curve image injects into `Fintype.piFinset` of the row
   lists (a curve is its tuple of rows).
2. `curveListSize_le_pow_of_rowList_le` — if every per-row list has size `≤ L` then the curve
   list-size is `≤ L^(ℓ+1)`, i.e. `m = L^(ℓ+1)`.

This **pins the curve list-size object exactly**: `m` is governed by `L`, the per-row count of
distinct RS codewords agreeing with the seed-data row on `≥ (1-δ)n` coordinates — i.e. the
**list-decoding list size of the fixed RS code at radius δ**.

## The lever analysis

### Lever (b): is the plain-RS curve list-size the Paley wall, or a different object?

It is **NOT** input (1) (the generalized-Paley eigenvalue `M = max_{b≠0}|η_b|`). The per-row list
size `L` is a list-decoding count, and bounding it for *fixed explicit RS above Johnson* is exactly
the BCHKS line-ball incidence (input 2, Conjecture 1.12): the number of codewords within radius δ
of a word equals the number of low-degree polynomials whose graph meets the received word's
weight-⌊δn⌋ ball, which is the affine-line × syndrome-ball incidence with √q cancellation. So
angle #05 routes to **input (2)**, the same wall that `_PrizeFloorOfBGK` already reduces to. The
prior agent A6a26's claim ("reduces to BCHKS 1.12") is **confirmed independently** — and sharpened:
it is input (2), not input (1). The curve route does not bypass Paley.

### Lever (a): does smoothness of the eval domain give a curve-specific bound?

The GG25 spread bound (`GG25SpreadBound.lean`, Lemma 3.2) is a pure **degree-ℓ root bound** on the
combiner parameter α — it uses `Polynomial.card_roots'`, not the multiplicative structure of the
domain μ_n. Smoothness enters only through the per-row list size `L`, i.e. only through input (2).
A smooth-domain agreement set of two close codeword-curves is the vanishing locus of a low-degree
bivariate polynomial on μ_n × F; the smoothness (μ_n a multiplicative subgroup) is exactly what
makes the incomplete character sum over μ_n the controlling quantity — i.e. it is the √q-cancellation
object, again input (2). Smoothness does not supply an *independent* bound; it is the very source of
the wall.

### The one genuinely-different GG25 lever, and why it fails for plain RS

GG25 obtains `m = O(1/η)` for folded-RS / multiplicity / random-RS / subspace-design codes via a
**list-recovery / subspace-design argument that requires field size linear in n with a fresh random
(or designed) structure per seed**. The prize regime q ≈ n·2^128 IS field-size-linear-in-n — this
is the tantalizing part. But the GG25 argument needs the *rows* of the stack to carry independent
randomness / subspace-design structure; **plain fixed RS has no such per-seed randomness** — its
rows are the fixed RS code. So the GG25 list-recovery step does not fire, and `L` falls back to the
worst-case RS list size above Johnson = input (2). This is the exact step where the smooth-domain
curve route reduces to the wall.

## Refutation of any "closure" claim

Could one hope `L = poly(n)` unconditionally above Johnson for fixed RS? No: above the Johnson
radius the RS list size is not known to be polynomial for fixed explicit RS (only at/below Johnson,
via the unconditional `JohnsonListBound`). The window interior (1-√ρ, 1-ρ-Θ(1/log n)) is strictly
above Johnson by construction, precisely where no poly(n) list bound is known without the √q
cancellation. Any `CurveListSizeLe` instance with m=poly(n) at the prize point would, via
`curveListSize_le_prod_rowList` read backwards, supply an above-Johnson poly RS list bound — which
is open and equivalent to BCHKS 1.12. So this angle cannot produce an unconditional closure; the
adversarial self-refutation stands.

## Honest verdict

- **proofStatus: reduces-to-paley** (more precisely, reduces to input (2) = BCHKS Conj 1.12, the
  hyperplane upgrade — the prize's actual load-bearing input).
- **bypassesPaley: false.** The curve list-size is the per-row RS list size above Johnson, which is
  the line-ball √q-cancellation object. Smoothness is the *source* of the wall, not an escape.
- **Value delivered:** a new axiom-clean structural factorization
  (`curveListSize_le_prod_rowList` / `_le_pow_of_rowList_le`) that pins the GG25 curve list-size to
  the per-row RS list-decoding list size, making precise that the open input is input (2), and
  identifying the exact failure step (no per-seed randomness in plain RS ⟹ GG25's field-linear
  list-recovery lever is unavailable).
- **namedOpenInput:** the per-row RS list-size bound above Johnson = `RSCurveListSizeResidual` /
  BCHKS Conjecture 1.12 (`WorstCaseIncidenceBounded`).

This is a genuine conditional/structural result and a clean reduction identification, not a closure.
