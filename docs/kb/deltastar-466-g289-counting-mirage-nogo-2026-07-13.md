---
id: deltastar-466-g289-counting-mirage-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, weighted-kernel, Cover-counting, Farkas, gate-independence, route-no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G289: the canonical bounded-degree feature no-gos are a dimension-counting mirage

## One-line

The weighted-kernel separation route is being closed one polynomial degree at a time (G286 odd
linear, G287 canonical quadratic, referee probes affine-2 / homogeneous-cubic), but every one of
those no-gos is forced by Cover function-counting rather than by the arithmetic of the CORE gate, and
the linear no-go is provably gate-independent: the same positive circuit kills the CORE gate and its
exact opposite. Bounded-degree canonical `(T2,T4,T8,T16)` features cannot certify the CORE covariance
sign. CORE remains open / on-BGK.

## The treadmill and why it is closed structurally

The sponsor census at `n=16` (`p<2600`, `p = 1 mod 16`, ranks `r in {5,6}`) has `N = 84` cells. The
generator-independent Ramanujan feature vector `(T2,T4,T8,T16)` has only `4` base coordinates,
because the admissible kernel index lives in the **thin 2-power tower** `<2> <= (Z/n)^*` and
Aut-invariance collapses the linear kernel-input normals to exactly `log2 n` Ramanujan aggregates.
Every bounded-degree polynomial feature span therefore has dimension `d = binom(4+D, D)`:

| degree D | affine dim d | Cover sep-fraction (N=84) | regime |
|---|---|---|---|
| 1 | 5 | 2.0e-19 | forced-by-counting (`d <= N/2`) |
| 2 | 15 | 3.4e-10 | forced-by-counting |
| 3 | 35 | 6.2e-02 | forced-by-counting (near crossover) |
| 4 | 70 | 1.0 | generic-separable (`d > N/2`) |
| 5 | 126 | 1.0 | generic-separable |

Cover's function-counting theorem: for `N` points in general position in `R^d`, the number of the
`2^N` sign dichotomies that a `d`-dimensional linear map can separate is
`C(N,d) = 2 * sum_{k<d} binom(N-1,k)`. The separable fraction `C(N,d)/2^N` is astronomically small
for every low degree (`d << N/2 = 42`). So a strict separator is astronomically non-generic and a
no-go is **forced by dimension counting**, carrying no information about the specific arithmetic gate.

## Gate independence is the sharp certificate of "no arithmetic content"

Model the census as raw (unsigned) feature vectors `f` and a gate `s : i -> {+-1}`; the gate-signed
vectors are `signedFeat f s i j = s i * f i j`. A strictly-positive Farkas circuit `(weight, hrel)`
for gate `s` is, verbatim, one for the flipped gate `s' = -s` with the identical positive weights
(negate the relation). Hence one positive circuit forbids a strict separator for a gate **and its
exact opposite** simultaneously, so the obstruction cannot be a function of the census signs.

The exact witness: five sponsor-faithful cells (`p in {113,337,401,433}`, ranks `{5,6}`, all avoiding
the degenerate `p=17` cell) with strictly-positive integer weights annihilate every one of the four
gate-signed canonical linear coordinates for the true CORE gate; the same weights annihilate the
negated gate. This is checked coordinatewise in Lean.

## Control experiment (informational, in the probe)

An exact-LP control over the full 84-cell census confirms the mechanism: random gate signs are
exactly as non-separable as the true CORE gate at every degree with `d <= N/2` (`0%` separable in
both cases through homogeneous quartic), and separation becomes generic (both real and random signs
separate) once `d > N/2`. The two apparent "separable" LP hits at `d=35` are boundary numerical
noise: exact rational re-evaluation of the recovered functional gives a strictly negative minimum,
so no real separator exists there either.

## Verdict for the frontier

Bounded-degree canonical `(T2,T4,T8,T16)` features can never certify the CORE covariance sign: below
the `d = N/2` crossover any no-go is a counting mirage, and above it separation is generic and equally
content-free. A surviving certificate must use **unbounded feature dimension, genuinely non-polynomial
structure, or new row-labelled arithmetic beyond the 2-power Ramanujan tower** (e.g. the full
`m=(p-1)/n`-term twisted Jacobi content that G228-G247 already rule out compressing). This is a
route-level no-go, not a sponsor estimate; it redirects effort away from the degree-by-degree
feature-separation program. CORE remains open / on-BGK.

## Formal payload

`_G289CountingMirageNoGo.lean`:
- `no_strict_separator_of_positive_relation` (positive circuit forbids a strict separator; local copy
  of the G287 obstruction),
- `flip_gate_relation` (same positive weights annihilate the negated gate),
- `gate_independent_no_go` (a positive circuit forbids a separator for a gate and its exact opposite),
- `circuitWeight_pos`, `census_farkas_relation` (exact five-cell circuit, four coordinate identities),
- `no_canonical_linear_separator_gate_independent` (the gate-independent census no-go).

Axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axioms.
Exact probe `scripts/probes/g289_counting_mirage_nogo.py`: gate A (Cover ceiling, exact integers) and
gate B (exact gate-independent 5-cell circuit) both hard `SystemExit(1)` on failure; PASS.

## Orthogonality

Complements rather than overlaps G286 (odd-linear parity no-go), G287 (canonical quadratic Farkas
circuit), G282/G285 (carry-Fourier / kernel-domain characters). Those close specific degrees; G289
explains WHY they close and proves the closure is gate-independent (dimension-counting), so the whole
bounded-degree canonical-feature program is a mirage. Does not bound the covariance at production
primes and does not exclude unbounded-dimension or non-polynomial certificates. CORE OPEN / ON-BGK.
