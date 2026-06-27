# Critical Loop: Autocorrelation SDP and Container Codegree-One

**Date:** 2026-06-27
**Issue:** #464
**Loop:** invent two nonstandard tools, try them, record exactly where each stops.
**Verdict:** no `delta*` proof. The SDP tool is a genuine partial power-saving over completion; the
container tool collapses for a new structural reason. Both leave the deployed floor at the same
worst-case incidence / flat-polynomial wall.

## Context From The Issue And Local Library

Issue #464 states the current core as the dyadic subgroup Gauss-period bound

```text
M(mu_n) = max_{b != 0} |sum_{x in mu_n} e_p(bx)| <= C * sqrt(n * log(p/n)).
```

The local PDF library confirms the routing:

- Podesta--Videla's generalized Paley graph paper identifies the spectrum of
  `Cay(F_q, R_k)` with Gaussian periods, so the graph/eigenvalue face is the same object.
- Kowalski's BGK exposition gives qualitative cancellation over small multiplicative subgroups,
  but the exponent is not the prize-scale `sqrt(n log p)` bound.
- Short-character-sum large-value and Burgess-box papers supply adjacent tools for character sums,
  but not a worst-case additive character sum over one fixed thin multiplicative subgroup.
- The local PDF-routing audit already maps ABF26, Kambire, GG25, random RS, BCHKS, roots-of-unity,
  and least-prime inputs to named gates; none supplies the missing universal incidence theorem.

So the useful question for a new loop is not "can we cite one more nearby paper?" It is:

1. can a new functional beat the `sqrt(p)` completion wall without assuming Paley?
2. can an information-theoretic/container argument compress the bad-scalar witness count directly?

The two Lean sockets below answer those questions.

## Tool 1: Degree-2 Autocorrelation SDP

File checked:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvSDP_AutocorrPowerSaving.lean
```

The idea is to rewrite the Gaussian periods as a DFT of the normalized Gauss-sum phase sequence.
Degree-1 LP only sees `||a||_2^2 = m`, which is the old `sqrt(p)` completion scale. Degree 2 also
sees the cyclic autocorrelation

```text
R(tau) = sum_t a_t * conjugate(a_{t+tau}).
```

The Lean file proves the abstract assembly:

- `autocorrL1_bound`: diagonal plus off-diagonal autocorrelation bounds give
  `m + (m - 1) * B`;
- `house_sq_le_of_sdp`: the house is bounded by the degree-2 SDP/autocorrelation envelope;
- `weil_const_below_sqrt_m`: a Weil-scale off-diagonal constant gives a non-vacuous improvement
  over `sqrt(p)` in the genuine large-index regime;
- `house_sq_prize_of_flat`: the prize would follow from the stronger flat-polynomial residual.

This is real movement: it gives a Paley-independent bracket strictly below completion if the
Jacobi/autocorrelation input is at Weil scale. It is not enough for the prize. The remaining factor
is `m^(1/4)` versus `sqrt(log m)`. That is the flat-polynomial problem for the explicit Gauss-sum
phase vector, which is just the Paley/BGK wall in a different coordinate system.

The critical lesson is that degree-2 SDP is not useless, but it is a halfway house. It improves
`sqrt(p)` to roughly `n^(1/4) p^(1/4)`, then stalls. Higher-degree SDPs reintroduce the deep moment
obligation `E_r <= Wick` at `r ~= log p`.

## Tool 2: Containers On The Bad-Configuration Hypergraph

File checked:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RadicalContainerCodegreeOne.lean
```

The radical hope was to stop analyzing `mu_n` directly and put containers on the hypergraph whose
vertices are scalars `gamma`, with edges representing bad configurations for a fixed stack. This is
not the same as the older container no-gos on additive structure of `mu_n`.

The obstruction is sharper and simpler than expected. For an active coordinate `i`,

```text
gamma |-> u0 i + gamma * u1 i
```

is injective. Therefore a single coordinate-value constraint has at most one scalar solution.
The Lean file proves:

- `affineLine_injective_of_active`;
- `codegree_one`;
- `bad_subset_card_le_of_codegree_one`;
- `badset_le_witnessCount`;
- `containerReducesToListSize_holds`.

Containers help when small cores have high codegree and the union bound is wasteful. Here the
codegree is already `1`. There is no redundancy to compress. The container output is the union
bound over witnesses, i.e. the line-restricted list size, which is exactly the Face-4 worst-case
incidence wall.

This is a new no-go mechanism: not phase blindness, not additive-energy saturation, not
linear-forms failure. It is scalar rigidity. The bad set is not container-compressible because an
active coordinate pins `gamma`.

## Refutation Of The Loop

The two tools fail in complementary ways.

The SDP tool is analytic and phase-aware. It extracts extra structure from the Gauss-sum phase
sequence, and it really beats completion. But degree 2 only controls an `L^1` autocorrelation
quantity. To hit the prize, it must be upgraded to a random-flat-polynomial sup bound for this
specific phase vector. That upgrade is the original wall.

The container tool is combinatorial and worst-case-facing. It tries to avoid Gauss sums entirely.
But the affine-line parameter is one-dimensional: a single active coordinate gives a linear equation
in `gamma`. This kills the high-codegree premise containers need. The method returns exactly the
list-size union bound, hence the open incidence theorem.

So this loop does not prove the floor. It narrows the shape of any future proof:

- A successful SDP proof must exploit high-order structure of the Gauss-sum phase vector beyond
  degree-2 autocorrelation, without degenerating into the already-known deep moment wall.
- A successful combinatorial proof cannot be a generic hypergraph-container theorem on bad
  configurations. It must use algebraic structure of the witness family that survives the
  codegree-one scalar rigidity.
- A successful off-BGK proof must dominate all far-line stacks, not just remove one binder-family
  obstruction.

## Verification

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvSDP_AutocorrPowerSaving.lean
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RadicalContainerCodegreeOne.lean
```

Both passed. The axiom audit reported only the expected classical/proof-irrelevance axioms and no
`sorryAx`.

## Next Tool To Try

The next non-duplicative target is a hybrid of these two failures:

```text
high-order autocorrelation containers on the Gauss-phase DFT,
not on scalar bad configurations.
```

That is, build a container/entropy argument on structured phase words `a_t = G(chi_t)/sqrt(p)`,
where codegrees are autocorrelation constraints rather than coordinate-value constraints. The win
condition is a deterministic flat-polynomial theorem

```text
||DFT(a)||_infty^2 <= C * m * log m
```

for the Gauss-sum phase sequence, using Hasse-Davenport/Jacobi cocycle identities as the structural
input. The first proof obligation is to show that those cocycle identities imply nontrivial
high-order autocorrelation entropy. If they only imply the degree-2 bound above, the route is dead.
