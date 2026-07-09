# #466 R286: subconvexity lens

Date: 2026-07-09

## Pivot

The right way to view the remaining prize core is as a subconvexity problem.
The finite micro-band certificates are useful bookkeeping, but they do not
explain the wall.  The live analytic object is a thin-subgroup character-sum
subconvexity statement, plus its incidence/hyperplane upgrade.

## Convexity scale

For a smooth multiplicative subgroup `G = μ_n ⊂ F_q`, the basic period is

```text
η_b = Σ_{x ∈ G} ψ(bx).
```

The convexity/triangle scale is `|η_b| <= n`.  Parseval gives only the average
square-root floor:

```text
Σ_{b≠0} |η_b|^2 = q n - n^2,
max_{b≠0} |η_b| ≳ sqrt(n).
```

The prize needs a worst-case upper bound close to that floor:

```text
|η_b|^2 <= C n log(q/n)
```

or `|η_b| <= C sqrt(n log(q/n))`.  This is the generalized-Paley/BGK
subconvexity face.

## Not enough: the sup-norm face

The in-tree interface is:

```text
InteriorWorstCaseIncompleteSum.WorstCaseIncompleteSumBound ψ G M
```

and `GeneralizedPaleyRamanujan.lean` packages the near-Ramanujan-up-to-`sqrt log`
form:

```text
GeneralizedPaleyNearRamanujan C ψ G
  := ∀ b ≠ 0, |η_b|^2 <= C |G| log(|F|/|G|).
```

This is genuine subconvexity, but the dossier's Round 13 correction is crucial:
the period sup-norm controls only an average hyperplane incidence.  It is
necessary context, not a full prize floor.

## Prize-bearing subconvexity: hyperplane cancellation

The floor consumes:

```text
OpenCoreConditionalPin.WorstCaseIncidenceBounded C δ B
```

At prize scale, `B ≈ q ε* ≈ n`.  The subconvexity statement that matters is
therefore not just pointwise `η_b`, but worst-case square-root cancellation in
the incidence autocorrelation/hyperplane sum.  In dossier language:

```text
WallHolds ∧ HyperplaneCancellation
```

where:

```text
WallHolds
  = BGK/Wick moment subconvexity, giving the Paley sup-norm M;

HyperplaneCancellation
  = BCHKS-1.12-style worst-case √q·B cancellation in the far-line incidence.
```

The second input is not a function of the first; the existing Round 13
machinery records same-moduli spectra with different worst-case incidence.

## Concrete attack target

The updated subconvexity package should be stated as:

```text
SubconvexityPackage(C, δ, B):
  1. WorstCaseIncompleteSumBound ψ G M
       with M <= C n log(q/n)
  2. WorstCaseIncidenceBounded C δ B
       with B/q <= ε*
```

The existing theorem

```text
Frontier.PrizeFloorOfBGK.prizeFloor_of_BGK_and_incidence
```

already proves that this package pins the δ* floor.  The remaining mathematical
work is to prove the package, and the actual subconvexity bottleneck is the
second hyperplane-cancellation clause.

## Working heuristic

Treat the finite micro-band tail as numerical evidence for the same phenomenon:
once the edge shoulders are certified away, the residual survival distribution
looks subconvex rather than convexity-limited:

```text
M >= 25000 cached tail:
  max S(0.75) = 0.39019695
  max q60     = 0.72248056
```

But this is only evidence.  A prize proof must promote the observed cancellation
to a uniform hyperplane-incidence subconvexity theorem.
