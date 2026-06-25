# Delta-star #464 critical assault: floor polarity, Door-IV gauges, and the remaining wall

Date: 2026-06-25.

Status: no prize proof. This note consolidates the current #464 loop after rereading the issue
dossier, the ProximityGap workbench, the Paley/BGK map, the residual census, the local Frontier
files, and the searched PDF library.

## Evidence base

Local documents and code surfaces checked:

- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`, including the late §16 correction.
- `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`.
- `ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/FarCosetExplosion.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AssaultV2_FloorLocalizationN32.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorLinnikThornerZamanArrow.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvCensusF317.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DoorIVOrderedWalkDoobMajorant.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P2ZqIrreducibilityNoGo.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvDIR9OrderedWalkMajorant.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorDominationInterface.lean`.
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_IncidenceSmoothingDeconvolutionBarrier.lean`.
- `docs/references/proximity-gap-paley-spectrum/README.md`.
- `docs/wiki/residual-census.md`.

PDF inventory:

- `~/papers/arklib` contains 327 PDFs; `docs/references` adds 10 more, for 337 searched PDFs.
- The core extracted/read subset for this pass included ABF26, KKH, Chai-Fan, Diamond-Gruen,
  BGK/Chang, Heath-Brown-Konyagin, di Benedetto-Shkredov-style subgroup exponential sums,
  Kowalski's BGK exposition, generalized Paley spectrum papers, Lam-Leung, Gaussian-period moment
  papers, and the local Paley reference map.
- The local `eprint-2026-782-HKK-FailureProximityGaps.pdf` artifact is not a valid PDF in this
  checkout. I did not rely on it as a primary source.

Live issue audit:

- I reread issue #464 via the GitHub API on 2026-06-25. The issue is open; the last fetched comment
  was `2026-06-22T10:14:58Z`, a Door-IV Lane 1/3 receipt pinning the exact `sqrt(2)` per-level
  obstruction threshold.
- The newest comment cluster after the dossier is internally consistent with this note's verdict:
  Door-IV gap/curvature/spectrum/local-run levers are negative structural results; the dyadic
  per-level growth floor is a lower-bound obstruction, not a core upper bound; and the off-BGK
  floor-selector line is useful only as binder-predicate obstruction removal unless paired with a
  universal stack-domination theorem.

## Corrected theorem landscape

The prize-facing lower pin is not "no known binder obstruction." In Lean, the consumer is the
universal incidence input

```text
WorstCaseIncidenceBounded C delta B
```

from `OpenCoreConditionalPin.lean`: every word stack / far direction must have at most the budgeted
number of bad scalars. The one-family surface in `FarCosetExplosion.lean` gives a lower bound on
`epsMCA` from a supplied far direction. It proves that a bad binder family is an obstruction. It does
not prove that removing that obstruction upper-bounds the supremum.

This is the polarity error that was still leaking through older §9 prose:

```text
forall directions, count(direction) <= B     -> count(binder) <= B
count(binder) <= B                           does not imply forall directions, count(direction) <= B
single <= global and single <= B             does not imply global <= B
```

The new guardrail `FloorNecessaryNotSufficient.lean` formalizes this abstractly. It is small, but it
prevents the most dangerous false closure.

## Attack 1: bad-prime floor selector

Proposed tool:

```text
FloorSelector(a):
  for p prime, p == 1 mod 2^a,
  FloorBad(2^a,p) iff p is the least prime 1 mod 2^a.
```

If `FloorSelector(a)` holds uniformly and the least prime is below `(2^a)^4`, then every prize-scale
prime is good for this explicit binder-floor predicate.

What was proved/refuted in this loop:

- The `n^5 << n^4` shortcut is false. `_FloorLinnikExponentGate.lean` proves the elementary gate:
  `(2^a)^4 < (2^a)^5`, while a `2 * n^3` supply is safely below `n^4`.
- The Thorner-Zaman-style interface remains the right conditional shape: a supply window with
  `beta <= 3` would be enough for the least-prime piece.
- The selector is not just discriminant ramification. Existing n=32 defect-core files separate the
  visible ramification set from the claimed floor-bad set.
- Most importantly: even a perfect selector plus a sub-4 AP-prime theorem proves only
  `not FloorBad(2^a,p)`. It is necessary obstruction removal, not `WorstCaseIncidenceBounded`.

Surviving research value:

The selector is still worth formalizing because it certifies that the explicit KKH/binder obstruction
does not fire at prize primes. It should be documented as

```text
binder_family_good_at_prize_primes
```

not as a delta-star proof.

## Attack 2: profile selector algebra

Invented tool:

```text
Profile(a,t)
M_Profile
I_Profile
DegenerateProfile
SelectorIdeal(a)
```

The hope is to replace ad hoc probes by a typed algebra of adjacent agreement profiles. The target
would be a structural theorem:

```text
ProfileFreezeAfterLeast:
  if p == 1 mod 2^a and p is above the least such prime,
  every nondegenerate seventh-type profile either freezes to six-type
  or has full rank.
```

Why it is new:

- It is p-sensitive without being a character-sum estimate.
- It targets exact rank failures instead of averaged period magnitudes.
- It could explain why the least prime is bad while later primes are good.

Why it currently fails as a prize proof:

- "Above the least prime" is not an algebraic property of a fixed ideal in `Z[zeta]`.
- Norm/resultant height bounds are exponential in `phi(n)` and reintroduce the old conjugate-count
  wall.
- Even if the profile theorem is true, it still controls only the modeled profile class unless a
  separate all-stack domination theorem is proved.

## Attack 3: Door-IV scalar potential gauges

Proposed tool:

Instead of bounding the raw dyadic period magnitude

```text
M_top <= K * M_child,
```

introduce a scalar potential `Phi` and prove

```text
Phi_top <= K * Phi_child.
```

The hope was that `Phi` contracts by `sqrt(2)` even when the raw worst-frequency split has a coherent
per-level floor above `sqrt(2)`.

Lean refutation:

`_DoorIVPotentialGaugeBarrier.lean` proves:

```text
c * M_child <= M_top
lo * M_top <= Phi_top
Phi_child <= hi * M_child
Phi_top <= K * Phi_child
--------------------------------
lo * c <= K * hi
```

So a normalized faithful scalar potential cannot beat the true per-level floor. A non-normalized
potential only hides the missing factor in its distortion `hi / lo`. If `Phi` is not comparable to
the true magnitude, it no longer returns the needed period or incidence bound.

Surviving research value:

Door-IV can only survive as a nonlocal vector or incidence functional. A bounded-distortion scalar
gauge is dead.

## Attack 4: ordered walks and Doob

Existing code already reduces the ordered-walk lane.

- `running max >= endpoint`, so a uniform prize bound for the running max is at least as hard as the
  endpoint bound.
- Honest Doob/Burkholder inputs see quadratic variation or an average over frequencies; that is
  phase-blind and returns the energy wall.
- The prime cyclic fiber has no nontrivial equivariant filtration; non-equivariant filtrations lose
  exactly the phase information the prize needs.

Surviving research value:

Only a genuinely phase-aware square-function theorem remains, and that theorem would essentially be
the BGK/Paley wall in ordered-walk language.

## Attack 5: incidence smoothing and deconvolution

Proposed tool:

Smooth the bad-scalar / offset-incidence profile, prove a better bound for the smoothed profile, and
recover the raw worst-case incidence by deconvolution.

Lean refutation:

`_IncidenceSmoothingDeconvolutionBarrier.lean` proves the bookkeeping obstruction:

```text
raw <= R * smooth
smooth <= B
--------------
raw <= R * B
```

So the inverse norm `R` has to fit inside the prize budget. A killed mode is worse: the smoothed
profile can be zero while the raw worst-case component is still above target. Therefore a smoothing
proof must either keep an invertible multiplier on every prize-relevant mode with acceptable inverse
loss, or prove a separate structural theorem excluding the lost modes.

Surviving research value:

Smoothing is not dead, but it cannot be used as a free regularization. Its proof obligation is
exactly the inverse-loss budget plus a no-kernel theorem for worst-case incidence modes.

## Attack 6: direct Paley/Wick transfer

This remains the real core. The equivalent forms are:

```text
M(mu_n) <= C * sqrt(n * log(p/n))
DC-subtracted Wick transfer to r ~ log q
Worst-case Paley eigenvalue bound for Cay(F_p, mu_n)
WorstCaseIncidenceBounded / BCHKS hyperplane cancellation
```

The local and PDF evidence still says:

- HBK/Stepanov/Weil technology is vacuous or sqrt(p)-limited in this thin `n approx p^{1/4}` window.
- di Benedetto-type subgroup estimates improve classical ranges but do not reach the prize scale.
- BGK/Chang is the surviving analytic input, but the effective constant/range needed here is not in
  the literature.
- Moment methods close the characteristic-zero face and fail exactly at characteristic-p transfer
  depth `r ~ log q`.

This route is not refuted. It is open.

## What new math would actually move the prize

The next theorem must be universal, not binder-local. Plausible statement shapes:

```text
AllStackDominatedBySparse3:
  every stack attaining the window worst case reduces, budget-preservingly,
  to a fixed sparse monomial/profile family.
```

```text
HyperplaneCancellationOperator:
  the BCHKS annihilator-hyperplane deviation is O(sqrt(q) * B)
  for every stack in the window, without first passing through a scalar M bound.
```

```text
PhaseAwareWickTransfer:
  short +/-1 relations among 2^a-th roots modulo p have Wick-rate tails
  uniformly up to r ~ log q, after subtracting the DC/wraparound contribution.
```

```text
WorstCaseVerticalSatoTate:
  every nonprincipal Gaussian period in the dyadic thin subgroup family has
  effective sub-Gaussian tails at the prize scale.
```

The first would be genuinely off-wall if it is true. The other three are different languages for the
analytic wall. None is currently proved.

## Verdict

Four new tools survived as useful guardrails or interfaces, not as prize machinery:

- Supremum polarity: one binder-family floor theorem cannot upper-bound a worst-case stack supremum.
- Domination interface: binder-goodness would become prize-facing only after a real all-stack
  domination theorem.
- Gauge distortion: a faithful scalar potential cannot hide a coherent dyadic floor.
- Deconvolution budget: smoothed incidence bounds must pay the inverse multiplier norm and cannot
  ignore killed modes.

The bad-prime floor selector remains a worthwhile arithmetic obstruction check. It should no longer
be described as a route to δ\* unless paired with a new theorem that dominates all stacks by the
binder/profile family. Door-IV scalar gauges are refuted. Incidence smoothing is budget-constrained.
Ordered-walk Doob is reduced. The prize core remains the universal incidence / Paley-BGK
cancellation problem.
