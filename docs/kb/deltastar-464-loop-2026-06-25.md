# Delta-star grind loop, 2026-06-25: the floor-selector route after the Linnik audit

## Executive state

I reread the live #464 issue, the in-tree v2 dossier, the ProximityGap agent guide, the Paley/BGK
paper map, the residual census, and the local bad-prime/resultant/frontier files. The prize is not
closed in this pass. The current state is sharper:

1. The analytic floor route still hits the BGK/Paley wall: prove square-root cancellation for
   dyadic thin-subgroup Gauss periods, or equivalently a DC-subtracted Wick transfer to depth
   `r ~ log q`.
2. The only route that is not itself a character-sum estimate is the off-BGK floor-selector
   obstruction check: characterize binder-family floor-bad primes as the least prime in the
   progression `1 mod n`, then show that least prime is below the prize scale `n^4`.
3. The issue/dossier wording around "Linnik gives n^5 << n^4" was too strong. Exponent 5 is
   above prize scale, not below it. The useful prime input is a sub-4 theorem: the in-tree
   `TZPrimeSupply`/`ThornerZamanPNT` bridge at `beta <= 3`, GRH/Montgomery-level input, or a
   dyadic-special least-prime theorem.
4. The later correction is more important than the prime-supply audit: even a perfect
   floor-selector theorem would prove `¬ FloorBad` for one modeled binder predicate, not the
   universal `WorstCaseIncidenceBounded` statement consumed by the delta-star lower pin.
5. The real hard input in the floor-selector obstruction check is therefore not generic least-prime
   existence. It is the uniform algebraic localization statement:

   `FloorLocalizationUniform FloorBad`:
   for all `a >= 4`, `FloorBad (2^a) p` iff `p` is the least prime `1 mod 2^a`.

The pass added two small Lean guardrails:

- `_FloorLinnikExponentGate.lean`, preventing the old `n^5 << n^4` exponent mistake.
- `FloorNecessaryNotSufficient.lean`, preventing the false converse from one binder family to all
  stacks.

It also corrected `_AssaultV2_FloorLocalizationN32.lean` and the canonical dossier so the route no
longer overclaims ordinary Linnik or prize closure.

## Evidence base actually inspected

Local artifacts:

- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`
- `ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md`
- `docs/wiki/residual-census.md`
- `docs/references/proximity-gap-paley-spectrum/README.md`
- `ArkLib/Data/CodingTheory/ProximityGap/PROXIMITY_PRIZE_WORKBENCH.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/KKH26ThornerZaman.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AssaultV2_FloorLocalizationN32.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorLinnikRungInstances.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorLinnikThornerZamanArrow.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorLinnikTZClosure.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_AvD2_LinnikWindowCountRequired.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorBadRamificationDisjoint.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorBadDefectTowerInvariant.lean`
- `scripts/probes/probe_444_floorbad_ramif.py`
- `scripts/probes/probe_444_floorbad_defect_tower_invariant.py`

Paper library status:

- The local library contains the Paley/BGK/HBK/Kowalski/Shkredov/di Benedetto/Gauss-period/Lam-Leung
  PDFs already summarized by `docs/references/proximity-gap-paley-spectrum/README.md`.
- The relevant outside check for this pass was Thorner-Zaman 2024, `arXiv:2108.10878`, whose abstract
  states it proves a refined PNT in APs with improvements for powerful moduli. The in-tree Lean layer
  still correctly treats this as a named hypothesis, not a formal theorem.

## Attack 1: use least primes to close the binder floor predicate

### Proposed tool

Define the floor-bad selector as a finite algebraic object rather than a character sum.

For each dyadic `n = 2^a`, let `FloorBad(n,p)` mean that the adjacent seventh-type agreement profile
is realizable over `F_p` for the relevant binder word. The proposed theorem is:

`FloorSelector(a)`:
for primes `p == 1 mod 2^a`, `FloorBad(2^a,p)` iff `p = P_a`, where `P_a` is the least prime
`1 mod 2^a`.

If this holds, and `P_a < (2^a)^4`, then every prize-scale prime is floor-good for this predicate.

This is attractive because it asks for a zero-dimensional realization theorem over fixed
cyclotomic data. It is not a bound on

`max_b |sum_{x in mu_n} exp(2*pi*i*b*x/p)|`.

### Immediate refutation of the naive prime-theorem step

The phrase "Linnik gives `P_a << n^5 << n^4`" is false as an exponent comparison. For every
nontrivial dyadic `n`,

`n^4 < n^5`.

So classical exponent-5 Linnik does not put the least prime below prize scale. The formal guardrail is:

- `dyadic_prize_scale_lt_fifth_power`
- `not_fifth_power_le_prize_scale`
- `two_mul_cube_le_fourth`
- `exponent_gate_summary`

This does not kill the floor-selector obstruction check; it removes a bad shortcut. The correct
prime-supply route is already present:

- `TZPrimeSupply n beta 1` gives a prime `p <= 2 n^beta`.
- If `beta <= 3` and `n >= 2`, then `2 n^beta <= n^4`.
- Therefore a uniform `TZPrimeSupply` family at `beta <= 3` gives `LinnikLeastPrimeBelowPrize`.

The analytic [TZ] input remains a named hypothesis in Lean; that is honest.

### Refutation of the proof-orientation step

The more serious failure is logical. The prize-facing API is:

```text
WorstCaseIncidenceBounded C delta B
```

which is a `forall` bound over every word stack / far direction. The floor-selector lane supplies
information about one distinguished binder family. The Lean guardrail
`FloorNecessaryNotSufficient.lean` proves the abstract polarity:

```text
forall i, count(i) <= B     -> count(i0) <= B
count(i0) <= B              -/-> forall i, count(i) <= B
single <= global and single <= B -/-> global <= B
```

So even if `FloorSelector(a)` is true and the least prime is sub-prize, the theorem shape is only

```text
not FloorBad(2^a,p)
```

for a supplied predicate. It is necessary obstruction removal. It is not a proof of the delta-star
floor unless one adds a new domination theorem reducing all stacks to that binder predicate.

### The harder refutation: ramification is not floor-badness

The most tempting algebraic route is to identify floor-bad primes with ramification or discriminant
drop of the defect polynomial. The tree already kills this for `n = 32`:

- The quartic defect core has odd ramification `{17,257}`.
- The claimed floor-bad prime is `97`, the least prime `1 mod 32`.
- `97` is unramified and has full root count for the displayed quartic.

So the selector is not "prime divides the discriminant." It is a more delicate existence condition:
the prime must support a forbidden adjacent agreement profile, and that condition is not identical
to repeated roots of the visible defect polynomial.

### Current uncertainty

`_AssaultV2_FloorLocalizationN32.lean` honestly flags that the `n=32 -> {97}` claim was not
independently reproduced under one faithful-looking Vandermonde consistency model. That is not a
minor documentation issue: the floor-selector route cannot progress until the exact `FloorBad`
predicate is pinned tightly enough that probes, Lean statements, and dossier prose are discussing the
same object.

## Invented machinery: the Profile Selector Algebra

The next tool should not be "more resultants" in the abstract. It should be a typed algebra of
agreement profiles.

Objects:

- `Profile(a,t)`: a combinatorial adjacent-pattern type for `n = 2^a`, with `t` agreement classes.
- `M_Profile`: the exact universal matrix over `Z[zeta_n]` whose rank condition expresses
  realizability.
- `I_Profile`: the determinantal ideal of all consistency obstructions.
- `DegenerateProfile`: the profiles already explained by six-type freeze, full-group artifacts, or
  correlated `X^{n/2} = +/-1` directions.
- `SelectorIdeal(a)`: the product/intersection of `I_Profile` over nondegenerate seventh-type
  profiles.

The hoped-for theorem is not a height bound on `Norm(SelectorIdeal)`; that would reintroduce the
exponential conjugate-count wall. The theorem should be structural:

`ProfileFreezeAfterLeast`:
after reduction modulo any prime `p == 1 mod 2^a` with `p > P_a`, every nondegenerate seventh-type
profile either becomes six-type frozen or has full rank.

This says "badness is a first-prime packing artifact." It tries to use the order geometry of the
least AP prime, not cancellation among all conjugates.

Why this might be new:

- It is p-sensitive but not character-sum p-sensitive.
- It targets an L-infinity obstruction by classifying exact rank failures, not averaging periods.
- It explains why the least prime could be bad while later primes are good even when the visible
  discriminant does not select the bad prime.

Why it may fail:

- The phrase "after the least prime" is not algebraic in `Z[zeta_n]`; it is an ordering statement
  about primes. A fixed integer resultant cannot normally know which divisor is the least prime in an
  AP unless the actual condition uses density/packing of the embedded subgroup in `F_p`.
- If `SelectorIdeal` has any persistent prime divisor `q == 1 mod 2^a` above `P_a`, the theorem is
  false. The existing `n=32` reproduction warning means we do not yet even have a stable target.
- A generic height proof is exponential (`~2^n`) and useless; the method needs profile-specific
  cancellation or a rank normal form, not a crude norm bound.

## Attempted proof sketch and where it breaks

1. Work over `R_a = Z[T]/Phi_{2^a}(T)`.
2. For each adjacent seventh-type profile, form the augmented rank matrix `A_Profile(g)`.
3. The bad-prime condition is `rank(A) = rank([A|b])` after specializing a primitive `2^a`-th root
   into `F_p`.
4. If every nondegenerate profile has a minor whose value is a product of cyclotomic units times
   `(p - P_a)` or a monotone packing factor, then only `P_a` can be bad.

Break: step 4 is fantasy in the current algebra. Minors live in `R_a`, not in ordered integers, and
their norms can have many prime divisors. The ramification-disjoint result proves the visible
discriminant is not the selector. A proof must find a canonical minor basis in which the nonleast
prime failures are killed by rank identities, not by size.

## Attack 2: return to Paley/BGK with the floor selector in hand

Suppose `FloorSelector(a)` is true. It still does not imply the full floor window. It gives a family
of primes that are good for the explicit adjacent seventh-type obstruction, but it does not bound the
Paley eigenvalue or arbitrary far-line incidence at prize primes. The only possible consumer bridge
would have to be explicit:

`not FloorBad(n,p)` -> the required `WorstCaseIncidenceBounded` at a window radius.

I did not find that implication as a proved final bridge in this pass, and the current closure theorem
only proves "not floor-bad" for the abstract predicate. The bridge should now be treated as a
separate missing theorem, not as an implicit consequence of the floor-selector statement.

If that bridge cannot be proved, the floor-selector route collapses back to BGK: it would only remove
one visible bad family, while arbitrary far-line incidence still needs the character-sum wall.

## Next concrete tasks

1. Pin the `FloorBad` predicate:
   write the exact finite-field rank condition from the probe into Lean as a decidable definition for
   small `a`, and make the `n=16` and `n=32` probes call the same model.

2. Reproduce or retract `n=32 -> {97}`:
   the current file records the claim but also says an independent model found no bad prime. This must
   be resolved before any uniform theorem is meaningful.

3. Prove or refute the consumer bridge:
   show whether any exact δ* floor statement follows from `¬ FloorBad(n,p)` for all prize primes.
   The expected answer is negative unless the bridge is really a domination theorem for all stacks.

4. Develop `Profile Selector Algebra`:
   start with a profile normal-form file that separates degeneracies from nondegenerate seventh-type
   profiles and produces explicit minor ideals for `a=4,5`.

5. Keep the analytic wall boxed:
   any route using only energy, moments, discriminants, norms, or root counts should be forced to
   state whether it proves `WorstCaseIncidenceBounded` or merely restates BGK.

## Verdict for this loop

The route survived as a useful off-BGK obstruction check, but both easy closure readings failed. The
useful new tool is not "Linnik closes the floor"; it is:

`FloorSelector + sub-4 AP-prime supply + a genuinely universal stack-domination theorem`.

The first and third pieces are still missing; the third is essentially the hard wall unless it has
new structure. The second piece is already packaged conditionally by the Thorner-Zaman supply
interface and now has a small exponent-gate Lean guardrail preventing the old overclaim from
re-entering.
