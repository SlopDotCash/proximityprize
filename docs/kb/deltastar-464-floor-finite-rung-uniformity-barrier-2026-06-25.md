# Issue #464: finite floor rungs do not prove uniform localization

Date: 2026-06-25.

Status: **logical guardrail**, not a delta-star proof.

## Inputs Checked

- Live issue #464 and the canonical dossier
  `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.
- The resolved off-BGK floor files:
  - `_AssaultV2_FloorLocalizationN32.lean`
  - `_FloorLinnikRungInstances.lean`
  - `_FloorLinnikThornerZamanArrow.lean`
  - `_FloorLinnikTZClosure.lean`
  - `_FloorLinnikExponentGate.lean`
  - `_FloorClosureContract.lean`
  - `_FloorDominationInterface.lean`
  - `FloorNecessaryNotSufficient.lean`

The current factual state is:

```text
a = 4, n = 16: floor-bad = {17}
a = 5, n = 32: floor-bad = {97}
```

Both match the proposed least-prime rule.  The needed input is stronger:

```text
for every a >= 4, floor-bad(2^a) = {least prime p == 1 mod 2^a}.
```

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorFiniteRungUniformityBarrier.lean
```

records the logical gap in the remaining off-BGK floor-localization lane.

The file abstracts the per-rung localization statement as a predicate

```lean
R : Nat -> Prop
```

and defines:

```lean
VerifiedOn
VerifiedPrefix
UniformFrom
SuccessorStep
```

The negative guardrails are:

```lean
verifiedOn_not_force_uniform
verifiedOn_Icc_iff_verifiedPrefix
verifiedPrefix_not_force_uniform
two_rung_floor_evidence_not_uniform
two_rung_floor_interval_evidence_not_uniform
not_uniformFrom_iff_exists_failure
not_successorStep_iff_exists_next_failure
```

The theorem `two_rung_floor_evidence_not_uniform` states that verifying rungs `a = 4, 5` cannot,
by logic alone, imply the uniform statement for all `a >= 4`.  The countermodel is the prefix model:

```text
R(a) := a <= 5.
```

It agrees on the checked rungs and fails at `a = 6`.

The file also records the positive replacement:

```lean
uniformFrom_of_base_and_successor_step
uniformFrom_of_verifiedPrefix_and_successor_step
uniformFrom_of_base_and_successorStep
uniformFrom_of_verifiedPrefix_and_successorStep
uniformFrom_of_verifiedOn_Icc_and_successorStep
```

These prove that a base verified rung plus a successor theorem

```text
R(a) -> R(a + 1)
```

does give uniformity.

The missing successor theorem is also scanner-facing:

```text
not SuccessorStep start R
  iff exists a >= start, R(a) and not R(a + 1).
```

With a verified prefix already in hand, failed uniformity now returns that same adjacent-rung
witness directly:

```lean
not_successorStep_of_verifiedPrefix_of_not_uniformFrom
not_successorStep_of_verifiedOn_Icc_of_not_uniformFrom
exists_next_failure_of_verifiedPrefix_of_not_uniformFrom
exists_next_failure_of_verifiedOn_Icc_of_not_uniformFrom
exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom
exists_next_failure_at_or_after_cutoff_of_verifiedOn_Icc_of_not_uniformFrom
```

For the floor lane, this is the refutable form of the proposed tower/renormalization law: either
prove the successor step for the actual floor-localization predicate, or find an adjacent rung
where the least-prime rule stops propagating.

The cutoff-refined forms say more: if every rung through `cutoff` has already been verified, then
the adjacent failure can be placed at some `a >= cutoff`.  A scanner extending a verified prefix
therefore never has to re-audit earlier rungs to explain a failed uniform theorem.

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorFiniteRungUniformityBarrier.lean
```

passed.

## Critical Consequence

The n=16 and n=32 floor scans are real evidence, but their proof type is finite:

```text
VerifiedPrefix 4 5 R
```

The closure contract consumes:

```text
UniformFrom 4 R
```

The new Lean file proves there is no inference from the former to the latter without extra
structure.  This matters because the off-BGK floor route currently rests on exactly that promotion:
the verified least-prime pattern must become a theorem for every dyadic rung.

## What New Math Would Look Like

The next useful theorem is not another finite scan and not another Linnik wrapper.  It is a
successor or renormalization theorem for the actual floor predicate:

```text
FloorLocalizationRung(a) -> FloorLocalizationRung(a + 1)
```

or a stronger direct all-rungs theorem.

For the concrete adjacent-profile floor object, such a theorem would need to compare the rank/minor
conditions for `mu_(2^a)` and `mu_(2^(a+1))`, while preserving the exact least-prime exceptional
mechanism.  That is a new structural statement about the cyclotomic resultant family; it is not
supplied by the facts that `17` and `97` match the pattern.

Even if that successor theorem is proved, the floor route still remains necessary-not-sufficient:
`_FloorClosureContract.lean` shows that floor-goodness must still be upgraded through
`FloorGoodFamilyBudget` and `FamilyDominates` before it reaches `WorstCaseIncidenceBounded`.

## Verdict

The least-prime floor program is now split into three explicit obligations:

```text
finite evidence:       a = 4, 5 verified
uniform localization:  missing successor/all-rungs theorem
prize conversion:      missing family budget + domination theorem
```

This pass banks the first-to-second barrier.  It prevents the n=16/n=32 evidence from being
accidentally treated as a uniform proof, and it names the exact kind of new math needed to promote
the evidence.
