# Issue #464: semiprimitive Gauss-period shortcut is incompatible with split prime fields

Date: 2026-06-25.

Status: negative structural progress, not a prize proof.

## Inputs Checked

- Live issue #464, whose prize regime fixes a dyadic subgroup `mu_n < F_p^*` with `p = 1 mod n`.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`, which already marks the semiprimitive shortcut as
  arithmetically dead at the prize point.
- `docs/kb/proximity-paley-gauss-period-litsweep-2026-06-13.md`, where semiprimitive generalized
  Paley results are catalogued as a classical closed-form mechanism outside the prize regime.

## Claim Tested

One classical way to get explicit Gauss-period spectra is the semiprimitive case. In the usual
notation, the mechanism requires an exponent `t` with

```text
n | p^t + 1
```

equivalently `p^t = -1 mod n`. This is attractive because semiprimitive generalized Paley graphs
often have closed spectra or strongly regular behavior, so it looks like a possible escape from the
thin-subgroup BGK/Paley wall.

The #464 prize prime-field regime has the opposite arithmetic shape:

```text
n | p - 1
```

because the smooth evaluation domain is a dyadic subgroup `mu_n` of `F_p^*`.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SemiprimitiveSplitPrimeFieldGate.lean
```

The file proves the elementary obstruction:

```text
p = 1 mod n  ->  p^t = 1 mod n  ->  p^t + 1 = 2 mod n.
```

For `n > 2`, this rules out `n | p^t + 1` at every exponent. The bundled dyadic version is:

```lean
dyadic_not_semiprimitiveDivisibility_of_split :
  2 <= a ->
  p = 1 [MOD 2 ^ a] ->
  not (SemiprimitiveDivisibility p (2 ^ a))
```

So the prime-field split condition used by the prize and the semiprimitive divisibility condition
are mutually incompatible for every nontrivial dyadic subgroup.

## Consequence for #464

This closes a tempting but false proof architecture:

1. identify the prize period as a generalized Paley eigenvalue;
2. import a semiprimitive closed-form spectrum;
3. read off a Ramanujan or near-Ramanujan bound;
4. conclude the delta-star floor.

Step 2 cannot apply. Semiprimitive formulas live on a different congruence class of primes or on
extension-field arithmetic where Frobenius has order hitting `-1` modulo the subgroup order. In the
prime-field prize setting Frobenius is trivial on the subgroup exponents because `p = 1 mod n`.

This is stronger than a heuristic regime mismatch. It is the exact modular contradiction.

## Relation to existing literature notes

This Lean gate sharpens the older verdict in:

- `docs/kb/proximity-paley-gauss-period-litsweep-2026-06-13.md`.
- `docs/kb/deltastar-Bmun-IS-generalized-Paley-spectral-gap-2026-06-13.md`.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.

Those notes already identify semiprimitive generalized Paley results as the only classical
sub-`sqrt(q)` closed-form mechanism and mark them as arithmetically dead at the prize point. The new
gate records the minimal proof, independent of any asymptotic constants or literature
normalization.

## What New Math Would Look Like

The semiprimitive failure does not disprove the floor. It only removes one source of closed-form
spectral control. The remaining possible routes are still the same hard ones:

1. prove the dyadic thin-subgroup BGK/Paley character-sum estimate directly;
2. prove a worst-stack incidence theorem without going through semiprimitive periods;
3. prove sparse dominance/classification for the action-orbit route;
4. close the off-BGK floor-localization theorem, while keeping it scoped as obstruction removal.

No theorem here asserts `mcaDeltaStar`, `mcaConjecture`, or the floor. It prevents a wrong imported
Gauss-period special case from being mistaken for the prize regime.
