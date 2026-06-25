# Delta-star #464: why the off-BGK floor route is necessary, not sufficient

Date: 2026-06-25.

## Summary

This is a critique of the strongest surviving non-BGK story in the dossier: bad-prime
localization plus least-prime-in-AP. The route remains useful, but it does not prove the prize
floor. It removes one explicit binder-family obstruction. The delta-star lower pin needs a
worst-case incidence bound over every word stack / far direction.

The new guardrail is formalized in:

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorNecessaryNotSufficient.lean`

It proves the abstract quantifier fact:

- `forall directions, count(direction) <= B` implies `count(binder) <= B`.
- `count(binder) <= B` does not imply `forall directions, count(direction) <= B`.
- A lower bound on a supremum from one summand cannot upper-bound the supremum.

This is deliberately small mathematics, but it catches the exact proof-orientation error in the
optimistic bad-prime story.

## Evidence read in this pass

- GitHub issue #464 and the in-tree canonical dossier `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.
- The local addenda in dossier sections 14-16, especially the n=32 floor resolution and the later
  correction that the floor route is necessary-not-sufficient.
- The ProximityGap agent guide and workbench.
- The relevant Frontier files:
  - `_AssaultV2_FloorLocalizationN32.lean`
  - `_FloorLinnikRungInstances.lean`
  - `_FloorLinnikThornerZamanArrow.lean`
  - `_FloorLinnikTZClosure.lean`
  - `_BchksF4_GoodPrimeLinnik.lean`
  - `_AssaultV2_FloorResultantHeight.lean`
  - `SpurBadPrimeChebotarev.lean`
- The local PDF library has 327 PDFs under `~/papers/arklib`. The library already contains the
  Paley/BGK/ABF/KKH/Chai-Fan/Lam-Leung core, but did not contain Thorner-Zaman arXiv:2108.10878.
  I fetched it into `tmp/pdfs/` and extracted the text for this pass.

## Correction to the old essay

The old optimistic sentence was:

> If floor-bad equals the smallest prime congruent to 1 mod n, then least-prime-in-AP closes the
> off-BGK floor, genuinely off the BGK wall.

The corrected sentence is:

> If floor-bad equals the smallest prime congruent to 1 mod n, and if a sub-quartic dyadic
> least-prime-in-AP theorem is supplied, then one explicit binder-family obstruction is removed
> at prize primes. This is necessary evidence for the prize floor, not a proof of the worst-case
> MCA floor.

There are two distinct gaps.

First, the prime-supply gap is sharper than the earlier prose admitted. Plain Linnik/Xylouris gives
an exponent around 5.18, which is not enough for `< n^4`. GRH gives a sufficient exponent
`2 + epsilon`. Thorner-Zaman's powerful-modulus refinement is the right place to look, because
`2^a` is powerful, but the dossier has not confirmed an unconditional dyadic exponent `< 4`.
The extracted Thorner-Zaman PDF supports this cautious reading: Corollary 3.1 improves the PNT in
AP for powerful moduli, but it is not already an in-tree proof of the exact dyadic sub-quartic least
prime needed here.

Second, and more important, even a perfect floor-localization theorem has the wrong quantifier.
`epsMCA` is a supremum over stacks. The lower-bound theorem `epsMCA_ge_far_incidence` says that a
single supplied far-line family contributes to that supremum. A good-prime theorem for this family
can show that this one contribution is harmless. It cannot show that all other contributions are
harmless.

## The proof-orientation test

Before accepting any proposed floor proof, apply this test.

Let `I(u, delta)` be the bad-scalar count of a stack or far direction `u`.

The prize floor consumes:

```text
forall u, I(u, delta) <= q * epsilon*
```

The bad-prime floor lane supplies at best:

```text
I(u_binder, delta) <= q * epsilon*
```

The first implies the second. The second does not imply the first.

The only way to make the bad-prime lane sufficient is to add a domination theorem:

```text
forall u, I(u, delta) <= Phi(I(u_binder, delta))
```

for a budget-preserving `Phi`, or to prove that every worst-case direction degenerates to the
binder family. But that domination theorem is exactly the missing sparse-dominance / BGK-Paley
incidence wall in another language. Without it, the route is obstruction removal, not closure.

## New tool: the Supremum Polarity Lemma

The small Lean brick names the tool as a reusable guardrail:

```text
AllDirectionsBounded bad B := forall i, card (bad i) <= B
OneDirectionBounded bad i0 B := card (bad i0) <= B
```

It proves `AllDirectionsBounded -> OneDirectionBounded` and gives a two-direction counterexample
to the converse. It also gives a numerical counterexample showing that a lower bound on a global
quantity plus a budget bound on the lower-bound witness cannot upper-bound the global quantity.

This is not deep. It is useful because the false proof uses exactly this invalid converse.

## What still survives

The bad-prime localization lane still matters.

- It is a clean way to certify that the explicit KKH/binder obstruction is not active at prize
  primes.
- The n=16 and n=32 scans are meaningful evidence for a tight-fit mechanism at the smallest
  `1 mod n` prime.
- It may still be worth formalizing a GRH-conditional or dyadic-powerful-modulus hypothesis:
  `leastPrimeOneModTwoPow_lt_pow_four`.

But its payoff should be stated as:

```text
binder_family_good_at_prize_primes
```

not:

```text
WorstCaseIncidenceBounded
```

## Next attack surface

The only route that could turn this lane into a prize proof is a direction-uniform theorem:

1. Classify all monomial directions that can maximize far-line incidence in the window.
2. Prove every maximizer is either binder-equivalent or controlled by the same fixed resultant
   mechanism.
3. If not, show the residual class is exactly the Paley/BGK period sup-norm, with no further
   hidden combinatorial escape.

The expected outcome is (3). That is still progress: it prevents future agents from spending
another loop on a necessary condition and calling it sufficient.

## Verdict

This loop refutes the previous strongest non-BGK closure reading. The floor localization theorem,
even if completed, is not a delta-star proof. It is a necessary obstruction check. The prize remains
at the worst-case incidence / thin-subgroup Paley wall.
