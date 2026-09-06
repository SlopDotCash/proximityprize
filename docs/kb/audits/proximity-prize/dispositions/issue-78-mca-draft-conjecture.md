# Issue 78: MCA Draft Conjecture API Status

Status: resolved.

Decision:

- Keep `ProximityGap.GrandChallenges.mcaConjecture` public as a compatibility surface.
- Do not move the draft-source statement into a separate module in this pass; its docstring
  already carries the ignored-source caveat and existing proofs depend on the current module.
- Prefer the `ignoredSource`-named adapters at exported API boundaries:
  `nonempty_mcaLowerWitness_of_ignoredSource_mcaConjecture`,
  `exists_mcaLowerWitness_of_ignoredSource_mcaConjecture`,
  `mcaThresholdExists_of_ignoredSource_mcaConjecture`, and
  `mcaThreshold_spec_of_ignoredSource_mcaConjecture`.
- Treat the old adapter names as compatibility names. Their docstrings now state that the
  consumed conjecture is faithful to an ignored ABF26 `.tex` block rather than the rendered
  paper.

Regression search:

```sh
rg -n 'mcaConjecture|conj:mca-conjecture|ignore|draft|§4\.5' \
  Research/ProximityPrize/GrandChallenges.lean \
  ArkLib/Data/CodingTheory/ProximityGap/GrandChallengesLattice.lean \
  docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md \
  docs/kb/audits/proximity-prize
```

Expected result: exported uses of the draft conjecture either use an `ignoredSource` name or
carry an adjacent ignored-source/draft caveat in their docstring or audit note. This is a
status/API decision, not a rendered-paper theorem obligation.
