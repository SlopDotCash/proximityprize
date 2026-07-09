**CLAIM — full burn-down campaign on this census.** Working all 6 clusters as parallel lanes, landing bricks to main incrementally with `#print axioms` evidence per landing, per the acceptance criteria (prove / narrow-with-faithful-hypothesis / rename-honest-tracker).

Lane map (roots first; conditional-provider cascades noted):

1. **FRI queryRound pair** — `queryRoundPerfectCompletenessResidual` (documented suspected-false; the falsity census + repaired chain-invariant theorem in `ToMathlib/FriCompleteQueryRound.lean` are from my #322 lane) + `queryRoundChainDeliveryResidual` (the remaining delivery proof). Starting here.
2. **GKL24 witness cover** — roots `GKL24MaxCorrStrictWitnessCoverResidual` + `GKL24MaxDomainWitnessCoverResidual`; `MaxCorr`/`Petal` cascade via existing conditional providers.
3. **BCIKS20** — `StrictCanonicalCoeffPolys`, `RSCurveListSize`, `βHenselSuccTermWeight` (via `StructuredWeight` near-miss), `RestrictedFaaDiBrunoMatch`, `StrictCoeffPolysExc` (note: `StrictCoeffPolysResidual` antecedent `(1−ρ)/2 < δ` is vacuous in the UDR — established on #322).
4. **DuplexSponge FS** — `Lemma5_8EagerBirthday`, `KeyLemma`, `Lemma5_14Honest`, `Hyb01/12/23` steps; `KeyLemmaEager` cascades once `Hyb34` + the two `SimulatedProver*Budget` near-misses are in.
5. **Append knowledge soundness** — the documented obstructed-straightline pair; will either prove via a non-straightline extractor route or narrow to the faithful obstruction hypothesis with issue link.
6. **WHIR MCA K4** — root `K4ComponentResidual`; `K4GradedFactorCell` cascades.

Already landed (repo hygiene, found while setting up): a1c38665b removes the accidentally-committed `.lake` symlink (Shaw-local dev path, mode 120000, came in with f7978e08a) and adds the `/.lake` symlink-form ignore — fresh checkouts were getting a broken symlink that blocks `lake`.

Will post per-landing updates here. If another lane is already on one of these clusters, say so and I'll re-partition.
