# Issue #314 Fiat-Shamir Grant Closeout Audit

This note records the June 10, 2026 closeout decision for the Fiat-Shamir specification grant:
the duplex-sponge executable/specification deliverable is in scope and complete enough for grant
closeout; the remaining strict DSFS residuals are post-grant CO25 Lemma 5.1 security hardening.

## Closeout Decision

**In scope for the grant.** ArkLib now has the concrete duplex-sponge Fiat-Shamir construction,
codec metadata, salted variants, canonical Fiat-Shamir transfer theorems, and DSFS completeness
run-collapse proofs needed for the specification grant:

- `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean`
  defines `duplexSpongeChallengeOracle`, `ProtocolSpec.Codec`, `SaltCodec`,
  `Reduction.duplexSpongeFiatShamir`, `Reduction.duplexSpongeFiatShamirSalted`, and the
  uniform-salt wrapper.
- `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunCollapse.lean`
  discharges `Reduction.duplexSpongeFiatShamir_runCollapseResidual` and
  `Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual`.
- `ArkLib/OracleReduction/FiatShamir/HVZKCanonicalClose.lean`,
  `ArkLib/OracleReduction/FiatShamir/StateRestorationTransport.lean`, and
  `ArkLib/OracleReduction/FiatShamir/BasicCompleteness.lean` close the canonical/basic FS
  completeness, SR soundness, SR knowledge soundness, and HVZK transfer surfaces used as the
  reference model.

**Post-grant security hardening.** The strict DSFS residuals below should remain explicit
assumptions until the full Chiesa--Orru [CO25] Section 5 hybrid proof is mechanized. They are not
raw `sorry` holes and should not block the grant's duplex-sponge specification closeout.

| Residual | Closeout classification | What it represents |
|---|---|---|
| `DuplexSpongeFS.KeyLemmaResidual` | Post-grant | The legacy per-prover key lemma statement over the current `SPMF` game surface. It is intentionally consumed by `duplexSpongeToFSGameStatDist`. |
| `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual` | Post-grant | CO25 Lemma 5.12 honest bad-event implication: off `E`, no backtrack chain step is inverse-anchored. |
| `Lemma5_14HonestResidual` | Post-grant | CO25 Lemma 5.14 honest bad-event implication: off `E`, there is at most one maximal backtrack sequence. |
| `Lemma5_16HonestFalseAsStated` | Post-grant | CO25 Lemma 5.16 honest bad-event implication: off `E`, all relevant chain queries are time-ordered. |
| `SimulatedProverChallengeBudgetResidual` | Post-grant | Lemma 5.1 witness-prover challenge-query budget for the simulated FS prover. |
| `SimulatedProverSharedBudgetResidual` | Post-grant | Lemma 5.1 witness-prover shared-oracle budget for the simulated FS prover. |
| `KeyLemmaEagerResidual` | Post-grant | The repaired eager-oracle, coin-equipped statement of the full CO25 Lemma 5.1 proof. |
| `D2sQueryStepGSpecBudgetResidual` | Post-grant | Per-step `gSpec` budget for the Section 5.4 dispatcher branch tree. |
| `D2fOuterImplSharedBudgetResidual` | Post-grant | Shared-query forwarding budget for the composed outer implementation. |

## Rationale

The grant title is a specification target: "Fiat-Shamir specification based on duplex sponges."
That target is met by the executable DSFS transform, protocol codec layer, salted construction,
and machine-checked completeness/run-collapse behavior. The remaining residuals are narrower and
deeper than a specification closeout: they encode the statistical-distance proof of CO25 Lemma 5.1
and supporting hybrid-game budget/bad-event lemmas.

`KeyLemmaFoundations.lean` already makes this distinction in code. It proves the reusable
foundational bricks such as the four-step TV triangle chain, the paper-exponent `etaStar` numeric
assembly, generic `IsQueryBoundP` lifts, abort elimination, memo determinism, log-projection
homomorphisms, and codec-bridge budgets. The named residuals are the remaining research-core
obligations, not concealed theorem claims.

One important fidelity note remains for future work: the current legacy `KeyLemmaResidual` uses
the older `KeyLemma.etaStar` denominator exponent `C+1`, while the paper-exponent eager surface in
`KeyLemmaFoundations.etaStarPaper` uses exponent `C`. The eager residual is therefore the better
post-grant target for completing the CO25 security proof.

## Documentation Updates

- `website/blueprint/src/oracle_reductions/fiat_shamir.tex` now describes both canonical FS and the
  duplex-sponge construction, including `duplexSpongeChallengeOracle`, `ProtocolSpec.Codec`,
  salted DSFS, run-collapse completeness, and the residualized key-lemma status.
- `website/blueprint/src/references.bib` now includes `CO25`.
- `docs/kb/papers/CO25.md` and `docs/kb/sources/CO25/metadata.yml` provide the local paper stub
  required by the KB workflow.

## Verification Commands

Recommended focused checks after touching this area:

```bash
lake env lean ArkLib/OracleReduction/FiatShamir/HVZKCanonicalClose.lean
lake env lean ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Soundness.lean
lake env lean ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunCollapse.lean
lake env lean ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/KeyLemmaFoundations.lean
python3 scripts/sorry_census.py --fail-on-holes
python3 scripts/residual_census.py --out /tmp/arklib-residual-census.json
./scripts/validate.sh
```

If only the blueprint text changes, `./scripts/validate.sh --docs` is the convenient add-on check.
