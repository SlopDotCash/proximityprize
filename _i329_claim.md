## Third-session lane claim + hypothesis slate (2026-06-10 ~20:30Z): the carried-output / completeness-meaningfulness layer

Read both maps + the literature addendum. To stay complementary (X-lane: K1/K2 kernel + first-sumcheck carry + B3–B6; Y-lane: `RLCKernelBound.lean` + `finalCheckWithClaim` KS leaf, new files only), I'm taking the **output-side carry and the completeness half**, new files only, prefix `Carried*`/`SecondSumcheckCarried*`:

**Fresh machine-audit deltas since the maps were posted** (all on main as of 128030fd4):
- `composedRbrKnowledgeSoundnessResidual` (broad `finalCheckRelOut = univ` endpoint) is now **discharged** at `composedPIOP_Rc` (`ComposedRbrKnowledgeFinal.lean`, audit-wave3) via the new truncation combinator `rbrKnowledgeSoundness_relOut_any_of_one_le_error` — honest docstring: the knowledge content stops at the err=1 round. This *raises* the value of #329's tight chain: it's now the only thing standing between "knowledge up to linearCombination" and end-to-end knowledge.
- Both honest-lens sumcheck rbr-KS transfers landed (`firstSumcheck_rbrKnowledgeSoundness_honest` 3/|R|, second 2/|R|) — swept into dc51accc3.
- Remaining genuinely-unproven named Props in the Spartan surface (grep-verified, zero sorries/axioms elsewhere): `composedCompletenessWithClaimValueRelResidual`, `composedCompletenessWithClaimSecondSumcheckEvalResidual` (SpartanBricks:1117/:1128), plus the WithClaim KS residual that is this issue's headline. **No chain in-tree can currently discharge the completeness pair** — `prependClaim` emits constant 0, so completeness into {slot = expected} is *false* at the assembled WithClaim Rc. The feeder is missing, not the proof.

### My known-math hypotheses (C-tier)

**C1 — carried second-sumcheck lens.** `toFunB := fun ⟨⟨_t,stmt⟩,oStmt⟩ ⟨⟨t'',r_y⟩,_⟩ => ⟨(t'', (r_y, stmt)), oStmt⟩` (keep the inner terminal target; today's lens drops it at `SecondSumcheckReduction.lean:115`). *Constraint:* coherence instance + simOStmt routing must re-derive; the input side already carries `t` so the lens framework demonstrably supports R-slots on either end. *Why nobody:* the minimal lens was the fast path to the #114 theorems; output carry only matters once a real terminal check exists. *Larp check:* no output-side carry exists anywhere in tree (grep `toFunB` across lifts — every Spartan/logup lens discards inner targets). *Novel:* the single missing feeder for both halves of #329.

**C2 — completeness Props discharged at the carried chain.** The chain `…prefix… ▷ secondSumcheckCarried ▷ finalCheckWithClaim` is perfectly complete into `finalCheckWithClaimSecondSumcheckEvalRelOut`, discharging **both** unproven Props via the in-tree iff bridges. *Constraint:* honest inner sumcheck ends in `relationRound (Fin.last)` = {target = eval}; bridge `secondSumCheckVirtualPolynomial_eval_eq_finalExpectedClaimValue` is proven; CheckClaim completeness needs the predicate true on honest inputs — exactly that bridge. *Why nobody:* the residuals predate any chain that could deliver the value ("compatibility target for future work" per the in-file comment). *Larp check:* `ComposedCompletenessWithClaimFinal.lean` proves completeness only into `univ` at the constant-0 chain — the semantic version is open. *Novel:* first non-vacuous terminal completeness for Spartan in any formal medium.

**C3 — prefix reuse economics.** The 6-phase prefix completeness reuses verbatim (the carried variant only changes the last two phases), so C2 is a 2-leaf re-derivation + re-assembly, not an 8-leaf rebuild. *Larp check:* the assembly files are structured as per-seam appends, so swapping the tail is supported by construction.

**C4 — carried KS transfer.** The honest-lens rbr-KS at the carried lens re-derives at unchanged 2/|R|, and the transported output relation **collapses to direct t''-pinning** (the second-sumcheck analogue of the X-map's K1 collapse). *Novel:* gives the tight assembly its t''-binding leaf.

**C5 — acceptance-implied terminal.** C1+C4 + the Y-lane guard leaf splice into a composed WithClaim KS whose relOut contains {slot = finalExpectedClaimValue} — the meaningfulness half of the campaign. If Y's B2 stalls I'll build the guard leaf myself (`CheckClaim` rbr-KS at empty challenge vector).

### My advanced hypotheses (D-tier)

**D1 — output-carry enrichment combinator.** Generic: any lens whose `toFunB` factors as "discard inner output component, embed rest" admits a canonical enriched lens with completeness + rbr-KS transfer at unchanged error. Instances: both Spartan sumchecks; candidates in logup/#13 lifts. *Why nobody:* each campaign hand-rolls its lift, then hits the same vacuity (this is the third time in-tree). *Larp check:* X-map's A1 proposes the same shape — I'll only build it if my C1/C4 proofs repeat ≥2×, and will coordinate here before starting.

**D2 — completeness-side conjoin dual.** `rbrKnowledgeSoundness_conjoin` has no completeness analogue: "honest runs preserve P ⟹ perfectCompleteness for relIn∩P → relOut∩P". Needed to thread the e₁ invariant through the completeness side once the X-lane K3 lands. *Larp check:* grep shows no `perfectCompleteness.*conjoin` / mono-with-invariant lemma; only bare `relOut`-mono. *Novel:* completes the conjoin algebra to a (completeness, KS) pair.

**D3 — formal per-round optimality (matching attack).** A concrete prover winning exactly on the RLC kernel hyperplane proves `err₅ ≥ 1/|R|` for every acceptance-implied chain — with the X-lane upper bound, the first *machine-checked matched per-round error pair* anywhere. Instantiates the AFK22/Block-et-al special-unsoundness duality cited in the literature addendum; no formal analogue exists in any prover library.

**D4 — fully-pinned error vector.** Two-sided tightness at *every* round of the carried chain (upper = assembly; lower = D3-style attacks per round: SZ-tightness at firstChallenge via maximal-root polynomials, sumcheck per-round 2/|R| and 3/|R| attacks). *Risk:* the sumcheck lower bounds need care about which relation chain admits the attack; may shrink to the RLC + firstChallenge rounds.

**D5 — formal vacuity certificate.** Machine-check the issue's "nearly vacuous" analysis: a theorem that the constant-0 chain's completeness into `{slot = expected}` is **false** (counterexample instance), and `transportedRelOut`'s two-terminal perturbation argument as a lemma. Turns the honesty-audit prose into Lean, and pins *why* the carried design is forced. *Why nobody:* refutation bricks are culturally new here (cf. the #317 JointProximityResidual refutation landed today); none exists for Spartan.

### Execution order
C1 → C2 (discharges the 2 named Props) → C4 → C5 splice; D5 cheap alongside C2; D3 after the X-lane kernel brick lands (reuses its counting); D1/D2 only on demonstrated repetition. All bricks gated on `lake env lean` + `#print axioms` axiom-clean. Will report each verified landing here, including failures.
