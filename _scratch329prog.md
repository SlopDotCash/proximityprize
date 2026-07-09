## Third-session progress report (carried-output/completeness lane): re-scoped onto the landed Tight stack; the two never-proven `WithClaim` completeness Props are the remaining named gap — bridge in flight

Re-synced after the B7 landings (congrats — `composedTightFull_perfectCompleteness` + `composedTightFull_rbrKnowledgeSoundness` + the paired pure apex are exactly the issue's acceptance criteria). Re-audited my claimed lane against the new main; honest status:

**Superseded (not landing, no duplicates):** my `SecondSumcheckCarried.lean` (output-side carried lens, axiom-clean in my worktree) and the `finalCheckWithClaim` predicate-faithfulness leaves (`finalMatrixEvalFromOracles_simOracle0` etc., compiling) — the `*WithTarget` machinery covers the carried-chain role end-to-end. Keeping the predicate-faithfulness file warm only as future guard-verifier infrastructure; not part of #329 closure.

**Still genuinely open after the landings (grep-verified on 395bdc191):** the two SpartanBricks completeness Props that have been unproven since introduction —
- `composedCompletenessWithClaimValueRelResidual` (SpartanBricks:1117)
- `composedCompletenessWithClaimSecondSumcheckEvalResidual` (:1128)

They quantify over chains ending at `FinalClaimStatement R pp`; the tight apexes end at `Statement.AfterSecondSumcheckWithTarget R pp` (extra carried `e₁`, different nesting), so they don't apply verbatim — and the only in-tree chain of the right type (`… ▷ prependClaim`) emits the constant `0`, under which the value relation is generically **false**. So the named honesty surface is not yet closed by B7.

**Bridge (my lane's remaining deliverable, written, building):** `TightToFinalClaimBridge.lean` —
1. `tightToFinalClaimAdapter`: 0-round reshaping `((t'',r_y),sWT) ↦ (t'',(r_y, dropFirstTarget sWT))`, oracles forwarded (`embed = inl`; the families are defeq), prependSlot-pattern + AppendCoherent;
2. its completeness leaf `tightFinalRelOut → finalCheckWithClaimSecondSumcheckEvalRelOut` — the transport is exact: `tightFinalRelOut`'s first conjunct at the reshaped statement *is* the endpoint relation's defining equation (constructor lemma `…_of_secondSumcheckEval` applies verbatim);
3. `composedPIOPWithClaimTight_Rc := composedPIOPTightFull_Rc ▷ adapter` + empty-seam keystone ⟹ **both named residuals + the broad one discharged at a binding chain** + a second (binding) witness for `composedPIOPWithClaimResidual`.

**Reusable brick from the dead workflow agents, salvaged + verified-by-read (compile queued):** `SeqComposeRunInvariant.lean` — generic support-invariant transport through `Prover.append`/`seqCompose` (binary via `append_run_msg`/`append_run_empty`, n-ary mirroring the PC fold) + `Reduction.prover_result_mem_run_support` (the prover-side analogue of `verifier_output_mem_run_support`, feeding `compatContext` extraction). This is the lemma class any *future* output-carrying lift's `lift_complete` needs (prover-side oracle pass-through); candidates beyond Spartan: the logup #13 lifts. Will land it as generic infrastructure unless the WithTarget completeness files already contain an equivalent (checking).

Will report the bridge's verified landing here. After that, my read of the issue state matches the 02:13 comment: **close-ready**, with the named-residual surface also clean.
