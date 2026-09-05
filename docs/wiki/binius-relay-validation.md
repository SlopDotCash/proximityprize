# Binius relay validation

The Relay module uses the canonical challenge oracle interface and derives the
finite and inhabited instances for its empty challenge index. Strict completeness
transports the full prefix of folding challenges using the explicit old-index
bound. The verifier support calculation uses `OptionT.mem_support_mk` with
`erw` because its support instance needs definitional unfolding.

The internal relay knowledge state uses `masterKStateCore`, matching the public
input and output relations. The previous `masterKStateProp` additionally required
local sumcheck checks not present in those relations. The public relation
definitions and theorem statements are unchanged. The existing bad-event branch
and its documented interior-round vacuity are unchanged; this compatibility
repair does not establish a stronger security claim or discharge a research
residual.

A direct Lean check of the repaired Relay file passed on 2026-09-05 using the
built prerequisites in the adapter-validation checkout. This is focused evidence:
whole-consumer and full-repository validation are separate requirements. Commit
step validation is described below and must not be inferred from Relay.

The two `iterated_fold` index-congruence lemmas also omit the unused `β 0 = 1`
instance. Their proofs only substitute equal indices and close by reflexivity.
The commit folding and completeness helpers omit the same instance. This
generalization removes an unnecessary dependency; it adds no assumptions to
Commit's public completeness statement. The complete candidate Prelude passed
a direct Lean check. A complete ReductionLogic source check with the generalized
lemmas inlined also passed; rebuilding the canonical dependency chain remains
part of full validation.

The Commit repair uses the same canonical empty-challenge instances and support
conversion, preserves the first oracle through `getFirstOracle_snoc_oracle`, and
restricts challenges with `Fin.tail`. Its internal knowledge state likewise
matches `masterKStateCore`. The pre-commit bad branch uses the existing
`badEventExistsProp_of_lt`: at the old oracle index the last block has not
completed, so the existing guard makes the branch true. This explicitly retains
the existing vacuity and proves no probability bound or stronger security claim.

A complete Commit source check with the generalized congruence and completeness
helpers inlined passed Lean. The canonical dependency rebuild, all consumers,
and hosted checks remain separate validation gates.
