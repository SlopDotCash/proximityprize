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
step repairs are still pending and must not be inferred complete from Relay.
