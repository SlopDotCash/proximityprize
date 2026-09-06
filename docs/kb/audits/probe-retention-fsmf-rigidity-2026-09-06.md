# Retention mapping: FSMF sampled zero counts — 2026-09-06

The complete 200,000-trial replay of
`scripts/probes/probe_fsmf_threeterm_vanishing_rigidity.py` passed and matched
`scripts/probes/_out_fsmf_rigidity.txt` byte for byte. Both artifacts are retained.
This adds two mappings to the previous 30 of the original 92 unreferenced
artifacts: 32 mapped, 60 remaining. The accompanying JSON records hashes and
results. The source header changed; its executable AST is unchanged.

The probe samples disjoint 14-subsets S,T of a 64-point domain in F_193,
independent uniform s,u in F_193, and uniform nonzero lambda. It counts zeros
of Z_S(X)(X-s) + lambda Z_T(X)(X-u) on that domain. Seed 31337 produces
counts 142662, 49113, 7502, 686, 36, 1 for zero counts 0 through 5 respectively.
The observed mean is 66324/200000 = 0.33162.

The former header incorrectly estimated the expected root count as
15 * 64/193, approximately five. For this distribution, condition on S,T
and fix a domain point x. If x belongs to S, the sum vanishes exactly when
u=x; if x belongs to T, exactly when s=x. Each has probability 1/193.
Outside both sets, both terms vanish with probability 1/193². If neither
vanishes, exactly one of the 192 nonzero lambda values cancels the sum,
contributing 192/193². Cases with exactly one zero term do not cancel.
Thus every domain point has zero probability 1/193, and linearity of
expectation gives 64/193. No independence between different domain points
is required. The revised header uses this calculation.

The observed maximum five is a sample statistic, not an upper bound for all
polynomial triples. The output's historical threshold 13 and fibre comparison
14 are retained as context and were not independently validated by this replay.
The probe does not construct the asserted joint cores, establish their
geometric realizability, prove general rigidity, or discharge issue #164.
