# G101F monomial seeded-search archive review

Retain `scripts/probes/_out_g101f_s2.txt` as a reproducible bounded search log. The full s2 replay exited successfully after 1629 seconds and reproduced the archived output exactly after normalizing elapsed-second labels. All 12 cells completed, covering n=16,32,64 and the configured k=2,4 thresholds. Trial division independently verified the common field prime 65537. The engine's small brute-force self-test passed.

The source uses seed 4669101, pencil and structural initial offsets, random candidates, and bounded local mutations. It checks its agreement-farness filter before searching each configured monomial. Its table distinguishes the analytic pencil lower bound from the search lower bound; neither is an upper bound on all offsets or all directions. The n=64,k=2,a=9 search reproduces 240 bad scalars for its selected candidate.

Diagnostic witness supports are printed for only a sample of the bad scalars, and the complete offset vectors are not archived. The result therefore reproduces this algorithm's output, without supplying a portable independent certificate of every witness or a production theorem. The complete output and hashes are in the companion JSON.

The archive belongs to the original unreferenced inventory. Its completed review advances the corrected aggregate to 74 of 92, leaving 18 to review.
