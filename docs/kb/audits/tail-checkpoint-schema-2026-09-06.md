# Tail checkpoint schema and consistency

The historical producer `scripts/probes/probe_466_rogers_siegel_tail_n32_resume.py` at `a9ae35f6f` writes the eight columns p, m, M, normalized M, Gumbel-normalized M, v2(p-1), generalized-Fermat level and least prime factor of m. The current CSV contains 2103 distinct-prime rows. Its SHA256 is `1b4ea5eaf810200a09db2106c472b8fdc1ad2fa0ea4290483da2f3393c563248`.

Every row passes trial-division primality, the stated prime window, 32*m=p-1, two-adic valuation and least-prime-factor checks. Exact integer binary searches also verify the generalized-Fermat level in every row. Both floating-point normalizations reproduce from the stored M and the historical formulas. These checks establish schema and internal consistency; they do not reproduce the coset maxima M, or establish the completeness of the historical ensemble. The checkpoint remains retained pending that review, with no completion-count increment.
