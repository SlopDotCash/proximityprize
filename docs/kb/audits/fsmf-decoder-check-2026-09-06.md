# FSMF decoder regression

The exhaustive regression checks all 625 received words on the four nonzero elements of F5. For each word, it directly enumerates all 25 degree-below-two codewords and compares the entire list with agreement at least three against the GS/Roth-Ruckenstein decoder. Every list agrees exactly. This tests candidate completeness and filtering, not just the best score or a sampled witness.

The `y_roots` docstring previously claimed every root modulo X^k is returned. Stripping X factors strengthens such a truncated congruence: for example, Q=X^k vanishes modulo X^k for every substitution, but stripping its X factors gives 1 and no branches. Exact polynomial roots are preserved by stripping, which is the property required by the list-decoding argument. The corrected docstring states that guarantee. The algorithm is unchanged.

This finite regression does not certify all larger parameter sets. The m=10 full census remains separately pending; retention remains 64 of 92 reviewed.
