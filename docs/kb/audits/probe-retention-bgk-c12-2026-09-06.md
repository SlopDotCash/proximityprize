# BGK C12 alignment archive

Retain `scripts/probes/_out_bgk_c12_alignment.txt`. Running the complete producer exited 0 and reproduced the archive after newline normalization. All 19 cells and both depths r=5,6 passed the producer's integer mass, orbit and direct/factorized collision checks. Cells with p <= 257 additionally reconstruct the full difference row and check its orbit invariance. Independent trial division verified every listed prime.

An independent enumeration at n=8, p=17 constructs subset sums directly from combinations rather than dynamic programming, then counts the equality sum(S)-sum(T)=2y-x over subgroup pairs. Its C12 values match the producer at both depths; the JSON records these values and full output.

The computations use integer histograms and Fraction comparisons, with chunked dot-product overflow guards. Decimals only display those fractions. Negative alignment or failed proposed gate values are finite observations; these cells do not establish production inequalities, and the signed rho-squared column is explicitly signed rather than an ordinary nonnegative square.

The archive belongs to the original unreferenced baseline; its source was already referenced. The corrected aggregate advances to 65 of 92 reviewed, with 27 remaining. This does not complete issue #2 or the Delta Star theorem.
